import V185TrunkScan20Chunk111

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_680417 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_680417 : Nat := 118140960795 + 680417 * 2 ^ 59
def prefixEnd_680417 : Nat := 4983230072969 + 3 ^ 40 * 680417 * 2
def baseEnd_680417 : Nat := 310560859102550754718511

theorem tailTrace_680417 : CollatzResearch.WordTrace tailWord_680417 prefixEnd_680417 310560859102550754718511 := by
  unfold tailWord_680417
  simp only [CollatzResearch.WordTrace]
  refine ⟨24816846775972889817079505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16544564517315259878053003 24816846775972889817079505)
  ·
    refine ⟨18612635081979667362809629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24816846775972889817079505 18612635081979667362809629)
    ·
      refine ⟨6979738155742375261053611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18612635081979667362809629 6979738155742375261053611)
      ·
        refine ⟨10469607233613562891580417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979738155742375261053611 10469607233613562891580417)
        ·
          refine ⟨7852205425210172168685313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10469607233613562891580417 7852205425210172168685313)
          ·
            refine ⟨5889154068907629126513985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7852205425210172168685313 5889154068907629126513985)
            ·
              refine ⟨4416865551680721844885489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889154068907629126513985 4416865551680721844885489)
              ·
                refine ⟨3312649163760541383664117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416865551680721844885489 3312649163760541383664117)
                ·
                  refine ⟨310560859102550754718511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312649163760541383664117 310560859102550754718511)
                  ·
                    rfl

theorem cell20_680417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_680417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680417 prefixEnd_680417 := by exact prefixLift 680417
  have htrace : WordTrace (prefixWord ++ tailWord_680417) baseStart_680417 baseEnd_680417 := by
    simpa [prefixWord, tailWord_680417, baseEnd_680417] using wordTrace_append hprefix tailTrace_680417
  have hstable : (prefixWord ++ tailWord_680417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680417).length < 2 ^ (prefixWord ++ tailWord_680417).sum := by decide
  have hdescent : baseEnd_680417 < baseStart_680417 := by decide
  rcases family_descends (prefixWord ++ tailWord_680417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680437 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_680437 : Nat := 118140960795 + 680437 * 2 ^ 59
def prefixEnd_680437 : Nat := 4983230072969 + 3 ^ 40 * 680437 * 2
def baseEnd_680437 : Nat := 310569987647519574051763

theorem tailTrace_680437 : CollatzResearch.WordTrace tailWord_680437 prefixEnd_680437 310569987647519574051763 := by
  unfold tailWord_680437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817576235900433232807565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545050823933622155205043 24817576235900433232807565)
  ·
    refine ⟨9306591088462662462302837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24817576235900433232807565 9306591088462662462302837)
    ·
      refine ⟨872492914543374605840891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9306591088462662462302837 872492914543374605840891)
      ·
        refine ⟨1308739371815061908761337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872492914543374605840891 1308739371815061908761337)
        ·
          refine ⟨981554528861296431571003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308739371815061908761337 981554528861296431571003)
          ·
            refine ⟨1472331793291944647356505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981554528861296431571003 1472331793291944647356505)
            ·
              refine ⟨1104248844968958485517379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472331793291944647356505 1104248844968958485517379)
              ·
                refine ⟨1656373267453437728276069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104248844968958485517379 1656373267453437728276069)
                ·
                  refine ⟨310569987647519574051763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656373267453437728276069 310569987647519574051763)
                  ·
                    rfl

theorem cell20_680437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_680437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680437 prefixEnd_680437 := by exact prefixLift 680437
  have htrace : WordTrace (prefixWord ++ tailWord_680437) baseStart_680437 baseEnd_680437 := by
    simpa [prefixWord, tailWord_680437, baseEnd_680437] using wordTrace_append hprefix tailTrace_680437
  have hstable : (prefixWord ++ tailWord_680437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680437).length < 2 ^ (prefixWord ++ tailWord_680437).sum := by decide
  have hdescent : baseEnd_680437 < baseStart_680437 := by decide
  rcases family_descends (prefixWord ++ tailWord_680437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680454 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_680454 : Nat := 118140960795 + 680454 * 2 ^ 59
def prefixEnd_680454 : Nat := 4983230072969 + 3 ^ 40 * 680454 * 2
def baseEnd_680454 : Nat := 310577746910743070485027

theorem tailTrace_680454 : CollatzResearch.WordTrace tailWord_680454 prefixEnd_680454 310577746910743070485027 := by
  unfold tailWord_680454
  simp only [CollatzResearch.WordTrace]
  refine ⟨775568633651213910505513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16545464184559230090784277 775568633651213910505513)
  ·
    refine ⟨581676475238410432879135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 775568633651213910505513 581676475238410432879135)
    ·
      refine ⟨872514712857615649318703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581676475238410432879135 872514712857615649318703)
      ·
        refine ⟨1308772069286423473978055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872514712857615649318703 1308772069286423473978055)
        ·
          refine ⟨1963158103929635210967083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308772069286423473978055 1963158103929635210967083)
          ·
            refine ⟨2944737155894452816450625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963158103929635210967083 2944737155894452816450625)
            ·
              refine ⟨2208552866920839612337969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944737155894452816450625 2208552866920839612337969)
              ·
                refine ⟨1656414650190629709253477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208552866920839612337969 1656414650190629709253477)
                ·
                  refine ⟨310577746910743070485027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656414650190629709253477 310577746910743070485027)
                  ·
                    rfl

theorem cell20_680454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_680454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680454 prefixEnd_680454 := by exact prefixLift 680454
  have htrace : WordTrace (prefixWord ++ tailWord_680454) baseStart_680454 baseEnd_680454 := by
    simpa [prefixWord, tailWord_680454, baseEnd_680454] using wordTrace_append hprefix tailTrace_680454
  have hstable : (prefixWord ++ tailWord_680454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680454).length < 2 ^ (prefixWord ++ tailWord_680454).sum := by decide
  have hdescent : baseEnd_680454 < baseStart_680454 := by decide
  rcases family_descends (prefixWord ++ tailWord_680454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680461 : List Nat := [1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_680461 : Nat := 118140960795 + 680461 * 2 ^ 59
def prefixEnd_680461 : Nat := 4983230072969 + 3 ^ 40 * 680461 * 2
def baseEnd_680461 : Nat := 103526980633827385750555

theorem tailTrace_680461 : CollatzResearch.WordTrace tailWord_680461 prefixEnd_680461 103526980633827385750555 := by
  unfold tailWord_680461
  simp only [CollatzResearch.WordTrace]
  refine ⟨24818451587813485331681237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545634391875656887787491 24818451587813485331681237)
  ·
    refine ⟨581682459089378562461279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24818451587813485331681237 581682459089378562461279)
    ·
      refine ⟨872523688634067843691919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581682459089378562461279 872523688634067843691919)
      ·
        refine ⟨1308785532951101765537879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872523688634067843691919 1308785532951101765537879)
        ·
          refine ⟨1963178299426652648306819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308785532951101765537879 1963178299426652648306819)
          ·
            refine ⟨2944767449139978972460229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963178299426652648306819 2944767449139978972460229)
            ·
              refine ⟨552143896713746057336293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2944767449139978972460229 552143896713746057336293)
              ·
                refine ⟨103526980633827385750555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552143896713746057336293 103526980633827385750555)
                ·
                  rfl

theorem cell20_680461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_680461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680461 prefixEnd_680461 := by exact prefixLift 680461
  have htrace : WordTrace (prefixWord ++ tailWord_680461) baseStart_680461 baseEnd_680461 := by
    simpa [prefixWord, tailWord_680461, baseEnd_680461] using wordTrace_append hprefix tailTrace_680461
  have hstable : (prefixWord ++ tailWord_680461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680461).length < 2 ^ (prefixWord ++ tailWord_680461).sum := by decide
  have hdescent : baseEnd_680461 < baseStart_680461 := by decide
  rcases family_descends (prefixWord ++ tailWord_680461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680471 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 2]
def baseStart_680471 : Nat := 118140960795 + 680471 * 2 ^ 59
def prefixEnd_680471 : Nat := 4983230072969 + 3 ^ 40 * 680471 * 2
def baseEnd_680471 : Nat := 310585506173966566918291

theorem tailTrace_680471 : CollatzResearch.WordTrace tailWord_680471 prefixEnd_680471 310585506173966566918291 := by
  unfold tailWord_680471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24818816317777257039545267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16545877545184838026363511 24818816317777257039545267)
  ·
    refine ⟨37228224476665885559317901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24818816317777257039545267 37228224476665885559317901)
    ·
      refine ⟨13960584178749707084744213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37228224476665885559317901 13960584178749707084744213)
      ·
        refine ⟨654402383378892519597385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13960584178749707084744213 654402383378892519597385)
        ·
          refine ⟨490801787534169389698039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654402383378892519597385 490801787534169389698039)
          ·
            refine ⟨736202681301254084547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490801787534169389698039 736202681301254084547059)
            ·
              refine ⟨1104304021951881126820589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736202681301254084547059 1104304021951881126820589)
              ·
                refine ⟨414114008231955422557721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104304021951881126820589 414114008231955422557721)
                ·
                  refine ⟨310585506173966566918291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414114008231955422557721 310585506173966566918291)
                  ·
                    rfl

theorem cell20_680471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 2].length) (baseStart_680471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680471 prefixEnd_680471 := by exact prefixLift 680471
  have htrace : WordTrace (prefixWord ++ tailWord_680471) baseStart_680471 baseEnd_680471 := by
    simpa [prefixWord, tailWord_680471, baseEnd_680471] using wordTrace_append hprefix tailTrace_680471
  have hstable : (prefixWord ++ tailWord_680471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680471).length < 2 ^ (prefixWord ++ tailWord_680471).sum := by decide
  have hdescent : baseEnd_680471 < baseStart_680471 := by decide
  rcases family_descends (prefixWord ++ tailWord_680471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680545 : List Nat := [1, 2, 3, 1, 1, 12]
def baseStart_680545 : Nat := 118140960795 + 680545 * 2 ^ 59
def prefixEnd_680545 : Nat := 4983230072969 + 3 ^ 40 * 680545 * 2
def baseEnd_680545 : Nat := 11504417844087081424123

theorem tailTrace_680545 : CollatzResearch.WordTrace tailWord_680545 prefixEnd_680545 11504417844087081424123 := by
  unfold tailWord_680545
  simp only [CollatzResearch.WordTrace]
  refine ⟨24821515319509167677739089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16547676879672778451826059 24821515319509167677739089)
  ·
    refine ⟨18616136489631875758304317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24821515319509167677739089 18616136489631875758304317)
    ·
      refine ⟨6981051183611953409364119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18616136489631875758304317 6981051183611953409364119)
      ·
        refine ⟨10471576775417930114046179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981051183611953409364119 10471576775417930114046179)
        ·
          refine ⟨15707365163126895171069269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10471576775417930114046179 15707365163126895171069269)
          ·
            refine ⟨11504417844087081424123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15707365163126895171069269 11504417844087081424123)
            ·
              rfl

theorem cell20_680545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_680545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680545 prefixEnd_680545 := by exact prefixLift 680545
  have htrace : WordTrace (prefixWord ++ tailWord_680545) baseStart_680545 baseEnd_680545 := by
    simpa [prefixWord, tailWord_680545, baseEnd_680545] using wordTrace_append hprefix tailTrace_680545
  have hstable : (prefixWord ++ tailWord_680545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680545).length < 2 ^ (prefixWord ++ tailWord_680545).sum := by decide
  have hdescent : baseEnd_680545 < baseStart_680545 := by decide
  rcases family_descends (prefixWord ++ tailWord_680545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680548 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_680548 : Nat := 118140960795 + 680548 * 2 ^ 59
def prefixEnd_680548 : Nat := 4983230072969 + 3 ^ 40 * 680548 * 2
def baseEnd_680548 : Nat := 310620651072096521351309

theorem tailTrace_680548 : CollatzResearch.WordTrace tailWord_680548 prefixEnd_680548 310620651072096521351309 := by
  unfold tailWord_680548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410812369249149595049149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16547749825665532793398865 12410812369249149595049149)
  ·
    refine ⟨4654054638468431098143431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12410812369249149595049149 4654054638468431098143431)
    ·
      refine ⟨6981081957702646647215147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654054638468431098143431 6981081957702646647215147)
      ·
        refine ⟨10471622936553969970822721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981081957702646647215147 10471622936553969970822721)
        ·
          refine ⟨7853717202415477478117041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10471622936553969970822721 7853717202415477478117041)
          ·
            refine ⟨5890287901811608108587781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853717202415477478117041 5890287901811608108587781)
            ·
              refine ⟨1104428981589676520360209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5890287901811608108587781 1104428981589676520360209)
              ·
                refine ⟨828321736192257390270157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104428981589676520360209 828321736192257390270157)
                ·
                  refine ⟨310620651072096521351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828321736192257390270157 310620651072096521351309)
                  ·
                    rfl

theorem cell20_680548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_680548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680548 prefixEnd_680548 := by exact prefixLift 680548
  have htrace : WordTrace (prefixWord ++ tailWord_680548) baseStart_680548 baseEnd_680548 := by
    simpa [prefixWord, tailWord_680548, baseEnd_680548] using wordTrace_append hprefix tailTrace_680548
  have hstable : (prefixWord ++ tailWord_680548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680548).length < 2 ^ (prefixWord ++ tailWord_680548).sum := by decide
  have hdescent : baseEnd_680548 < baseStart_680548 := by decide
  rcases family_descends (prefixWord ++ tailWord_680548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680576 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_680576 : Nat := 118140960795 + 680576 * 2 ^ 59
def prefixEnd_680576 : Nat := 4983230072969 + 3 ^ 40 * 680576 * 2
def baseEnd_680576 : Nat := 310633431035052868417861

theorem tailTrace_680576 : CollatzResearch.WordTrace tailWord_680576 prefixEnd_680576 310633431035052868417861 := by
  unfold tailWord_680576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411322991198429986058791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16548430654931239981411721 12411322991198429986058791)
  ·
    refine ⟨18616984486797644979088187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12411322991198429986058791 18616984486797644979088187)
    ·
      refine ⟨27925476730196467468632281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18616984486797644979088187 27925476730196467468632281)
      ·
        refine ⟨20944107547647350601474211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27925476730196467468632281 20944107547647350601474211)
        ·
          refine ⟨31416161321471025902211317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20944107547647350601474211 31416161321471025902211317)
          ·
            refine ⟨2945265123887908678332311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31416161321471025902211317 2945265123887908678332311)
            ·
              refine ⟨4417897685831863017498467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945265123887908678332311 4417897685831863017498467)
              ·
                refine ⟨6626846528747794526247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417897685831863017498467 6626846528747794526247701)
                ·
                  refine ⟨310633431035052868417861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6626846528747794526247701 310633431035052868417861)
                  ·
                    rfl

theorem cell20_680576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_680576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680576 prefixEnd_680576 := by exact prefixLift 680576
  have htrace : WordTrace (prefixWord ++ tailWord_680576) baseStart_680576 baseEnd_680576 := by
    simpa [prefixWord, tailWord_680576, baseEnd_680576] using wordTrace_append hprefix tailTrace_680576
  have hstable : (prefixWord ++ tailWord_680576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680576).length < 2 ^ (prefixWord ++ tailWord_680576).sum := by decide
  have hdescent : baseEnd_680576 < baseStart_680576 := by decide
  rcases family_descends (prefixWord ++ tailWord_680576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680630 : List Nat := [5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_680630 : Nat := 118140960795 + 680630 * 2 ^ 59
def prefixEnd_680630 : Nat := 4983230072969 + 3 ^ 40 * 680630 * 2
def baseEnd_680630 : Nat := 103552692702156226872547

theorem tailTrace_680630 : CollatzResearch.WordTrace tailWord_680630 prefixEnd_680630 103552692702156226872547 := by
  unfold tailWord_680630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551538470262576699661459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16549743682800818129722229 1551538470262576699661459)
  ·
    refine ⟨2327307705393865049492189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551538470262576699661459 2327307705393865049492189)
    ·
      refine ⟨872740389522699393559571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2327307705393865049492189 872740389522699393559571)
      ·
        refine ⟨1309110584284049090339357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872740389522699393559571 1309110584284049090339357)
        ·
          refine ⟨490916469106518408877259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1309110584284049090339357 490916469106518408877259)
          ·
            refine ⟨736374703659777613315889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490916469106518408877259 736374703659777613315889)
            ·
              refine ⟨552281027744833209986917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736374703659777613315889 552281027744833209986917)
              ·
                refine ⟨103552692702156226872547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552281027744833209986917 103552692702156226872547)
                ·
                  rfl

theorem cell20_680630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_680630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680630 prefixEnd_680630 := by exact prefixLift 680630
  have htrace : WordTrace (prefixWord ++ tailWord_680630) baseStart_680630 baseEnd_680630 := by
    simpa [prefixWord, tailWord_680630, baseEnd_680630] using wordTrace_append hprefix tailTrace_680630
  have hstable : (prefixWord ++ tailWord_680630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680630).length < 2 ^ (prefixWord ++ tailWord_680630).sum := by decide
  have hdescent : baseEnd_680630 < baseStart_680630 := by decide
  rcases family_descends (prefixWord ++ tailWord_680630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680638 : List Nat := [4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_680638 : Nat := 118140960795 + 680638 * 2 ^ 59
def prefixEnd_680638 : Nat := 4983230072969 + 3 ^ 40 * 680638 * 2
def baseEnd_680638 : Nat := 103553909841485402783647

theorem tailTrace_680638 : CollatzResearch.WordTrace tailWord_680638 prefixEnd_680638 103553909841485402783647 := by
  unfold tailWord_680638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3103113413521530570109321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16549938205448163040583045 3103113413521530570109321)
  ·
    refine ⟨2327335060141147927581991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3103113413521530570109321 2327335060141147927581991)
    ·
      refine ⟨3491002590211721891372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2327335060141147927581991 3491002590211721891372987)
      ·
        refine ⟨5236503885317582837059481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491002590211721891372987 5236503885317582837059481)
        ·
          refine ⟨3927377913988187127794611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5236503885317582837059481 3927377913988187127794611)
          ·
            refine ⟨5891066870982280691691917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927377913988187127794611 5891066870982280691691917)
            ·
              refine ⟨2209150076618355259384469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5891066870982280691691917 2209150076618355259384469)
              ·
                refine ⟨103553909841485402783647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2209150076618355259384469 103553909841485402783647)
                ·
                  rfl

theorem cell20_680638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_680638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680638 prefixEnd_680638 := by exact prefixLift 680638
  have htrace : WordTrace (prefixWord ++ tailWord_680638) baseStart_680638 baseEnd_680638 := by
    simpa [prefixWord, tailWord_680638, baseEnd_680638] using wordTrace_append hprefix tailTrace_680638
  have hstable : (prefixWord ++ tailWord_680638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680638).length < 2 ^ (prefixWord ++ tailWord_680638).sum := by decide
  have hdescent : baseEnd_680638 < baseStart_680638 := by decide
  rcases family_descends (prefixWord ++ tailWord_680638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680648 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_680648 : Nat := 118140960795 + 680648 * 2 ^ 59
def prefixEnd_680648 : Nat := 4983230072969 + 3 ^ 40 * 680648 * 2
def baseEnd_680648 : Nat := 310666293796940618017567

theorem tailTrace_680648 : CollatzResearch.WordTrace tailWord_680648 prefixEnd_680648 310666293796940618017567 := by
  unfold tailWord_680648
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412636019068008134369299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16550181358757344179159065 12412636019068008134369299)
  ·
    refine ⟨18618954028602012201553949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12412636019068008134369299 18618954028602012201553949)
    ·
      refine ⟨6982107760725754575582731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18618954028602012201553949 6982107760725754575582731)
      ·
        refine ⟨10473161641088631863374097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982107760725754575582731 10473161641088631863374097)
        ·
          refine ⟨7854871230816473897530573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10473161641088631863374097 7854871230816473897530573)
          ·
            refine ⟨2945576711556177711573965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7854871230816473897530573 2945576711556177711573965)
            ·
              refine ⟨1104591266833566641840237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2945576711556177711573965 1104591266833566641840237)
              ·
                refine ⟨414221725062587490690089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104591266833566641840237 414221725062587490690089)
                ·
                  refine ⟨310666293796940618017567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414221725062587490690089 310666293796940618017567)
                  ·
                    rfl

theorem cell20_680648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_680648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680648 prefixEnd_680648 := by exact prefixLift 680648
  have htrace : WordTrace (prefixWord ++ tailWord_680648) baseStart_680648 baseEnd_680648 := by
    simpa [prefixWord, tailWord_680648, baseEnd_680648] using wordTrace_append hprefix tailTrace_680648
  have hstable : (prefixWord ++ tailWord_680648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680648).length < 2 ^ (prefixWord ++ tailWord_680648).sum := by decide
  have hdescent : baseEnd_680648 < baseStart_680648 := by decide
  rcases family_descends (prefixWord ++ tailWord_680648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680676 : List Nat := [2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_680676 : Nat := 118140960795 + 680676 * 2 ^ 59
def prefixEnd_680676 : Nat := 4983230072969 + 3 ^ 40 * 680676 * 2
def baseEnd_680676 : Nat := 103559691253298988361373

theorem tailTrace_680676 : CollatzResearch.WordTrace tailWord_680676 prefixEnd_680676 103559691253298988361373 := by
  unfold tailWord_680676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413146641017288525378941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16550862188023051367171921 12413146641017288525378941)
  ·
    refine ⟨4654929990381483197017103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12413146641017288525378941 4654929990381483197017103)
    ·
      refine ⟨6982394985572224795525655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654929990381483197017103 6982394985572224795525655)
      ·
        refine ⟨10473592478358337193288483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982394985572224795525655 10473592478358337193288483)
        ·
          refine ⟨15710388717537505789932725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473592478358337193288483 15710388717537505789932725)
          ·
            refine ⟨1472848942269141167806193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15710388717537505789932725 1472848942269141167806193)
            ·
              refine ⟨1104636706701855875854645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1472848942269141167806193 1104636706701855875854645)
              ·
                refine ⟨103559691253298988361373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104636706701855875854645 103559691253298988361373)
                ·
                  rfl

theorem cell20_680676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_680676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680676 prefixEnd_680676 := by exact prefixLift 680676
  have htrace : WordTrace (prefixWord ++ tailWord_680676) baseStart_680676 baseEnd_680676 := by
    simpa [prefixWord, tailWord_680676, baseEnd_680676] using wordTrace_append hprefix tailTrace_680676
  have hstable : (prefixWord ++ tailWord_680676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680676).length < 2 ^ (prefixWord ++ tailWord_680676).sum := by decide
  have hdescent : baseEnd_680676 < baseStart_680676 := by decide
  rcases family_descends (prefixWord ++ tailWord_680676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680707 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 2]
def baseStart_680707 : Nat := 118140960795 + 680707 * 2 ^ 59
def prefixEnd_680707 : Nat := 4983230072969 + 3 ^ 40 * 680707 * 2
def baseEnd_680707 : Nat := 310693223004598635050659

theorem tailTrace_680707 : CollatzResearch.WordTrace tailWord_680707 prefixEnd_680707 310693223004598635050659 := by
  unfold tailWord_680707
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827423944922269345136375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16551615963281512896757583 24827423944922269345136375)
  ·
    refine ⟨37241135917383404017704563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24827423944922269345136375 37241135917383404017704563)
    ·
      refine ⟨55861703876075106026556845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37241135917383404017704563 55861703876075106026556845)
      ·
        refine ⟨20948138953528164759958817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55861703876075106026556845 20948138953528164759958817)
        ·
          refine ⟨15711104215146123569969113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20948138953528164759958817 15711104215146123569969113)
          ·
            refine ⟨11783328161359592677476835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15711104215146123569969113 11783328161359592677476835)
            ·
              refine ⟨17674992242039389016215253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783328161359592677476835 17674992242039389016215253)
              ·
                refine ⟨414257630672798180067545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17674992242039389016215253 414257630672798180067545)
                ·
                  refine ⟨310693223004598635050659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414257630672798180067545 310693223004598635050659)
                  ·
                    rfl

theorem cell20_680707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2].length) (baseStart_680707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680707 prefixEnd_680707 := by exact prefixLift 680707
  have htrace : WordTrace (prefixWord ++ tailWord_680707) baseStart_680707 baseEnd_680707 := by
    simpa [prefixWord, tailWord_680707, baseEnd_680707] using wordTrace_append hprefix tailTrace_680707
  have hstable : (prefixWord ++ tailWord_680707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680707).length < 2 ^ (prefixWord ++ tailWord_680707).sum := by decide
  have hdescent : baseEnd_680707 < baseStart_680707 := by decide
  rcases family_descends (prefixWord ++ tailWord_680707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680710 : List Nat := [6, 2, 2, 10]
def baseStart_680710 : Nat := 118140960795 + 680710 * 2 ^ 59
def prefixEnd_680710 : Nat := 4983230072969 + 3 ^ 40 * 680710 * 2
def baseEnd_680710 : Nat := 1278578569079604765229

theorem tailTrace_680710 : CollatzResearch.WordTrace tailWord_680710 prefixEnd_680710 1278578569079604765229 := by
  unfold tailWord_680710
  simp only [CollatzResearch.WordTrace]
  refine ⟨775860417622231276796737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16551688909274267238330389 775860417622231276796737)
  ·
    refine ⟨581895313216673457597553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 775860417622231276796737 581895313216673457597553)
    ·
      refine ⟨436421484912505093198165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581895313216673457597553 436421484912505093198165)
      ·
        refine ⟨1278578569079604765229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 436421484912505093198165 1278578569079604765229)
        ·
          rfl

theorem cell20_680710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 10].length) (baseStart_680710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680710 prefixEnd_680710 := by exact prefixLift 680710
  have htrace : WordTrace (prefixWord ++ tailWord_680710) baseStart_680710 baseEnd_680710 := by
    simpa [prefixWord, tailWord_680710, baseEnd_680710] using wordTrace_append hprefix tailTrace_680710
  have hstable : (prefixWord ++ tailWord_680710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680710).length < 2 ^ (prefixWord ++ tailWord_680710).sum := by decide
  have hdescent : baseEnd_680710 < baseStart_680710 := by decide
  rcases family_descends (prefixWord ++ tailWord_680710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680721 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_680721 : Nat := 118140960795 + 680721 * 2 ^ 59
def prefixEnd_680721 : Nat := 4983230072969 + 3 ^ 40 * 680721 * 2
def baseEnd_680721 : Nat := 310699612986076808583935

theorem tailTrace_680721 : CollatzResearch.WordTrace tailWord_680721 prefixEnd_680721 310699612986076808583935 := by
  unfold tailWord_680721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827934566871549736146017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16551956377914366490764011 24827934566871549736146017)
  ·
    refine ⟨18620950925153662302109513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24827934566871549736146017 18620950925153662302109513)
    ·
      refine ⟨13965713193865246726582135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18620950925153662302109513 13965713193865246726582135)
      ·
        refine ⟨20948569790797870089873203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13965713193865246726582135 20948569790797870089873203)
        ·
          refine ⟨31422854686196805134809805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20948569790797870089873203 31422854686196805134809805)
          ·
            refine ⟨11783570507323801925553677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31422854686196805134809805 11783570507323801925553677)
            ·
              refine ⟨4418838940246425722082629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11783570507323801925553677 4418838940246425722082629)
              ·
                refine ⟨828532301296204822890493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4418838940246425722082629 828532301296204822890493)
                ·
                  refine ⟨310699612986076808583935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828532301296204822890493 310699612986076808583935)
                  ·
                    rfl

theorem cell20_680721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_680721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680721 prefixEnd_680721 := by exact prefixLift 680721
  have htrace : WordTrace (prefixWord ++ tailWord_680721) baseStart_680721 baseEnd_680721 := by
    simpa [prefixWord, tailWord_680721, baseEnd_680721] using wordTrace_append hprefix tailTrace_680721
  have hstable : (prefixWord ++ tailWord_680721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680721).length < 2 ^ (prefixWord ++ tailWord_680721).sum := by decide
  have hdescent : baseEnd_680721 < baseStart_680721 := by decide
  rcases family_descends (prefixWord ++ tailWord_680721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680728 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_680728 : Nat := 118140960795 + 680728 * 2 ^ 59
def prefixEnd_680728 : Nat := 4983230072969 + 3 ^ 40 * 680728 * 2
def baseEnd_680728 : Nat := 310702807976815895350573

theorem tailTrace_680728 : CollatzResearch.WordTrace tailWord_680728 prefixEnd_680728 310702807976815895350573 := by
  unfold tailWord_680728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12414094938923094965825419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16552126585230793287767225 12414094938923094965825419)
  ·
    refine ⟨18621142408384642448738129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12414094938923094965825419 18621142408384642448738129)
    ·
      refine ⟨13965856806288481836553597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18621142408384642448738129 13965856806288481836553597)
      ·
        refine ⟨5237196302358180688707599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13965856806288481836553597 5237196302358180688707599)
        ·
          refine ⟨7855794453537271033061399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5237196302358180688707599 7855794453537271033061399)
          ·
            refine ⟨11783691680305906549592099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855794453537271033061399 11783691680305906549592099)
            ·
              refine ⟨17675537520458859824388149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783691680305906549592099 17675537520458859824388149)
              ·
                refine ⟨1657081642543018108536389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17675537520458859824388149 1657081642543018108536389)
                ·
                  refine ⟨310702807976815895350573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657081642543018108536389 310702807976815895350573)
                  ·
                    rfl

theorem cell20_680728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_680728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680728 prefixEnd_680728 := by exact prefixLift 680728
  have htrace : WordTrace (prefixWord ++ tailWord_680728) baseStart_680728 baseEnd_680728 := by
    simpa [prefixWord, tailWord_680728, baseEnd_680728] using wordTrace_append hprefix tailTrace_680728
  have hstable : (prefixWord ++ tailWord_680728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680728).length < 2 ^ (prefixWord ++ tailWord_680728).sum := by decide
  have hdescent : baseEnd_680728 < baseStart_680728 := by decide
  rcases family_descends (prefixWord ++ tailWord_680728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680738 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_680738 : Nat := 118140960795 + 680738 * 2 ^ 59
def prefixEnd_680738 : Nat := 4983230072969 + 3 ^ 40 * 680738 * 2
def baseEnd_680738 : Nat := 310707372249300305017199

theorem tailTrace_680738 : CollatzResearch.WordTrace tailWord_680738 prefixEnd_680738 310707372249300305017199 := by
  unfold tailWord_680738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207138651952490409878717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16552369738539974426343245 6207138651952490409878717)
  ·
    refine ⟨2327676994482183903704519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6207138651952490409878717 2327676994482183903704519)
    ·
      refine ⟨3491515491723275855556779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2327676994482183903704519 3491515491723275855556779)
      ·
        refine ⟨5237273237584913783335169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491515491723275855556779 5237273237584913783335169)
        ·
          refine ⟨3927954928188685337501377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5237273237584913783335169 3927954928188685337501377)
          ·
            refine ⟨2945966196141514003126033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3927954928188685337501377 2945966196141514003126033)
            ·
              refine ⟨2209474647106135502344525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945966196141514003126033 2209474647106135502344525)
              ·
                refine ⟨828552992664800813379197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209474647106135502344525 828552992664800813379197)
                ·
                  refine ⟨310707372249300305017199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828552992664800813379197 310707372249300305017199)
                  ·
                    rfl

theorem cell20_680738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_680738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680738 prefixEnd_680738 := by exact prefixLift 680738
  have htrace : WordTrace (prefixWord ++ tailWord_680738) baseStart_680738 baseEnd_680738 := by
    simpa [prefixWord, tailWord_680738, baseEnd_680738] using wordTrace_append hprefix tailTrace_680738
  have hstable : (prefixWord ++ tailWord_680738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680738).length < 2 ^ (prefixWord ++ tailWord_680738).sum := by decide
  have hdescent : baseEnd_680738 < baseStart_680738 := by decide
  rcases family_descends (prefixWord ++ tailWord_680738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680758 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_680758 : Nat := 118140960795 + 680758 * 2 ^ 59
def prefixEnd_680758 : Nat := 4983230072969 + 3 ^ 40 * 680758 * 2
def baseEnd_680758 : Nat := 310716500794269124350451

theorem tailTrace_680758 : CollatzResearch.WordTrace tailWord_680758 prefixEnd_680758 310716500794269124350451 := by
  unfold tailWord_680758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551830254233594065952683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16552856045158336703495285 1551830254233594065952683)
  ·
    refine ⟨2327745381350391098929025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551830254233594065952683 2327745381350391098929025)
    ·
      refine ⟨1745809036012793324196769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327745381350391098929025 1745809036012793324196769)
      ·
        refine ⟨1309356777009594993147577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745809036012793324196769 1309356777009594993147577)
        ·
          refine ⟨982017582757196244860683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309356777009594993147577 982017582757196244860683)
          ·
            refine ⟨1473026374135794367291025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982017582757196244860683 1473026374135794367291025)
            ·
              refine ⟨1104769780601845775468269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473026374135794367291025 1104769780601845775468269)
              ·
                refine ⟨414288667725692165800601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104769780601845775468269 414288667725692165800601)
                ·
                  refine ⟨310716500794269124350451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414288667725692165800601 310716500794269124350451)
                  ·
                    rfl

theorem cell20_680758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_680758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680758 prefixEnd_680758 := by exact prefixLift 680758
  have htrace : WordTrace (prefixWord ++ tailWord_680758) baseStart_680758 baseEnd_680758 := by
    simpa [prefixWord, tailWord_680758, baseEnd_680758] using wordTrace_append hprefix tailTrace_680758
  have hstable : (prefixWord ++ tailWord_680758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680758).length < 2 ^ (prefixWord ++ tailWord_680758).sum := by decide
  have hdescent : baseEnd_680758 < baseStart_680758 := by decide
  rcases family_descends (prefixWord ++ tailWord_680758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680769 : List Nat := [1, 2, 5, 3, 1, 1, 7]
def baseStart_680769 : Nat := 118140960795 + 680769 * 2 ^ 59
def prefixEnd_680769 : Nat := 4983230072969 + 3 ^ 40 * 680769 * 2
def baseEnd_680769 : Nat := 34524613499333552775971

theorem tailTrace_680769 : CollatzResearch.WordTrace tailWord_680769 prefixEnd_680769 34524613499333552775971 := by
  unfold tailWord_680769
  simp only [CollatzResearch.WordTrace]
  refine ⟨24829685270697653933893361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16553123513798435955928907 24829685270697653933893361)
  ·
    refine ⟨18622263953023240450420021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24829685270697653933893361 18622263953023240450420021)
    ·
      refine ⟨1745837245595928792226877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18622263953023240450420021 1745837245595928792226877)
      ·
        refine ⟨654688967098473297085079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1745837245595928792226877 654688967098473297085079)
        ·
          refine ⟨982033450647709945627619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654688967098473297085079 982033450647709945627619)
          ·
            refine ⟨1473050175971564918441429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982033450647709945627619 1473050175971564918441429)
            ·
              refine ⟨34524613499333552775971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1473050175971564918441429 34524613499333552775971)
              ·
                rfl

theorem cell20_680769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_680769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680769 prefixEnd_680769 := by exact prefixLift 680769
  have htrace : WordTrace (prefixWord ++ tailWord_680769) baseStart_680769 baseEnd_680769 := by
    simpa [prefixWord, tailWord_680769, baseEnd_680769] using wordTrace_append hprefix tailTrace_680769
  have hstable : (prefixWord ++ tailWord_680769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680769).length < 2 ^ (prefixWord ++ tailWord_680769).sum := by decide
  have hdescent : baseEnd_680769 < baseStart_680769 := by decide
  rcases family_descends (prefixWord ++ tailWord_680769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680807 : List Nat := [1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_680807 : Nat := 118140960795 + 680807 * 2 ^ 59
def prefixEnd_680807 : Nat := 4983230072969 + 3 ^ 40 * 680807 * 2
def baseEnd_680807 : Nat := 103579621909814243905639

theorem tailTrace_680807 : CollatzResearch.WordTrace tailWord_680807 prefixEnd_680807 103579621909814243905639 := by
  unfold tailWord_680807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831071244559986423776675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16554047496373324282517783 24831071244559986423776675)
  ·
    refine ⟨37246606866839979635665013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24831071244559986423776675 37246606866839979635665013)
    ·
      refine ⟨3491869393766248090843595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37246606866839979635665013 3491869393766248090843595)
      ·
        refine ⟨5237804090649372136265393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491869393766248090843595 5237804090649372136265393)
        ·
          refine ⟨3928353067987029102199045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5237804090649372136265393 3928353067987029102199045)
          ·
            refine ⟨736566200247567956662321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3928353067987029102199045 736566200247567956662321)
            ·
              refine ⟨552424650185675967496741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736566200247567956662321 552424650185675967496741)
              ·
                refine ⟨103579621909814243905639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 552424650185675967496741 103579621909814243905639)
                ·
                  rfl

theorem cell20_680807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_680807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680807 prefixEnd_680807 := by exact prefixLift 680807
  have htrace : WordTrace (prefixWord ++ tailWord_680807) baseStart_680807 baseEnd_680807 := by
    simpa [prefixWord, tailWord_680807, baseEnd_680807] using wordTrace_append hprefix tailTrace_680807
  have hstable : (prefixWord ++ tailWord_680807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680807).length < 2 ^ (prefixWord ++ tailWord_680807).sum := by decide
  have hdescent : baseEnd_680807 < baseStart_680807 := by decide
  rcases family_descends (prefixWord ++ tailWord_680807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680834 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_680834 : Nat := 118140960795 + 680834 * 2 ^ 59
def prefixEnd_680834 : Nat := 4983230072969 + 3 ^ 40 * 680834 * 2
def baseEnd_680834 : Nat := 310751189265150637816807

theorem tailTrace_680834 : CollatzResearch.WordTrace tailWord_680834 prefixEnd_680834 310751189265150637816807 := by
  unfold tailWord_680834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208014003865542508752389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16554704010308113356673037 6208014003865542508752389)
  ·
    refine ⟨1164002625724789220391073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6208014003865542508752389 1164002625724789220391073)
    ·
      refine ⟨873001969293591915293305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164002625724789220391073 873001969293591915293305)
      ·
        refine ⟨654751476970193936469979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873001969293591915293305 654751476970193936469979)
        ·
          refine ⟨982127215455290904704969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654751476970193936469979 982127215455290904704969)
          ·
            refine ⟨736595411591468178528727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982127215455290904704969 736595411591468178528727)
            ·
              refine ⟨1104893117387202267793091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736595411591468178528727 1104893117387202267793091)
              ·
                refine ⟨1657339676080803401689637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104893117387202267793091 1657339676080803401689637)
                ·
                  refine ⟨310751189265150637816807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657339676080803401689637 310751189265150637816807)
                  ·
                    rfl

theorem cell20_680834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_680834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680834 prefixEnd_680834 := by exact prefixLift 680834
  have htrace : WordTrace (prefixWord ++ tailWord_680834) baseStart_680834 baseEnd_680834 := by
    simpa [prefixWord, tailWord_680834, baseEnd_680834] using wordTrace_append hprefix tailTrace_680834
  have hstable : (prefixWord ++ tailWord_680834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680834).length < 2 ^ (prefixWord ++ tailWord_680834).sum := by decide
  have hdescent : baseEnd_680834 < baseStart_680834 := by decide
  rcases family_descends (prefixWord ++ tailWord_680834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680835 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_680835 : Nat := 118140960795 + 680835 * 2 ^ 59
def prefixEnd_680835 : Nat := 4983230072969 + 3 ^ 40 * 680835 * 2
def baseEnd_680835 : Nat := 310751645692399078783469

theorem tailTrace_680835 : CollatzResearch.WordTrace tailWord_680835 prefixEnd_680835 310751645692399078783469 := by
  unfold tailWord_680835
  simp only [CollatzResearch.WordTrace]
  refine ⟨24832092488458547205795959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16554728325639031470530639 24832092488458547205795959)
  ·
    refine ⟨37248138732687820808693939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24832092488458547205795959 37248138732687820808693939)
    ·
      refine ⟨55872208099031731213040909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37248138732687820808693939 55872208099031731213040909)
      ·
        refine ⟨20952078037136899204890341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55872208099031731213040909 20952078037136899204890341)
        ·
          refine ⟨3928514631963168600916939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20952078037136899204890341 3928514631963168600916939)
          ·
            refine ⟨5892771947944752901375409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928514631963168600916939 5892771947944752901375409)
            ·
              refine ⟨4419578960958564676031557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892771947944752901375409 4419578960958564676031557)
              ·
                refine ⟨828671055179730876755917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4419578960958564676031557 828671055179730876755917)
                ·
                  refine ⟨310751645692399078783469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828671055179730876755917 310751645692399078783469)
                  ·
                    rfl

theorem cell20_680835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_680835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680835 prefixEnd_680835 := by exact prefixLift 680835
  have htrace : WordTrace (prefixWord ++ tailWord_680835) baseStart_680835 baseEnd_680835 := by
    simpa [prefixWord, tailWord_680835, baseEnd_680835] using wordTrace_append hprefix tailTrace_680835
  have hstable : (prefixWord ++ tailWord_680835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680835).length < 2 ^ (prefixWord ++ tailWord_680835).sum := by decide
  have hdescent : baseEnd_680835 < baseStart_680835 := by decide
  rcases family_descends (prefixWord ++ tailWord_680835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680852 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_680852 : Nat := 118140960795 + 680852 * 2 ^ 59
def prefixEnd_680852 : Nat := 4983230072969 + 3 ^ 40 * 680852 * 2
def baseEnd_680852 : Nat := 310759404955622575216733

theorem tailTrace_680852 : CollatzResearch.WordTrace tailWord_680852 prefixEnd_680852 310759404955622575216733 := by
  unfold tailWord_680852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416356264698479554582405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16555141686264639406109873 12416356264698479554582405)
  ·
    refine ⟨2328066799630964916484201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12416356264698479554582405 2328066799630964916484201)
    ·
      refine ⟨1746050099723223687363151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328066799630964916484201 1746050099723223687363151)
      ·
        refine ⟨2619075149584835531044727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746050099723223687363151 2619075149584835531044727)
        ·
          refine ⟨3928612724377253296567091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619075149584835531044727 3928612724377253296567091)
          ·
            refine ⟨5892919086565879944850637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928612724377253296567091 5892919086565879944850637)
            ·
              refine ⟨2209844657462204979318989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5892919086565879944850637 2209844657462204979318989)
              ·
                refine ⟨828691746548326867244621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209844657462204979318989 828691746548326867244621)
                ·
                  refine ⟨310759404955622575216733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828691746548326867244621 310759404955622575216733)
                  ·
                    rfl

theorem cell20_680852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_680852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680852 prefixEnd_680852 := by exact prefixLift 680852
  have htrace : WordTrace (prefixWord ++ tailWord_680852) baseStart_680852 baseEnd_680852 := by
    simpa [prefixWord, tailWord_680852, baseEnd_680852] using wordTrace_append hprefix tailTrace_680852
  have hstable : (prefixWord ++ tailWord_680852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680852).length < 2 ^ (prefixWord ++ tailWord_680852).sum := by decide
  have hdescent : baseEnd_680852 < baseStart_680852 := by decide
  rcases family_descends (prefixWord ++ tailWord_680852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680866 : List Nat := [3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_680866 : Nat := 118140960795 + 680866 * 2 ^ 59
def prefixEnd_680866 : Nat := 4983230072969 + 3 ^ 40 * 680866 * 2
def baseEnd_680866 : Nat := 103588598312366916250003

theorem tailTrace_680866 : CollatzResearch.WordTrace tailWord_680866 prefixEnd_680866 103588598312366916250003 := by
  unfold tailWord_680866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208305787836559875043613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16555482100897493000116301 6208305787836559875043613)
  ·
    refine ⟨2328114670438709953141355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6208305787836559875043613 2328114670438709953141355)
    ·
      refine ⟨3492172005658064929712033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328114670438709953141355 3492172005658064929712033)
      ·
        refine ⟨2619129004243548697284025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492172005658064929712033 2619129004243548697284025)
        ·
          refine ⟨1964346753182661522963019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619129004243548697284025 1964346753182661522963019)
          ·
            refine ⟨2946520129773992284444529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964346753182661522963019 2946520129773992284444529)
            ·
              refine ⟨2209890097330494213333397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946520129773992284444529 2209890097330494213333397)
              ·
                refine ⟨103588598312366916250003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2209890097330494213333397 103588598312366916250003)
                ·
                  rfl

theorem cell20_680866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_680866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680866 prefixEnd_680866 := by exact prefixLift 680866
  have htrace : WordTrace (prefixWord ++ tailWord_680866) baseStart_680866 baseEnd_680866 := by
    simpa [prefixWord, tailWord_680866, baseEnd_680866] using wordTrace_append hprefix tailTrace_680866
  have hstable : (prefixWord ++ tailWord_680866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680866).length < 2 ^ (prefixWord ++ tailWord_680866).sum := by decide
  have hdescent : baseEnd_680866 < baseStart_680866 := by decide
  rcases family_descends (prefixWord ++ tailWord_680866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680900 : List Nat := [2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_680900 : Nat := 118140960795 + 680900 * 2 ^ 59
def prefixEnd_680900 : Nat := 4983230072969 + 3 ^ 40 * 680900 * 2
def baseEnd_680900 : Nat := 103593771154515913872179

theorem tailTrace_680900 : CollatzResearch.WordTrace tailWord_680900 prefixEnd_680900 103593771154515913872179 := by
  unfold tailWord_680900
  simp only [CollatzResearch.WordTrace]
  refine ⟨12417231616611531653456077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16556308822148708871274769 12417231616611531653456077)
  ·
    refine ⟨4656461856229324370046029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12417231616611531653456077 4656461856229324370046029)
    ·
      refine ⟨1746173196085996638767261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4656461856229324370046029 1746173196085996638767261)
      ·
        refine ⟨654814948532248739537723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1746173196085996638767261 654814948532248739537723)
        ·
          refine ⟨982222422798373109306585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654814948532248739537723 982222422798373109306585)
          ·
            refine ⟨736666817098779831979939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982222422798373109306585 736666817098779831979939)
            ·
              refine ⟨1105000225648169747969909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736666817098779831979939 1105000225648169747969909)
              ·
                refine ⟨103593771154515913872179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1105000225648169747969909 103593771154515913872179)
                ·
                  rfl

theorem cell20_680900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_680900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680900 prefixEnd_680900 := by exact prefixLift 680900
  have htrace : WordTrace (prefixWord ++ tailWord_680900) baseStart_680900 baseEnd_680900 := by
    simpa [prefixWord, tailWord_680900, baseEnd_680900] using wordTrace_append hprefix tailTrace_680900
  have hstable : (prefixWord ++ tailWord_680900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680900).length < 2 ^ (prefixWord ++ tailWord_680900).sum := by decide
  have hdescent : baseEnd_680900 < baseStart_680900 := by decide
  rcases family_descends (prefixWord ++ tailWord_680900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680911 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_680911 : Nat := 118140960795 + 680911 * 2 ^ 59
def prefixEnd_680911 : Nat := 4983230072969 + 3 ^ 40 * 680911 * 2
def baseEnd_680911 : Nat := 310786334163280592249825

theorem tailTrace_680911 : CollatzResearch.WordTrace tailWord_680911 prefixEnd_680911 310786334163280592249825 := by
  unfold tailWord_680911
  simp only [CollatzResearch.WordTrace]
  refine ⟨24834864436183212185562587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16556576290788808123708391 24834864436183212185562587)
  ·
    refine ⟨37252296654274818278343881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24834864436183212185562587 37252296654274818278343881)
    ·
      refine ⟨27939222490706113708757911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37252296654274818278343881 27939222490706113708757911)
      ·
        refine ⟨41908833736059170563136867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27939222490706113708757911 41908833736059170563136867)
        ·
          refine ⟨62863250604088755844705301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41908833736059170563136867 62863250604088755844705301)
          ·
            refine ⟨2946714872066660430220561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62863250604088755844705301 2946714872066660430220561)
            ·
              refine ⟨2210036154049995322665421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946714872066660430220561 2210036154049995322665421)
              ·
                refine ⟨828763557768748245999533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2210036154049995322665421 828763557768748245999533)
                ·
                  refine ⟨310786334163280592249825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828763557768748245999533 310786334163280592249825)
                  ·
                    rfl

theorem cell20_680911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_680911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680911 prefixEnd_680911 := by exact prefixLift 680911
  have htrace : WordTrace (prefixWord ++ tailWord_680911) baseStart_680911 baseEnd_680911 := by
    simpa [prefixWord, tailWord_680911, baseEnd_680911] using wordTrace_append hprefix tailTrace_680911
  have hstable : (prefixWord ++ tailWord_680911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680911).length < 2 ^ (prefixWord ++ tailWord_680911).sum := by decide
  have hdescent : baseEnd_680911 < baseStart_680911 := by decide
  rcases family_descends (prefixWord ++ tailWord_680911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680942 : List Nat := [4, 1, 2, 1, 4, 1, 7]
def baseStart_680942 : Nat := 118140960795 + 680942 * 2 ^ 59
def prefixEnd_680942 : Nat := 4983230072969 + 3 ^ 40 * 680942 * 2
def baseEnd_680942 : Nat := 34533387045331362468485

theorem tailTrace_680942 : CollatzResearch.WordTrace tailWord_680942 prefixEnd_680942 34533387045331362468485 := by
  unfold tailWord_680942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104499387383863059992635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16557330066047269653294053 3104499387383863059992635)
  ·
    refine ⟨4656749081075794589988953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104499387383863059992635 4656749081075794589988953)
    ·
      refine ⟨3492561810806845942491715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4656749081075794589988953 3492561810806845942491715)
      ·
        refine ⟨5238842716210268913737573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492561810806845942491715 5238842716210268913737573)
        ·
          refine ⟨982283009289425421325795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5238842716210268913737573 982283009289425421325795)
          ·
            refine ⟨1473424513934138131988693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982283009289425421325795 1473424513934138131988693)
            ·
              refine ⟨34533387045331362468485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1473424513934138131988693 34533387045331362468485)
              ·
                rfl

theorem cell20_680942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_680942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680942 prefixEnd_680942 := by exact prefixLift 680942
  have htrace : WordTrace (prefixWord ++ tailWord_680942) baseStart_680942 baseEnd_680942 := by
    simpa [prefixWord, tailWord_680942, baseEnd_680942] using wordTrace_append hprefix tailTrace_680942
  have hstable : (prefixWord ++ tailWord_680942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680942).length < 2 ^ (prefixWord ++ tailWord_680942).sum := by decide
  have hdescent : baseEnd_680942 < baseStart_680942 := by decide
  rcases family_descends (prefixWord ++ tailWord_680942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_680956 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_680956 : Nat := 118140960795 + 680956 * 2 ^ 59
def prefixEnd_680956 : Nat := 4983230072969 + 3 ^ 40 * 680956 * 2
def baseEnd_680956 : Nat := 310806873389460435749641

theorem tailTrace_680956 : CollatzResearch.WordTrace tailWord_680956 prefixEnd_680956 310806873389460435749641 := by
  unfold tailWord_680956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418252860510092435475361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16557670480680123247300481 12418252860510092435475361)
  ·
    refine ⟨9313689645382569326606521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12418252860510092435475361 9313689645382569326606521)
    ·
      refine ⟨6985267234036926994954891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9313689645382569326606521 6985267234036926994954891)
      ·
        refine ⟨10477900851055390492432337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985267234036926994954891 10477900851055390492432337)
        ·
          refine ⟨7858425638291542869324253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10477900851055390492432337 7858425638291542869324253)
          ·
            refine ⟨2946909614359328575996595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7858425638291542869324253 2946909614359328575996595)
            ·
              refine ⟨4420364421538992863994893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946909614359328575996595 4420364421538992863994893)
              ·
                refine ⟨1657636658077122323998085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420364421538992863994893 1657636658077122323998085)
                ·
                  refine ⟨310806873389460435749641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657636658077122323998085 310806873389460435749641)
                  ·
                    rfl

theorem cell20_680956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_680956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_680956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_680956 prefixEnd_680956 := by exact prefixLift 680956
  have htrace : WordTrace (prefixWord ++ tailWord_680956) baseStart_680956 baseEnd_680956 := by
    simpa [prefixWord, tailWord_680956, baseEnd_680956] using wordTrace_append hprefix tailTrace_680956
  have hstable : (prefixWord ++ tailWord_680956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_680956).length < 2 ^ (prefixWord ++ tailWord_680956).sum := by decide
  have hdescent : baseEnd_680956 < baseStart_680956 := by decide
  rcases family_descends (prefixWord ++ tailWord_680956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681008 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_681008 : Nat := 118140960795 + 681008 * 2 ^ 59
def prefixEnd_681008 : Nat := 4983230072969 + 3 ^ 40 * 681008 * 2
def baseEnd_681008 : Nat := 310830607606379366016095

theorem tailTrace_681008 : CollatzResearch.WordTrace tailWord_681008 prefixEnd_681008 310830607606379366016095 := by
  unfold tailWord_681008
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419201158415898875921839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16558934877887865167895785 12419201158415898875921839)
  ·
    refine ⟨18628801737623848313882759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12419201158415898875921839 18628801737623848313882759)
    ·
      refine ⟨27943202606435772470824139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18628801737623848313882759 27943202606435772470824139)
      ·
        refine ⟨41914803909653658706236209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27943202606435772470824139 41914803909653658706236209)
        ·
          refine ⟨31436102932240244029677157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41914803909653658706236209 31436102932240244029677157)
          ·
            refine ⟨5894269299795045755564467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31436102932240244029677157 5894269299795045755564467)
            ·
              refine ⟨8841403949692568633346701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894269299795045755564467 8841403949692568633346701)
              ·
                refine ⟨3315526481134713237505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8841403949692568633346701 3315526481134713237505013)
                ·
                  refine ⟨310830607606379366016095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315526481134713237505013 310830607606379366016095)
                  ·
                    rfl

theorem cell20_681008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_681008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681008 prefixEnd_681008 := by exact prefixLift 681008
  have htrace : WordTrace (prefixWord ++ tailWord_681008) baseStart_681008 baseEnd_681008 := by
    simpa [prefixWord, tailWord_681008, baseEnd_681008] using wordTrace_append hprefix tailTrace_681008
  have hstable : (prefixWord ++ tailWord_681008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681008).length < 2 ^ (prefixWord ++ tailWord_681008).sum := by decide
  have hdescent : baseEnd_681008 < baseStart_681008 := by decide
  rcases family_descends (prefixWord ++ tailWord_681008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681021 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_681021 : Nat := 118140960795 + 681021 * 2 ^ 59
def prefixEnd_681021 : Nat := 4983230072969 + 3 ^ 40 * 681021 * 2
def baseEnd_681021 : Nat := 310836541160609098582709

theorem tailTrace_681021 : CollatzResearch.WordTrace tailWord_681021 prefixEnd_681021 310836541160609098582709 := by
  unfold tailWord_681021
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838876465784700972066917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16559250977189800648044611 24838876465784700972066917)
  ·
    refine ⟨4657289337334631432262547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24838876465784700972066917 4657289337334631432262547)
    ·
      refine ⟨6985934006001947148393821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4657289337334631432262547 6985934006001947148393821)
      ·
        refine ⟨2619725252250730180647683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6985934006001947148393821 2619725252250730180647683)
        ·
          refine ⟨3929587878376095270971525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619725252250730180647683 3929587878376095270971525)
          ·
            refine ⟨736797727195517863307161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3929587878376095270971525 736797727195517863307161)
            ·
              refine ⟨552598295396638397480371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736797727195517863307161 552598295396638397480371)
              ·
                refine ⟨828897443094957596220557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552598295396638397480371 828897443094957596220557)
                ·
                  refine ⟨310836541160609098582709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828897443094957596220557 310836541160609098582709)
                  ·
                    rfl

theorem cell20_681021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_681021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681021 prefixEnd_681021 := by exact prefixLift 681021
  have htrace : WordTrace (prefixWord ++ tailWord_681021) baseStart_681021 baseEnd_681021 := by
    simpa [prefixWord, tailWord_681021, baseEnd_681021] using wordTrace_append hprefix tailTrace_681021
  have hstable : (prefixWord ++ tailWord_681021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681021).length < 2 ^ (prefixWord ++ tailWord_681021).sum := by decide
  have hdescent : baseEnd_681021 < baseStart_681021 := by decide
  rcases family_descends (prefixWord ++ tailWord_681021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681063 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_681063 : Nat := 118140960795 + 681063 * 2 ^ 59
def prefixEnd_681063 : Nat := 4983230072969 + 3 ^ 40 * 681063 * 2
def baseEnd_681063 : Nat := 310855711105043619182537

theorem tailTrace_681063 : CollatzResearch.WordTrace tailWord_681063 prefixEnd_681063 310855711105043619182537 := by
  unfold tailWord_681063
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840408331632542145095843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16560272221088361430063895 24840408331632542145095843)
  ·
    refine ⟨37260612497448813217643765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24840408331632542145095843 37260612497448813217643765)
    ·
      refine ⟨3493182421635826239154103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37260612497448813217643765 3493182421635826239154103)
      ·
        refine ⟨5239773632453739358731155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493182421635826239154103 5239773632453739358731155)
        ·
          refine ⟨7859660448680609038096733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239773632453739358731155 7859660448680609038096733)
          ·
            refine ⟨2947372668255228389286275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7859660448680609038096733 2947372668255228389286275)
            ·
              refine ⟨4421059002382842583929413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947372668255228389286275 4421059002382842583929413)
              ·
                refine ⟨828948562946782984486765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4421059002382842583929413 828948562946782984486765)
                ·
                  refine ⟨310855711105043619182537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828948562946782984486765 310855711105043619182537)
                  ·
                    rfl

theorem cell20_681063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_681063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681063 prefixEnd_681063 := by exact prefixLift 681063
  have htrace : WordTrace (prefixWord ++ tailWord_681063) baseStart_681063 baseEnd_681063 := by
    simpa [prefixWord, tailWord_681063, baseEnd_681063] using wordTrace_append hprefix tailTrace_681063
  have hstable : (prefixWord ++ tailWord_681063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681063).length < 2 ^ (prefixWord ++ tailWord_681063).sum := by decide
  have hdescent : baseEnd_681063 < baseStart_681063 := by decide
  rcases family_descends (prefixWord ++ tailWord_681063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681066 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_681066 : Nat := 118140960795 + 681066 * 2 ^ 59
def prefixEnd_681066 : Nat := 4983230072969 + 3 ^ 40 * 681066 * 2
def baseEnd_681066 : Nat := 310857080386788942082525

theorem tailTrace_681066 : CollatzResearch.WordTrace tailWord_681066 prefixEnd_681066 310857080386788942082525 := by
  unfold tailWord_681066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6210129437655418414363763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16560345167081115771636701 6210129437655418414363763)
  ·
    refine ⟨9315194156483127621545645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6210129437655418414363763 9315194156483127621545645)
    ·
      refine ⟨3493197808681172858079617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9315194156483127621545645 3493197808681172858079617)
      ·
        refine ⟨2619898356510879643559713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3493197808681172858079617 2619898356510879643559713)
        ·
          refine ⟨1964923767383159732669785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619898356510879643559713 1964923767383159732669785)
          ·
            refine ⟨1473692825537369799502339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964923767383159732669785 1473692825537369799502339)
            ·
              refine ⟨2210539238306054699253509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473692825537369799502339 2210539238306054699253509)
              ·
                refine ⟨414476107182385256110033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2210539238306054699253509 414476107182385256110033)
                ·
                  refine ⟨310857080386788942082525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414476107182385256110033 310857080386788942082525)
                  ·
                    rfl

theorem cell20_681066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_681066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681066 prefixEnd_681066 := by exact prefixLift 681066
  have htrace : WordTrace (prefixWord ++ tailWord_681066) baseStart_681066 baseEnd_681066 := by
    simpa [prefixWord, tailWord_681066, baseEnd_681066] using wordTrace_append hprefix tailTrace_681066
  have hstable : (prefixWord ++ tailWord_681066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681066).length < 2 ^ (prefixWord ++ tailWord_681066).sum := by decide
  have hdescent : baseEnd_681066 < baseStart_681066 := by decide
  rcases family_descends (prefixWord ++ tailWord_681066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681118 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_681118 : Nat := 118140960795 + 681118 * 2 ^ 59
def prefixEnd_681118 : Nat := 4983230072969 + 3 ^ 40 * 681118 * 2
def baseEnd_681118 : Nat := 310880814603707872348979

theorem tailTrace_681118 : CollatzResearch.WordTrace tailWord_681118 prefixEnd_681118 310880814603707872348979 := by
  unfold tailWord_681118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105301793304160817293501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16561609564288857692232005 3105301793304160817293501)
  ·
    refine ⟨1164488172489060306485063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3105301793304160817293501 1164488172489060306485063)
    ·
      refine ⟨1746732258733590459727595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164488172489060306485063 1746732258733590459727595)
      ·
        refine ⟨2620098388100385689591393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746732258733590459727595 2620098388100385689591393)
        ·
          refine ⟨1965073791075289267193545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2620098388100385689591393 1965073791075289267193545)
          ·
            refine ⟨1473805343306466950395159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965073791075289267193545 1473805343306466950395159)
            ·
              refine ⟨2210708014959700425592739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473805343306466950395159 2210708014959700425592739)
              ·
                refine ⟨3316062022439550638389109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210708014959700425592739 3316062022439550638389109)
                ·
                  refine ⟨310880814603707872348979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3316062022439550638389109 310880814603707872348979)
                  ·
                    rfl

theorem cell20_681118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_681118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681118 prefixEnd_681118 := by exact prefixLift 681118
  have htrace : WordTrace (prefixWord ++ tailWord_681118) baseStart_681118 baseEnd_681118 := by
    simpa [prefixWord, tailWord_681118, baseEnd_681118] using wordTrace_append hprefix tailTrace_681118
  have hstable : (prefixWord ++ tailWord_681118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681118).length < 2 ^ (prefixWord ++ tailWord_681118).sum := by decide
  have hdescent : baseEnd_681118 < baseStart_681118 := by decide
  rcases family_descends (prefixWord ++ tailWord_681118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681125 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 2]
def baseStart_681125 : Nat := 118140960795 + 681125 * 2 ^ 59
def prefixEnd_681125 : Nat := 4983230072969 + 3 ^ 40 * 681125 * 2
def baseEnd_681125 : Nat := 310884009594446959115617

theorem tailTrace_681125 : CollatzResearch.WordTrace tailWord_681125 prefixEnd_681125 310884009594446959115617 := by
  unfold tailWord_681125
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842669657407926733852829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16561779771605284489235219 24842669657407926733852829)
  ·
    refine ⟨9316001121527972525194811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24842669657407926733852829 9316001121527972525194811)
    ·
      refine ⟨13974001682291958787792217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9316001121527972525194811 13974001682291958787792217)
      ·
        refine ⟨10480501261718969090844163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13974001682291958787792217 10480501261718969090844163)
        ·
          refine ⟨15720751892578453636266245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480501261718969090844163 15720751892578453636266245)
          ·
            refine ⟨2947640979858460056799921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15720751892578453636266245 2947640979858460056799921)
            ·
              refine ⟨2210730734893845042599941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947640979858460056799921 2210730734893845042599941)
              ·
                refine ⟨414512012792595945487489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2210730734893845042599941 414512012792595945487489)
                ·
                  refine ⟨310884009594446959115617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414512012792595945487489 310884009594446959115617)
                  ·
                    rfl

theorem cell20_681125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_681125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681125 prefixEnd_681125 := by exact prefixLift 681125
  have htrace : WordTrace (prefixWord ++ tailWord_681125) baseStart_681125 baseEnd_681125 := by
    simpa [prefixWord, tailWord_681125, baseEnd_681125] using wordTrace_append hprefix tailTrace_681125
  have hstable : (prefixWord ++ tailWord_681125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681125).length < 2 ^ (prefixWord ++ tailWord_681125).sum := by decide
  have hdescent : baseEnd_681125 < baseStart_681125 := by decide
  rcases family_descends (prefixWord ++ tailWord_681125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681160 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_681160 : Nat := 118140960795 + 681160 * 2 ^ 59
def prefixEnd_681160 : Nat := 4983230072969 + 3 ^ 40 * 681160 * 2
def baseEnd_681160 : Nat := 310899984548142392948807

theorem tailTrace_681160 : CollatzResearch.WordTrace tailWord_681160 prefixEnd_681160 310899984548142392948807 := by
  unfold tailWord_681160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12421973106140563855688467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16562630808187418474251289 12421973106140563855688467)
  ·
    refine ⟨18632959659210845783532701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12421973106140563855688467 18632959659210845783532701)
    ·
      refine ⟨6987359872204067168824763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18632959659210845783532701 6987359872204067168824763)
      ·
        refine ⟨10481039808306100753237145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987359872204067168824763 10481039808306100753237145)
        ·
          refine ⟨7860779856229575564927859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10481039808306100753237145 7860779856229575564927859)
          ·
            refine ⟨11791169784344363347391789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860779856229575564927859 11791169784344363347391789)
            ·
              refine ⟨4421688669129136255271921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11791169784344363347391789 4421688669129136255271921)
              ·
                refine ⟨3316266501846852191453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4421688669129136255271921 3316266501846852191453941)
                ·
                  refine ⟨310899984548142392948807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3316266501846852191453941 310899984548142392948807)
                  ·
                    rfl

theorem cell20_681160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_681160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681160 prefixEnd_681160 := by exact prefixLift 681160
  have htrace : WordTrace (prefixWord ++ tailWord_681160) baseStart_681160 baseEnd_681160 := by
    simpa [prefixWord, tailWord_681160, baseEnd_681160] using wordTrace_append hprefix tailTrace_681160
  have hstable : (prefixWord ++ tailWord_681160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681160).length < 2 ^ (prefixWord ++ tailWord_681160).sum := by decide
  have hdescent : baseEnd_681160 < baseStart_681160 := by decide
  rcases family_descends (prefixWord ++ tailWord_681160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681184 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_681184 : Nat := 118140960795 + 681184 * 2 ^ 59
def prefixEnd_681184 : Nat := 4983230072969 + 3 ^ 40 * 681184 * 2
def baseEnd_681184 : Nat := 310910938802104976148709

theorem tailTrace_681184 : CollatzResearch.WordTrace tailWord_681184 prefixEnd_681184 310910938802104976148709 := by
  unfold tailWord_681184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422410782097089905125303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16563214376129453206833737 12422410782097089905125303)
  ·
    refine ⟨18633616173145634857687955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12422410782097089905125303 18633616173145634857687955)
    ·
      refine ⟨27950424259718452286531933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18633616173145634857687955 27950424259718452286531933)
      ·
        refine ⟨10481409097394419607449475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27950424259718452286531933 10481409097394419607449475)
        ·
          refine ⟨15722113646091629411174213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10481409097394419607449475 15722113646091629411174213)
          ·
            refine ⟨2947896308642180514595165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15722113646091629411174213 2947896308642180514595165)
            ·
              refine ⟨1105461115740817692973187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2947896308642180514595165 1105461115740817692973187)
              ·
                refine ⟨1658191673611226539459781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105461115740817692973187 1658191673611226539459781)
                ·
                  refine ⟨310910938802104976148709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658191673611226539459781 310910938802104976148709)
                  ·
                    rfl

theorem cell20_681184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_681184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681184 prefixEnd_681184 := by exact prefixLift 681184
  have htrace : WordTrace (prefixWord ++ tailWord_681184) baseStart_681184 baseEnd_681184 := by
    simpa [prefixWord, tailWord_681184, baseEnd_681184] using wordTrace_append hprefix tailTrace_681184
  have hstable : (prefixWord ++ tailWord_681184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681184).length < 2 ^ (prefixWord ++ tailWord_681184).sum := by decide
  have hdescent : baseEnd_681184 < baseStart_681184 := by decide
  rcases family_descends (prefixWord ++ tailWord_681184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681194 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_681194 : Nat := 118140960795 + 681194 * 2 ^ 59
def prefixEnd_681194 : Nat := 4983230072969 + 3 ^ 40 * 681194 * 2
def baseEnd_681194 : Nat := 310915503074589385815335

theorem tailTrace_681194 : CollatzResearch.WordTrace tailWord_681194 prefixEnd_681194 310915503074589385815335 := by
  unfold tailWord_681194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6211296573539487879528659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16563457529438634345409757 6211296573539487879528659)
  ·
    refine ⟨9316944860309231819292989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6211296573539487879528659 9316944860309231819292989)
    ·
      refine ⟨3493854322615961932234871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9316944860309231819292989 3493854322615961932234871)
      ·
        refine ⟨5240781483923942898352307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493854322615961932234871 5240781483923942898352307)
        ·
          refine ⟨7861172225885914347528461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5240781483923942898352307 7861172225885914347528461)
          ·
            refine ⟨2947939584707217880323173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7861172225885914347528461 2947939584707217880323173)
            ·
              refine ⟨552738672132603352560595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2947939584707217880323173 552738672132603352560595)
              ·
                refine ⟨829108008198905028840893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552738672132603352560595 829108008198905028840893)
                ·
                  refine ⟨310915503074589385815335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829108008198905028840893 310915503074589385815335)
                  ·
                    rfl

theorem cell20_681194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_681194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681194 prefixEnd_681194 := by exact prefixLift 681194
  have htrace : WordTrace (prefixWord ++ tailWord_681194) baseStart_681194 baseEnd_681194 := by
    simpa [prefixWord, tailWord_681194, baseEnd_681194] using wordTrace_append hprefix tailTrace_681194
  have hstable : (prefixWord ++ tailWord_681194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681194).length < 2 ^ (prefixWord ++ tailWord_681194).sum := by decide
  have hdescent : baseEnd_681194 < baseStart_681194 := by decide
  rcases family_descends (prefixWord ++ tailWord_681194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681229 : List Nat := [1, 7, 12]
def baseStart_681229 : Nat := 118140960795 + 681229 * 2 ^ 59
def prefixEnd_681229 : Nat := 4983230072969 + 3 ^ 40 * 681229 * 2
def baseEnd_681229 : Nat := 426517802507935280725

theorem tailTrace_681229 : CollatzResearch.WordTrace tailWord_681229 prefixEnd_681229 426517802507935280725 := by
  unfold tailWord_681229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846462849031152495638741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16564308566020768330425827 24846462849031152495638741)
  ·
    refine ⟨582338973024167636616533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24846462849031152495638741 582338973024167636616533)
    ·
      refine ⟨426517802507935280725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 582338973024167636616533 426517802507935280725)
      ·
        rfl

theorem cell20_681229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 12].length) (baseStart_681229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681229 prefixEnd_681229 := by exact prefixLift 681229
  have htrace : WordTrace (prefixWord ++ tailWord_681229) baseStart_681229 baseEnd_681229 := by
    simpa [prefixWord, tailWord_681229, baseEnd_681229] using wordTrace_append hprefix tailTrace_681229
  have hstable : (prefixWord ++ tailWord_681229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681229).length < 2 ^ (prefixWord ++ tailWord_681229).sum := by decide
  have hdescent : baseEnd_681229 < baseStart_681229 := by decide
  rcases family_descends (prefixWord ++ tailWord_681229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681239 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 2]
def baseStart_681239 : Nat := 118140960795 + 681239 * 2 ^ 59
def prefixEnd_681239 : Nat := 4983230072969 + 3 ^ 40 * 681239 * 2
def baseEnd_681239 : Nat := 310936042300769229315151

theorem tailTrace_681239 : CollatzResearch.WordTrace tailWord_681239 prefixEnd_681239 310936042300769229315151 := by
  unfold tailWord_681239
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846827578994924203502771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16564551719329949469001847 24846827578994924203502771)
  ·
    refine ⟨37270241368492386305254157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24846827578994924203502771 37270241368492386305254157)
    ·
      refine ⟨13976340513184644864470309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37270241368492386305254157 13976340513184644864470309)
      ·
        refine ⟨2620563846222120912088183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13976340513184644864470309 2620563846222120912088183)
        ·
          refine ⟨3930845769333181368132275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620563846222120912088183 3930845769333181368132275)
          ·
            refine ⟨5896268653999772052198413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930845769333181368132275 5896268653999772052198413)
            ·
              refine ⟨2211100745249914519574405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5896268653999772052198413 2211100745249914519574405)
              ·
                refine ⟨414581389734358972420201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2211100745249914519574405 414581389734358972420201)
                ·
                  refine ⟨310936042300769229315151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414581389734358972420201 310936042300769229315151)
                  ·
                    rfl

theorem cell20_681239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2].length) (baseStart_681239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681239 prefixEnd_681239 := by exact prefixLift 681239
  have htrace : WordTrace (prefixWord ++ tailWord_681239) baseStart_681239 baseEnd_681239 := by
    simpa [prefixWord, tailWord_681239, baseEnd_681239] using wordTrace_append hprefix tailTrace_681239
  have hstable : (prefixWord ++ tailWord_681239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681239).length < 2 ^ (prefixWord ++ tailWord_681239).sum := by decide
  have hdescent : baseEnd_681239 < baseStart_681239 := by decide
  rcases family_descends (prefixWord ++ tailWord_681239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681243 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_681243 : Nat := 118140960795 + 681243 * 2 ^ 59
def prefixEnd_681243 : Nat := 4983230072969 + 3 ^ 40 * 681243 * 2
def baseEnd_681243 : Nat := 310937868009762993181801

theorem tailTrace_681243 : CollatzResearch.WordTrace tailWord_681243 prefixEnd_681243 310937868009762993181801 := by
  unfold tailWord_681243
  simp only [CollatzResearch.WordTrace]
  refine ⟨24846973470980432886648383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16564648980653621924432255 24846973470980432886648383)
  ·
    refine ⟨37270460206470649329972575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24846973470980432886648383 37270460206470649329972575)
    ·
      refine ⟨55905690309705973994958863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37270460206470649329972575 55905690309705973994958863)
      ·
        refine ⟨83858535464558960992438295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55905690309705973994958863 83858535464558960992438295)
        ·
          refine ⟨125787803196838441488657443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83858535464558960992438295 125787803196838441488657443)
          ·
            refine ⟨188681704795257662232986165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125787803196838441488657443 188681704795257662232986165)
            ·
              refine ⟨17688909824555405834342453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188681704795257662232986165 17688909824555405834342453)
              ·
                refine ⟨1658335296052069296969605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17688909824555405834342453 1658335296052069296969605)
                ·
                  refine ⟨310937868009762993181801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658335296052069296969605 310937868009762993181801)
                  ·
                    rfl

theorem cell20_681243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_681243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681243 prefixEnd_681243 := by exact prefixLift 681243
  have htrace : WordTrace (prefixWord ++ tailWord_681243) baseStart_681243 baseEnd_681243 := by
    simpa [prefixWord, tailWord_681243, baseEnd_681243] using wordTrace_append hprefix tailTrace_681243
  have hstable : (prefixWord ++ tailWord_681243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681243).length < 2 ^ (prefixWord ++ tailWord_681243).sum := by decide
  have hdescent : baseEnd_681243 < baseStart_681243 := by decide
  rcases family_descends (prefixWord ++ tailWord_681243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681253 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_681253 : Nat := 118140960795 + 681253 * 2 ^ 59
def prefixEnd_681253 : Nat := 4983230072969 + 3 ^ 40 * 681253 * 2
def baseEnd_681253 : Nat := 310942432282247402848427

theorem tailTrace_681253 : CollatzResearch.WordTrace tailWord_681253 prefixEnd_681253 310942432282247402848427 := by
  unfold tailWord_681253
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847338200944204594512413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16564892133962803063008275 24847338200944204594512413)
  ·
    refine ⟨9317751825354076722942155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24847338200944204594512413 9317751825354076722942155)
    ·
      refine ⟨13976627738031115084413233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9317751825354076722942155 13976627738031115084413233)
      ·
        refine ⟨10482470803523336313309925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13976627738031115084413233 10482470803523336313309925)
        ·
          refine ⟨1965463275660625558745611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10482470803523336313309925 1965463275660625558745611)
          ·
            refine ⟨2948194913490938338118417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965463275660625558745611 2948194913490938338118417)
            ·
              refine ⟨2211146185118203753588813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948194913490938338118417 2211146185118203753588813)
              ·
                refine ⟨829179819419326407595805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2211146185118203753588813 829179819419326407595805)
                ·
                  refine ⟨310942432282247402848427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829179819419326407595805 310942432282247402848427)
                  ·
                    rfl

theorem cell20_681253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_681253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681253 prefixEnd_681253 := by exact prefixLift 681253
  have htrace : WordTrace (prefixWord ++ tailWord_681253) baseStart_681253 baseEnd_681253 := by
    simpa [prefixWord, tailWord_681253, baseEnd_681253] using wordTrace_append hprefix tailTrace_681253
  have hstable : (prefixWord ++ tailWord_681253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681253).length < 2 ^ (prefixWord ++ tailWord_681253).sum := by decide
  have hdescent : baseEnd_681253 < baseStart_681253 := by decide
  rcases family_descends (prefixWord ++ tailWord_681253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681274 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_681274 : Nat := 118140960795 + 681274 * 2 ^ 59
def prefixEnd_681274 : Nat := 4983230072969 + 3 ^ 40 * 681274 * 2
def baseEnd_681274 : Nat := 310952017254464663148341

theorem tailTrace_681274 : CollatzResearch.WordTrace tailWord_681274 prefixEnd_681274 310952017254464663148341 := by
  unfold tailWord_681274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212026033467031295256719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16565402755912083454017917 6212026033467031295256719)
  ·
    refine ⟨9318039050200546942885079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212026033467031295256719 9318039050200546942885079)
    ·
      refine ⟨13977058575300820414327619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9318039050200546942885079 13977058575300820414327619)
      ·
        refine ⟨20965587862951230621491429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13977058575300820414327619 20965587862951230621491429)
        ·
          refine ⟨3931047724303355741529643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20965587862951230621491429 3931047724303355741529643)
          ·
            refine ⟨5896571586455033612294465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931047724303355741529643 5896571586455033612294465)
            ·
              refine ⟨4422428689841275209220849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5896571586455033612294465 4422428689841275209220849)
              ·
                refine ⟨3316821517380956406915637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422428689841275209220849 3316821517380956406915637)
                ·
                  refine ⟨310952017254464663148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3316821517380956406915637 310952017254464663148341)
                  ·
                    rfl

theorem cell20_681274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_681274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681274 prefixEnd_681274 := by exact prefixLift 681274
  have htrace : WordTrace (prefixWord ++ tailWord_681274) baseStart_681274 baseEnd_681274 := by
    simpa [prefixWord, tailWord_681274, baseEnd_681274] using wordTrace_append hprefix tailTrace_681274
  have hstable : (prefixWord ++ tailWord_681274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681274).length < 2 ^ (prefixWord ++ tailWord_681274).sum := by decide
  have hdescent : baseEnd_681274 < baseStart_681274 := by decide
  rcases family_descends (prefixWord ++ tailWord_681274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681284 : List Nat := [2, 3, 4, 1, 1, 2, 7]
def baseStart_681284 : Nat := 118140960795 + 681284 * 2 ^ 59
def prefixEnd_681284 : Nat := 4983230072969 + 3 ^ 40 * 681284 * 2
def baseEnd_681284 : Nat := 34550731280772119201663

theorem tailTrace_681284 : CollatzResearch.WordTrace tailWord_681284 prefixEnd_681284 34550731280772119201663 := by
  unfold tailWord_681284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424234431915948444445453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16565645909221264592593937 12424234431915948444445453)
  ·
    refine ⟨4659087911968480666667045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12424234431915948444445453 4659087911968480666667045)
    ·
      refine ⟨873578983494090125000071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4659087911968480666667045 873578983494090125000071)
      ·
        refine ⟨1310368475241135187500107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873578983494090125000071 1310368475241135187500107)
        ·
          refine ⟨1965552712861702781250161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310368475241135187500107 1965552712861702781250161)
          ·
            refine ⟨1474164534646277085937621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1965552712861702781250161 1474164534646277085937621)
            ·
              refine ⟨34550731280772119201663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1474164534646277085937621 34550731280772119201663)
              ·
                rfl

theorem cell20_681284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_681284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681284 prefixEnd_681284 := by exact prefixLift 681284
  have htrace : WordTrace (prefixWord ++ tailWord_681284) baseStart_681284 baseEnd_681284 := by
    simpa [prefixWord, tailWord_681284, baseEnd_681284] using wordTrace_append hprefix tailTrace_681284
  have hstable : (prefixWord ++ tailWord_681284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681284).length < 2 ^ (prefixWord ++ tailWord_681284).sum := by decide
  have hdescent : baseEnd_681284 < baseStart_681284 := by decide
  rcases family_descends (prefixWord ++ tailWord_681284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681322 : List Nat := [3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_681322 : Nat := 118140960795 + 681322 * 2 ^ 59
def prefixEnd_681322 : Nat := 4983230072969 + 3 ^ 40 * 681322 * 2
def baseEnd_681322 : Nat := 103657975254129943182715

theorem tailTrace_681322 : CollatzResearch.WordTrace tailWord_681322 prefixEnd_681322 103657975254129943182715 := by
  unfold tailWord_681322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212463709423557344693555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16566569891796152919182813 6212463709423557344693555)
  ·
    refine ⟨9318695564135336017040333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212463709423557344693555 9318695564135336017040333)
    ·
      refine ⟨3494510836550751006390125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9318695564135336017040333 3494510836550751006390125)
      ·
        refine ⟨1310441563706531627396297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3494510836550751006390125 1310441563706531627396297)
        ·
          refine ⟨982831172779898720547223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310441563706531627396297 982831172779898720547223)
          ·
            refine ⟨1474246759169848080820835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982831172779898720547223 1474246759169848080820835)
            ·
              refine ⟨2211370138754772121231253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474246759169848080820835 2211370138754772121231253)
              ·
                refine ⟨103657975254129943182715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2211370138754772121231253 103657975254129943182715)
                ·
                  rfl

theorem cell20_681322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_681322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681322 prefixEnd_681322 := by exact prefixLift 681322
  have htrace : WordTrace (prefixWord ++ tailWord_681322) baseStart_681322 baseEnd_681322 := by
    simpa [prefixWord, tailWord_681322, baseEnd_681322] using wordTrace_append hprefix tailTrace_681322
  have hstable : (prefixWord ++ tailWord_681322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681322).length < 2 ^ (prefixWord ++ tailWord_681322).sum := by decide
  have hdescent : baseEnd_681322 < baseStart_681322 := by decide
  rcases family_descends (prefixWord ++ tailWord_681322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681346 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_681346 : Nat := 118140960795 + 681346 * 2 ^ 59
def prefixEnd_681346 : Nat := 4983230072969 + 3 ^ 40 * 681346 * 2
def baseEnd_681346 : Nat := 310984880016352412748047

theorem tailTrace_681346 : CollatzResearch.WordTrace tailWord_681346 prefixEnd_681346 310984880016352412748047 := by
  unfold tailWord_681346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212682547401820369411973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16567153459738187651765261 6212682547401820369411973)
  ·
    refine ⟨1164877977637841319264745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6212682547401820369411973 1164877977637841319264745)
    ·
      refine ⟨873658483228380989448559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164877977637841319264745 873658483228380989448559)
      ·
        refine ⟨1310487724842571484172839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873658483228380989448559 1310487724842571484172839)
        ·
          refine ⟨1965731587263857226259259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310487724842571484172839 1965731587263857226259259)
          ·
            refine ⟨2948597380895785839388889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965731587263857226259259 2948597380895785839388889)
            ·
              refine ⟨2211448035671839379541667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948597380895785839388889 2211448035671839379541667)
              ·
                refine ⟨3317172053507759069312501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211448035671839379541667 3317172053507759069312501)
                ·
                  refine ⟨310984880016352412748047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3317172053507759069312501 310984880016352412748047)
                  ·
                    rfl

theorem cell20_681346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_681346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681346 prefixEnd_681346 := by exact prefixLift 681346
  have htrace : WordTrace (prefixWord ++ tailWord_681346) baseStart_681346 baseEnd_681346 := by
    simpa [prefixWord, tailWord_681346, baseEnd_681346] using wordTrace_append hprefix tailTrace_681346
  have hstable : (prefixWord ++ tailWord_681346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681346).length < 2 ^ (prefixWord ++ tailWord_681346).sum := by decide
  have hdescent : baseEnd_681346 < baseStart_681346 := by decide
  rcases family_descends (prefixWord ++ tailWord_681346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681353 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_681353 : Nat := 118140960795 + 681353 * 2 ^ 59
def prefixEnd_681353 : Nat := 4983230072969 + 3 ^ 40 * 681353 * 2
def baseEnd_681353 : Nat := 310988075007091499514685

theorem tailTrace_681353 : CollatzResearch.WordTrace tailWord_681353 prefixEnd_681353 310988075007091499514685 := by
  unfold tailWord_681353
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850985500581921673152713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16567323667054614448768475 24850985500581921673152713)
  ·
    refine ⟨18638239125436441254864535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24850985500581921673152713 18638239125436441254864535)
    ·
      refine ⟨27957358688154661882296803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18638239125436441254864535 27957358688154661882296803)
      ·
        refine ⟨41936038032231992823445205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27957358688154661882296803 41936038032231992823445205)
        ·
          refine ⟨982875891380437331799497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41936038032231992823445205 982875891380437331799497)
          ·
            refine ⟨737156918535327998849623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982875891380437331799497 737156918535327998849623)
            ·
              refine ⟨1105735377802991998274435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737156918535327998849623 1105735377802991998274435)
              ·
                refine ⟨1658603066704487997411653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105735377802991998274435 1658603066704487997411653)
                ·
                  refine ⟨310988075007091499514685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658603066704487997411653 310988075007091499514685)
                  ·
                    rfl

theorem cell20_681353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_681353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681353 prefixEnd_681353 := by exact prefixLift 681353
  have htrace : WordTrace (prefixWord ++ tailWord_681353) baseStart_681353 baseEnd_681353 := by
    simpa [prefixWord, tailWord_681353, baseEnd_681353] using wordTrace_append hprefix tailTrace_681353
  have hstable : (prefixWord ++ tailWord_681353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681353).length < 2 ^ (prefixWord ++ tailWord_681353).sum := by decide
  have hdescent : baseEnd_681353 < baseStart_681353 := by decide
  rcases family_descends (prefixWord ++ tailWord_681353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681404 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_681404 : Nat := 118140960795 + 681404 * 2 ^ 59
def prefixEnd_681404 : Nat := 4983230072969 + 3 ^ 40 * 681404 * 2
def baseEnd_681404 : Nat := 311011352796761988814477

theorem tailTrace_681404 : CollatzResearch.WordTrace tailWord_681404 prefixEnd_681404 311011352796761988814477 := by
  unfold tailWord_681404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12426422811698578691629633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16568563748931438255506177 12426422811698578691629633)
  ·
    refine ⟨9319817108773934018722225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12426422811698578691629633 9319817108773934018722225)
    ·
      refine ⟨6989862831580450514041669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9319817108773934018722225 6989862831580450514041669)
      ·
        refine ⟨1310599280921334471382813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6989862831580450514041669 1310599280921334471382813)
        ·
          refine ⟨491474730345500426768555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310599280921334471382813 491474730345500426768555)
          ·
            refine ⟨737212095518250640152833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491474730345500426768555 737212095518250640152833)
            ·
              refine ⟨552909071638687980114625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737212095518250640152833 552909071638687980114625)
              ·
                refine ⟨414681803729015985085969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552909071638687980114625 414681803729015985085969)
                ·
                  refine ⟨311011352796761988814477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414681803729015985085969 311011352796761988814477)
                  ·
                    rfl

theorem cell20_681404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_681404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681404 prefixEnd_681404 := by exact prefixLift 681404
  have htrace : WordTrace (prefixWord ++ tailWord_681404) baseStart_681404 baseEnd_681404 := by
    simpa [prefixWord, tailWord_681404, baseEnd_681404] using wordTrace_append hprefix tailTrace_681404
  have hstable : (prefixWord ++ tailWord_681404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681404).length < 2 ^ (prefixWord ++ tailWord_681404).sum := by decide
  have hdescent : baseEnd_681404 < baseStart_681404 := by decide
  rcases family_descends (prefixWord ++ tailWord_681404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681405 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_681405 : Nat := 118140960795 + 681405 * 2 ^ 59
def prefixEnd_681405 : Nat := 4983230072969 + 3 ^ 40 * 681405 * 2
def baseEnd_681405 : Nat := 311011809224010429781139

theorem tailTrace_681405 : CollatzResearch.WordTrace tailWord_681405 prefixEnd_681405 311011809224010429781139 := by
  unfold tailWord_681405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24852882096393534554045669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16568588064262356369363779 24852882096393534554045669)
  ·
    refine ⟨4659915393073787728883563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24852882096393534554045669 4659915393073787728883563)
    ·
      refine ⟨6989873089610681593325345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4659915393073787728883563 6989873089610681593325345)
      ·
        refine ⟨5242404817208011194994009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6989873089610681593325345 5242404817208011194994009)
        ·
          refine ⟨3931803612906008396245507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5242404817208011194994009 3931803612906008396245507)
          ·
            refine ⟨5897705419359012594368261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931803612906008396245507 5897705419359012594368261)
            ·
              refine ⟨1105819766129814861444049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5897705419359012594368261 1105819766129814861444049)
              ·
                refine ⟨829364824597361146083037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105819766129814861444049 829364824597361146083037)
                ·
                  refine ⟨311011809224010429781139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829364824597361146083037 311011809224010429781139)
                  ·
                    rfl

theorem cell20_681405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_681405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681405 prefixEnd_681405 := by exact prefixLift 681405
  have htrace : WordTrace (prefixWord ++ tailWord_681405) baseStart_681405 baseEnd_681405 := by
    simpa [prefixWord, tailWord_681405, baseEnd_681405] using wordTrace_append hprefix tailTrace_681405
  have hstable : (prefixWord ++ tailWord_681405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681405).length < 2 ^ (prefixWord ++ tailWord_681405).sum := by decide
  have hdescent : baseEnd_681405 < baseStart_681405 := by decide
  rcases family_descends (prefixWord ++ tailWord_681405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681433 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_681433 : Nat := 118140960795 + 681433 * 2 ^ 59
def prefixEnd_681433 : Nat := 4983230072969 + 3 ^ 40 * 681433 * 2
def baseEnd_681433 : Nat := 311024589186966776847691

theorem tailTrace_681433 : CollatzResearch.WordTrace tailWord_681433 prefixEnd_681433 311024589186966776847691 := by
  unfold tailWord_681433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24853903340292095336064953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16569268893528063557376635 24853903340292095336064953)
  ·
    refine ⟨18640427505219071502048715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24853903340292095336064953 18640427505219071502048715)
    ·
      refine ⟨27960641257828607253073073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18640427505219071502048715 27960641257828607253073073)
      ·
        refine ⟨20970480943371455439804805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27960641257828607253073073 20970480943371455439804805)
        ·
          refine ⟨3931965176882147894963401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20970480943371455439804805 3931965176882147894963401)
          ·
            refine ⟨2948973882661610921222551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931965176882147894963401 2948973882661610921222551)
            ·
              refine ⟨4423460823992416381833827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948973882661610921222551 4423460823992416381833827)
              ·
                refine ⟨6635191235988624572750741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423460823992416381833827 6635191235988624572750741)
                ·
                  refine ⟨311024589186966776847691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6635191235988624572750741 311024589186966776847691)
                  ·
                    rfl

theorem cell20_681433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_681433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681433 prefixEnd_681433 := by exact prefixLift 681433
  have htrace : WordTrace (prefixWord ++ tailWord_681433) baseStart_681433 baseEnd_681433 := by
    simpa [prefixWord, tailWord_681433, baseEnd_681433] using wordTrace_append hprefix tailTrace_681433
  have hstable : (prefixWord ++ tailWord_681433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681433).length < 2 ^ (prefixWord ++ tailWord_681433).sum := by decide
  have hdescent : baseEnd_681433 < baseStart_681433 := by decide
  rcases family_descends (prefixWord ++ tailWord_681433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681464 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_681464 : Nat := 118140960795 + 681464 * 2 ^ 59
def prefixEnd_681464 : Nat := 4983230072969 + 3 ^ 40 * 681464 * 2
def baseEnd_681464 : Nat := 311038738431668446814231

theorem tailTrace_681464 : CollatzResearch.WordTrace tailWord_681464 prefixEnd_681464 311038738431668446814231 := by
  unfold tailWord_681464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427517001589893815221723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16570022668786525086962297 12427517001589893815221723)
  ·
    refine ⟨18641275502384840722832585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427517001589893815221723 18641275502384840722832585)
    ·
      refine ⟨13980956626788630542124439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18641275502384840722832585 13980956626788630542124439)
      ·
        refine ⟨20971434940182945813186659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13980956626788630542124439 20971434940182945813186659)
        ·
          refine ⟨31457152410274418719779989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20971434940182945813186659 31457152410274418719779989)
          ·
            refine ⟨1474554019231613377489687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31457152410274418719779989 1474554019231613377489687)
            ·
              refine ⟨2211831028847420066234531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474554019231613377489687 2211831028847420066234531)
              ·
                refine ⟨3317746543271130099351797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211831028847420066234531 3317746543271130099351797)
                ·
                  refine ⟨311038738431668446814231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3317746543271130099351797 311038738431668446814231)
                  ·
                    rfl

theorem cell20_681464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_681464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681464 prefixEnd_681464 := by exact prefixLift 681464
  have htrace : WordTrace (prefixWord ++ tailWord_681464) baseStart_681464 baseEnd_681464 := by
    simpa [prefixWord, tailWord_681464, baseEnd_681464] using wordTrace_append hprefix tailTrace_681464
  have hstable : (prefixWord ++ tailWord_681464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681464).length < 2 ^ (prefixWord ++ tailWord_681464).sum := by decide
  have hdescent : baseEnd_681464 < baseStart_681464 := by decide
  rcases family_descends (prefixWord ++ tailWord_681464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681481 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 3]
def baseStart_681481 : Nat := 118140960795 + 681481 * 2 ^ 59
def prefixEnd_681481 : Nat := 4983230072969 + 3 ^ 40 * 681481 * 2
def baseEnd_681481 : Nat := 311046497694891943247495

theorem tailTrace_681481 : CollatzResearch.WordTrace tailWord_681481 prefixEnd_681481 311046497694891943247495 := by
  unfold tailWord_681481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24855654044118199533812297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16570436029412133022541531 24855654044118199533812297)
  ·
    refine ⟨18641740533088649650359223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24855654044118199533812297 18641740533088649650359223)
    ·
      refine ⟨27962610799632974475538835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641740533088649650359223 27962610799632974475538835)
      ·
        refine ⟨41943916199449461713308253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27962610799632974475538835 41943916199449461713308253)
        ·
          refine ⟨15728968574793548142490595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41943916199449461713308253 15728968574793548142490595)
          ·
            refine ⟨23593452862190322213735893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15728968574793548142490595 23593452862190322213735893)
            ·
              refine ⟨552971551457585676884435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23593452862190322213735893 552971551457585676884435)
              ·
                refine ⟨829457327186378515326653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552971551457585676884435 829457327186378515326653)
                ·
                  refine ⟨311046497694891943247495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829457327186378515326653 311046497694891943247495)
                  ·
                    rfl

theorem cell20_681481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_681481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681481 prefixEnd_681481 := by exact prefixLift 681481
  have htrace : WordTrace (prefixWord ++ tailWord_681481) baseStart_681481 baseEnd_681481 := by
    simpa [prefixWord, tailWord_681481, baseEnd_681481] using wordTrace_append hprefix tailTrace_681481
  have hstable : (prefixWord ++ tailWord_681481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681481).length < 2 ^ (prefixWord ++ tailWord_681481).sum := by decide
  have hdescent : baseEnd_681481 < baseStart_681481 := by decide
  rcases family_descends (prefixWord ++ tailWord_681481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681505 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 2]
def baseStart_681505 : Nat := 118140960795 + 681505 * 2 ^ 59
def prefixEnd_681505 : Nat := 4983230072969 + 3 ^ 40 * 681505 * 2
def baseEnd_681505 : Nat := 311057451948854526447397

theorem tailTrace_681505 : CollatzResearch.WordTrace tailWord_681505 prefixEnd_681505 311057451948854526447397 := by
  unfold tailWord_681505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24856529396031251632685969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16571019597354167755123979 24856529396031251632685969)
  ·
    refine ⟨18642397047023438724514477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24856529396031251632685969 18642397047023438724514477)
    ·
      refine ⟨6990898892633789521692929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18642397047023438724514477 6990898892633789521692929)
      ·
        refine ⟨5243174169475342141269697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6990898892633789521692929 5243174169475342141269697)
        ·
          refine ⟨3932380627106506605952273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5243174169475342141269697 3932380627106506605952273)
          ·
            refine ⟨2949285470329879954464205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932380627106506605952273 2949285470329879954464205)
            ·
              refine ⟨1105982051373704982924077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2949285470329879954464205 1105982051373704982924077)
              ·
                refine ⟨414743269265139368596529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105982051373704982924077 414743269265139368596529)
                ·
                  refine ⟨311057451948854526447397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414743269265139368596529 311057451948854526447397)
                  ·
                    rfl

theorem cell20_681505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_681505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681505 prefixEnd_681505 := by exact prefixLift 681505
  have htrace : WordTrace (prefixWord ++ tailWord_681505) baseStart_681505 baseEnd_681505 := by
    simpa [prefixWord, tailWord_681505, baseEnd_681505] using wordTrace_append hprefix tailTrace_681505
  have hstable : (prefixWord ++ tailWord_681505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681505).length < 2 ^ (prefixWord ++ tailWord_681505).sum := by decide
  have hdescent : baseEnd_681505 < baseStart_681505 := by decide
  rcases family_descends (prefixWord ++ tailWord_681505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681512 : List Nat := [2, 1, 5, 2, 2, 2, 6]
def baseStart_681512 : Nat := 118140960795 + 681512 * 2 ^ 59
def prefixEnd_681512 : Nat := 4983230072969 + 3 ^ 40 * 681512 * 2
def baseEnd_681512 : Nat := 34562294104399290357115

theorem tailTrace_681512 : CollatzResearch.WordTrace tailWord_681512 prefixEnd_681512 34562294104399290357115 := by
  unfold tailWord_681512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428392353502945914095395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16571189804670594552127193 12428392353502945914095395)
  ·
    refine ⟨18642588530254418871143093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12428392353502945914095395 18642588530254418871143093)
    ·
      refine ⟨1747742674711351769169665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18642588530254418871143093 1747742674711351769169665)
      ·
        refine ⟨1310807006033513826877249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1747742674711351769169665 1310807006033513826877249)
        ·
          refine ⟨983105254525135370157937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310807006033513826877249 983105254525135370157937)
          ·
            refine ⟨737328940893851527618453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983105254525135370157937 737328940893851527618453)
            ·
              refine ⟨34562294104399290357115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 737328940893851527618453 34562294104399290357115)
              ·
                rfl

theorem cell20_681512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_681512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681512 prefixEnd_681512 := by exact prefixLift 681512
  have htrace : WordTrace (prefixWord ++ tailWord_681512) baseStart_681512 baseEnd_681512 := by
    simpa [prefixWord, tailWord_681512, baseEnd_681512] using wordTrace_append hprefix tailTrace_681512
  have hstable : (prefixWord ++ tailWord_681512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681512).length < 2 ^ (prefixWord ++ tailWord_681512).sum := by decide
  have hdescent : baseEnd_681512 < baseStart_681512 := by decide
  rcases family_descends (prefixWord ++ tailWord_681512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681561 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_681561 : Nat := 118140960795 + 681561 * 2 ^ 59
def prefixEnd_681561 : Nat := 4983230072969 + 3 ^ 40 * 681561 * 2
def baseEnd_681561 : Nat := 311083011874767220580501

theorem tailTrace_681561 : CollatzResearch.WordTrace tailWord_681561 prefixEnd_681561 311083011874767220580501 := by
  unfold tailWord_681561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24858571883828373196724537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16572381255885582131149691 24858571883828373196724537)
  ·
    refine ⟨18643928912871279897543403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24858571883828373196724537 18643928912871279897543403)
    ·
      refine ⟨27965893369306919846315105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18643928912871279897543403 27965893369306919846315105)
      ·
        refine ⟨20974420026980189884736329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27965893369306919846315105 20974420026980189884736329)
        ·
          refine ⟨15730815020235142413552247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20974420026980189884736329 15730815020235142413552247)
          ·
            refine ⟨23596222530352713620328371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15730815020235142413552247 23596222530352713620328371)
            ·
              refine ⟨35394333795529070430492557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23596222530352713620328371 35394333795529070430492557)
              ·
                refine ⟨13272875173323401411434709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35394333795529070430492557 13272875173323401411434709)
                ·
                  refine ⟨311083011874767220580501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13272875173323401411434709 311083011874767220580501)
                  ·
                    rfl

theorem cell20_681561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_681561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681561 prefixEnd_681561 := by exact prefixLift 681561
  have htrace : WordTrace (prefixWord ++ tailWord_681561) baseStart_681561 baseEnd_681561 := by
    simpa [prefixWord, tailWord_681561, baseEnd_681561] using wordTrace_append hprefix tailTrace_681561
  have hstable : (prefixWord ++ tailWord_681561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681561).length < 2 ^ (prefixWord ++ tailWord_681561).sum := by decide
  have hdescent : baseEnd_681561 < baseStart_681561 := by decide
  rcases family_descends (prefixWord ++ tailWord_681561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681633 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_681633 : Nat := 118140960795 + 681633 * 2 ^ 59
def prefixEnd_681633 : Nat := 4983230072969 + 3 ^ 40 * 681633 * 2
def baseEnd_681633 : Nat := 311115874636654970180207

theorem tailTrace_681633 : CollatzResearch.WordTrace tailWord_681633 prefixEnd_681633 311115874636654970180207 := by
  unfold tailWord_681633
  simp only [CollatzResearch.WordTrace]
  refine ⟨24861197939567529493345553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16574131959711686328897035 24861197939567529493345553)
  ·
    refine ⟨18645898454675647120009165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24861197939567529493345553 18645898454675647120009165)
    ·
      refine ⟨6992211920503367670003437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18645898454675647120009165 6992211920503367670003437)
      ·
        refine ⟨2622079470188762876251289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6992211920503367670003437 2622079470188762876251289)
        ·
          refine ⟨1966559602641572157188467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2622079470188762876251289 1966559602641572157188467)
          ·
            refine ⟨2949839403962358235782701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966559602641572157188467 2949839403962358235782701)
            ·
              refine ⟨1106189776485884338418513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2949839403962358235782701 1106189776485884338418513)
              ·
                refine ⟨829642332364413253813885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106189776485884338418513 829642332364413253813885)
                ·
                  refine ⟨311115874636654970180207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829642332364413253813885 311115874636654970180207)
                  ·
                    rfl

theorem cell20_681633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_681633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681633 prefixEnd_681633 := by exact prefixLift 681633
  have htrace : WordTrace (prefixWord ++ tailWord_681633) baseStart_681633 baseEnd_681633 := by
    simpa [prefixWord, tailWord_681633, baseEnd_681633] using wordTrace_append hprefix tailTrace_681633
  have hstable : (prefixWord ++ tailWord_681633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681633).length < 2 ^ (prefixWord ++ tailWord_681633).sum := by decide
  have hdescent : baseEnd_681633 < baseStart_681633 := by decide
  rcases family_descends (prefixWord ++ tailWord_681633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681661 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_681661 : Nat := 118140960795 + 681661 * 2 ^ 59
def prefixEnd_681661 : Nat := 4983230072969 + 3 ^ 40 * 681661 * 2
def baseEnd_681661 : Nat := 311128654599611317246759

theorem tailTrace_681661 : CollatzResearch.WordTrace tailWord_681661 prefixEnd_681661 311128654599611317246759 := by
  unfold tailWord_681661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24862219183466090275364837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16574812788977393516909891 24862219183466090275364837)
  ·
    refine ⟨4661666096899891926630907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24862219183466090275364837 4661666096899891926630907)
    ·
      refine ⟨6992499145349837889946361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661666096899891926630907 6992499145349837889946361)
      ·
        refine ⟨5244374359012378417459771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6992499145349837889946361 5244374359012378417459771)
        ·
          refine ⟨7866561538518567626189657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244374359012378417459771 7866561538518567626189657)
          ·
            refine ⟨5899921153888925719642243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7866561538518567626189657 5899921153888925719642243)
            ·
              refine ⟨8849881730833388579463365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899921153888925719642243 8849881730833388579463365)
              ·
                refine ⟨1659352824531260358649381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8849881730833388579463365 1659352824531260358649381)
                ·
                  refine ⟨311128654599611317246759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659352824531260358649381 311128654599611317246759)
                  ·
                    rfl

theorem cell20_681661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_681661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681661 prefixEnd_681661 := by exact prefixLift 681661
  have htrace : WordTrace (prefixWord ++ tailWord_681661) baseStart_681661 baseEnd_681661 := by
    simpa [prefixWord, tailWord_681661, baseEnd_681661] using wordTrace_append hprefix tailTrace_681661
  have hstable : (prefixWord ++ tailWord_681661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681661).length < 2 ^ (prefixWord ++ tailWord_681661).sum := by decide
  have hdescent : baseEnd_681661 < baseStart_681661 := by decide
  rcases family_descends (prefixWord ++ tailWord_681661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681670 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_681670 : Nat := 118140960795 + 681670 * 2 ^ 59
def prefixEnd_681670 : Nat := 4983230072969 + 3 ^ 40 * 681670 * 2
def baseEnd_681670 : Nat := 311132762444847285946723

theorem tailTrace_681670 : CollatzResearch.WordTrace tailWord_681670 prefixEnd_681670 311132762444847285946723 := by
  unfold tailWord_681670
  simp only [CollatzResearch.WordTrace]
  refine ⟨776954607513546400388827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16575031626955656541628309 776954607513546400388827)
  ·
    refine ⟨1165431911270319600583241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776954607513546400388827 1165431911270319600583241)
    ·
      refine ⟨874073933452739700437431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165431911270319600583241 874073933452739700437431)
      ·
        refine ⟨1311110900179109550656147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874073933452739700437431 1311110900179109550656147)
        ·
          refine ⟨1966666350268664325984221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311110900179109550656147 1966666350268664325984221)
          ·
            refine ⟨737499881350749122244083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1966666350268664325984221 737499881350749122244083)
            ·
              refine ⟨1106249822026123683366125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737499881350749122244083 1106249822026123683366125)
              ·
                refine ⟨414843683259796381262297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1106249822026123683366125 414843683259796381262297)
                ·
                  refine ⟨311132762444847285946723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414843683259796381262297 311132762444847285946723)
                  ·
                    rfl

theorem cell20_681670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_681670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681670 prefixEnd_681670 := by exact prefixLift 681670
  have htrace : WordTrace (prefixWord ++ tailWord_681670) baseStart_681670 baseEnd_681670 := by
    simpa [prefixWord, tailWord_681670, baseEnd_681670] using wordTrace_append hprefix tailTrace_681670
  have hstable : (prefixWord ++ tailWord_681670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681670).length < 2 ^ (prefixWord ++ tailWord_681670).sum := by decide
  have hdescent : baseEnd_681670 < baseStart_681670 := by decide
  rcases family_descends (prefixWord ++ tailWord_681670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681674 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_681674 : Nat := 118140960795 + 681674 * 2 ^ 59
def prefixEnd_681674 : Nat := 4983230072969 + 3 ^ 40 * 681674 * 2
def baseEnd_681674 : Nat := 311134588153841049813373

theorem tailTrace_681674 : CollatzResearch.WordTrace tailWord_681674 prefixEnd_681674 311134588153841049813373 := by
  unfold tailWord_681674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215673333104748373897019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16575128888279328997058717 6215673333104748373897019)
  ·
    refine ⟨9323509999657122560845529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215673333104748373897019 9323509999657122560845529)
    ·
      refine ⟨6992632499742841920634147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9323509999657122560845529 6992632499742841920634147)
      ·
        refine ⟨10488948749614262880951221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992632499742841920634147 10488948749614262880951221)
        ·
          refine ⟨983338945276337145089177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10488948749614262880951221 983338945276337145089177)
          ·
            refine ⟨737504208957252858816883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983338945276337145089177 737504208957252858816883)
            ·
              refine ⟨1106256313435879288225325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737504208957252858816883 1106256313435879288225325)
              ·
                refine ⟨414846117538454733084497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1106256313435879288225325 414846117538454733084497)
                ·
                  refine ⟨311134588153841049813373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414846117538454733084497 311134588153841049813373)
                  ·
                    rfl

theorem cell20_681674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_681674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681674 prefixEnd_681674 := by exact prefixLift 681674
  have htrace : WordTrace (prefixWord ++ tailWord_681674) baseStart_681674 baseEnd_681674 := by
    simpa [prefixWord, tailWord_681674, baseEnd_681674] using wordTrace_append hprefix tailTrace_681674
  have hstable : (prefixWord ++ tailWord_681674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681674).length < 2 ^ (prefixWord ++ tailWord_681674).sum := by decide
  have hdescent : baseEnd_681674 < baseStart_681674 := by decide
  rcases family_descends (prefixWord ++ tailWord_681674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681695 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 2]
def baseStart_681695 : Nat := 118140960795 + 681695 * 2 ^ 59
def prefixEnd_681695 : Nat := 4983230072969 + 3 ^ 40 * 681695 * 2
def baseEnd_681695 : Nat := 311144173126058310113287

theorem tailTrace_681695 : CollatzResearch.WordTrace tailWord_681695 prefixEnd_681695 311144173126058310113287 := by
  unfold tailWord_681695
  simp only [CollatzResearch.WordTrace]
  refine ⟨24863459265342914082102539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16575639510228609388068359 24863459265342914082102539)
  ·
    refine ⟨37295188898014371123153809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24863459265342914082102539 37295188898014371123153809)
    ·
      refine ⟨27971391673510778342365357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37295188898014371123153809 27971391673510778342365357)
      ·
        refine ⟨10489271877566541878387009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27971391673510778342365357 10489271877566541878387009)
        ·
          refine ⟨7866953908174906408790257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10489271877566541878387009 7866953908174906408790257)
          ·
            refine ⟨5900215431131179806592693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7866953908174906408790257 5900215431131179806592693)
            ·
              refine ⟨553145196668548106868065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5900215431131179806592693 553145196668548106868065)
              ·
                refine ⟨414858897501411080151049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553145196668548106868065 414858897501411080151049)
                ·
                  refine ⟨311144173126058310113287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414858897501411080151049 311144173126058310113287)
                  ·
                    rfl

theorem cell20_681695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2].length) (baseStart_681695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681695 prefixEnd_681695 := by exact prefixLift 681695
  have htrace : WordTrace (prefixWord ++ tailWord_681695) baseStart_681695 baseEnd_681695 := by
    simpa [prefixWord, tailWord_681695, baseEnd_681695] using wordTrace_append hprefix tailTrace_681695
  have hstable : (prefixWord ++ tailWord_681695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681695).length < 2 ^ (prefixWord ++ tailWord_681695).sum := by decide
  have hdescent : baseEnd_681695 < baseStart_681695 := by decide
  rcases family_descends (prefixWord ++ tailWord_681695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681706 : List Nat := [3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_681706 : Nat := 118140960795 + 681706 * 2 ^ 59
def prefixEnd_681706 : Nat := 4983230072969 + 3 ^ 40 * 681706 * 2
def baseEnd_681706 : Nat := 103716397941930386915525

theorem tailTrace_681706 : CollatzResearch.WordTrace tailWord_681706 prefixEnd_681706 103716397941930386915525 := by
  unfold tailWord_681706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215965117075765740188243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16575906978868708640501981 6215965117075765740188243)
  ·
    refine ⟨9323947675613648610282365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215965117075765740188243 9323947675613648610282365)
    ·
      refine ⟨3496480378355118228855887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9323947675613648610282365 3496480378355118228855887)
      ·
        refine ⟨5244720567532677343283831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3496480378355118228855887 5244720567532677343283831)
        ·
          refine ⟨7867080851299016014925747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244720567532677343283831 7867080851299016014925747)
          ·
            refine ⟨11800621276948524022388621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867080851299016014925747 11800621276948524022388621)
            ·
              refine ⟨4425232978855696508395733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11800621276948524022388621 4425232978855696508395733)
              ·
                refine ⟨103716397941930386915525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4425232978855696508395733 103716397941930386915525)
                ·
                  rfl

theorem cell20_681706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_681706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681706 prefixEnd_681706 := by exact prefixLift 681706
  have htrace : WordTrace (prefixWord ++ tailWord_681706) baseStart_681706 baseEnd_681706 := by
    simpa [prefixWord, tailWord_681706, baseEnd_681706] using wordTrace_append hprefix tailTrace_681706
  have hstable : (prefixWord ++ tailWord_681706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681706).length < 2 ^ (prefixWord ++ tailWord_681706).sum := by decide
  have hdescent : baseEnd_681706 < baseStart_681706 := by decide
  rcases family_descends (prefixWord ++ tailWord_681706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681709 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_681709 : Nat := 118140960795 + 681709 * 2 ^ 59
def prefixEnd_681709 : Nat := 4983230072969 + 3 ^ 40 * 681709 * 2
def baseEnd_681709 : Nat := 311150563107536483646563

theorem tailTrace_681709 : CollatzResearch.WordTrace tailWord_681709 prefixEnd_681709 311150563107536483646563 := by
  unfold tailWord_681709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24863969887292194473112181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16575979924861462982074787 24863969887292194473112181)
  ·
    refine ⟨2330997176933643231854267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24863969887292194473112181 2330997176933643231854267)
    ·
      refine ⟨3496495765400464847781401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330997176933643231854267 3496495765400464847781401)
      ·
        refine ⟨2622371824050348635836051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496495765400464847781401 2622371824050348635836051)
        ·
          refine ⟨3933557736075522953754077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622371824050348635836051 3933557736075522953754077)
          ·
            refine ⟨1475084151028321107657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3933557736075522953754077 1475084151028321107657779)
            ·
              refine ⟨2212626226542481661486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475084151028321107657779 2212626226542481661486669)
              ·
                refine ⟨829734834953430623057501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2212626226542481661486669 829734834953430623057501)
                ·
                  refine ⟨311150563107536483646563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829734834953430623057501 311150563107536483646563)
                  ·
                    rfl

theorem cell20_681709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_681709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681709 prefixEnd_681709 := by exact prefixLift 681709
  have htrace : WordTrace (prefixWord ++ tailWord_681709) baseStart_681709 baseEnd_681709 := by
    simpa [prefixWord, tailWord_681709, baseEnd_681709] using wordTrace_append hprefix tailTrace_681709
  have hstable : (prefixWord ++ tailWord_681709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681709).length < 2 ^ (prefixWord ++ tailWord_681709).sum := by decide
  have hdescent : baseEnd_681709 < baseStart_681709 := by decide
  rcases family_descends (prefixWord ++ tailWord_681709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681761 : List Nat := [1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_681761 : Nat := 118140960795 + 681761 * 2 ^ 59
def prefixEnd_681761 : Nat := 4983230072969 + 3 ^ 40 * 681761 * 2
def baseEnd_681761 : Nat := 103724765774818471304339

theorem tailTrace_681761 : CollatzResearch.WordTrace tailWord_681761 prefixEnd_681761 103724765774818471304339 := by
  unfold tailWord_681761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865866483103807354005137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16577244322069204902670091 24865866483103807354005137)
  ·
    refine ⟨18649399862327855515503853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24865866483103807354005137 18649399862327855515503853)
    ·
      refine ⟨6993524948372945818313945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18649399862327855515503853 6993524948372945818313945)
      ·
        refine ⟨5245143711279709363735459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6993524948372945818313945 5245143711279709363735459)
        ·
          refine ⟨7867715566919564045603189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245143711279709363735459 7867715566919564045603189)
          ·
            refine ⟨737598334398709129275299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7867715566919564045603189 737598334398709129275299)
            ·
              refine ⟨1106397501598063693912949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737598334398709129275299 1106397501598063693912949)
              ·
                refine ⟨103724765774818471304339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1106397501598063693912949 103724765774818471304339)
                ·
                  rfl

theorem cell20_681761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_681761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681761 prefixEnd_681761 := by exact prefixLift 681761
  have htrace : WordTrace (prefixWord ++ tailWord_681761) baseStart_681761 baseEnd_681761 := by
    simpa [prefixWord, tailWord_681761, baseEnd_681761] using wordTrace_append hprefix tailTrace_681761
  have hstable : (prefixWord ++ tailWord_681761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681761).length < 2 ^ (prefixWord ++ tailWord_681761).sum := by decide
  have hdescent : baseEnd_681761 < baseStart_681761 := by decide
  rcases family_descends (prefixWord ++ tailWord_681761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681813 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_681813 : Nat := 118140960795 + 681813 * 2 ^ 59
def prefixEnd_681813 : Nat := 4983230072969 + 3 ^ 40 * 681813 * 2
def baseEnd_681813 : Nat := 311198031541374344179471

theorem tailTrace_681813 : CollatzResearch.WordTrace tailWord_681813 prefixEnd_681813 311198031541374344179471 := by
  unfold tailWord_681813
  simp only [CollatzResearch.WordTrace]
  refine ⟨24867763078915420234898093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16578508719276946823265395 24867763078915420234898093)
  ·
    refine ⟨9325411154593282588086785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24867763078915420234898093 9325411154593282588086785)
    ·
      refine ⟨6994058365944961941065089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9325411154593282588086785 6994058365944961941065089)
      ·
        refine ⟨5245543774458721455798817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6994058365944961941065089 5245543774458721455798817)
        ·
          refine ⟨3934157830844041091849113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5245543774458721455798817 3934157830844041091849113)
          ·
            refine ⟨2950618373133030818886835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3934157830844041091849113 2950618373133030818886835)
            ·
              refine ⟨4425927559699546228330253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950618373133030818886835 4425927559699546228330253)
              ·
                refine ⟨1659722834887329835623845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4425927559699546228330253 1659722834887329835623845)
                ·
                  refine ⟨311198031541374344179471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1659722834887329835623845 311198031541374344179471)
                  ·
                    rfl

theorem cell20_681813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_681813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681813 prefixEnd_681813 := by exact prefixLift 681813
  have htrace : WordTrace (prefixWord ++ tailWord_681813) baseStart_681813 baseEnd_681813 := by
    simpa [prefixWord, tailWord_681813, baseEnd_681813] using wordTrace_append hprefix tailTrace_681813
  have hstable : (prefixWord ++ tailWord_681813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681813).length < 2 ^ (prefixWord ++ tailWord_681813).sum := by decide
  have hdescent : baseEnd_681813 < baseStart_681813 := by decide
  rcases family_descends (prefixWord ++ tailWord_681813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681823 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_681823 : Nat := 118140960795 + 681823 * 2 ^ 59
def prefixEnd_681823 : Nat := 4983230072969 + 3 ^ 40 * 681823 * 2
def baseEnd_681823 : Nat := 311202595813858753846097

theorem tailTrace_681823 : CollatzResearch.WordTrace tailWord_681823 prefixEnd_681823 311202595813858753846097 := by
  unfold tailWord_681823
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868127808879191942762123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16578751872586127961841415 24868127808879191942762123)
  ·
    refine ⟨37302191713318787914143185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24868127808879191942762123 37302191713318787914143185)
    ·
      refine ⟨27976643784989090935607389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37302191713318787914143185 27976643784989090935607389)
      ·
        refine ⟨10491241419370909100852771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27976643784989090935607389 10491241419370909100852771)
        ·
          refine ⟨15736862129056363651279157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10491241419370909100852771 15736862129056363651279157)
          ·
            refine ⟨1475330824599034092307421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15736862129056363651279157 1475330824599034092307421)
            ·
              refine ⟨553249059224637784615283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475330824599034092307421 553249059224637784615283)
              ·
                refine ⟨829873588836956676922925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553249059224637784615283 829873588836956676922925)
                ·
                  refine ⟨311202595813858753846097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829873588836956676922925 311202595813858753846097)
                  ·
                    rfl

theorem cell20_681823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_681823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681823 prefixEnd_681823 := by exact prefixLift 681823
  have htrace : WordTrace (prefixWord ++ tailWord_681823) baseStart_681823 baseEnd_681823 := by
    simpa [prefixWord, tailWord_681823, baseEnd_681823] using wordTrace_append hprefix tailTrace_681823
  have hstable : (prefixWord ++ tailWord_681823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681823).length < 2 ^ (prefixWord ++ tailWord_681823).sum := by decide
  have hdescent : baseEnd_681823 < baseStart_681823 := by decide
  rcases family_descends (prefixWord ++ tailWord_681823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681837 : List Nat := [1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_681837 : Nat := 118140960795 + 681837 * 2 ^ 59
def prefixEnd_681837 : Nat := 4983230072969 + 3 ^ 40 * 681837 * 2
def baseEnd_681837 : Nat := 103736328598445642459791

theorem tailTrace_681837 : CollatzResearch.WordTrace tailWord_681837 prefixEnd_681837 103736328598445642459791 := by
  unfold tailWord_681837
  simp only [CollatzResearch.WordTrace]
  refine ⟨24868638430828472333771765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16579092287218981555847843 24868638430828472333771765)
  ·
    refine ⟨2331434852890169281291103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24868638430828472333771765 2331434852890169281291103)
    ·
      refine ⟨3497152279335253921936655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2331434852890169281291103 3497152279335253921936655)
      ·
        refine ⟨5245728419002880882904983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3497152279335253921936655 5245728419002880882904983)
        ·
          refine ⟨7868592628504321324357475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245728419002880882904983 7868592628504321324357475)
          ·
            refine ⟨11802888942756481986536213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868592628504321324357475 11802888942756481986536213)
            ·
              refine ⟨553260419191710093118885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11802888942756481986536213 553260419191710093118885)
              ·
                refine ⟨103736328598445642459791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553260419191710093118885 103736328598445642459791)
                ·
                  rfl

theorem cell20_681837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_681837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681837 prefixEnd_681837 := by exact prefixLift 681837
  have htrace : WordTrace (prefixWord ++ tailWord_681837) baseStart_681837 baseEnd_681837 := by
    simpa [prefixWord, tailWord_681837, baseEnd_681837] using wordTrace_append hprefix tailTrace_681837
  have hstable : (prefixWord ++ tailWord_681837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681837).length < 2 ^ (prefixWord ++ tailWord_681837).sum := by decide
  have hdescent : baseEnd_681837 < baseStart_681837 := by decide
  rcases family_descends (prefixWord ++ tailWord_681837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681854 : List Nat := [4, 2, 3, 1, 1, 3, 6]
def baseStart_681854 : Nat := 118140960795 + 681854 * 2 ^ 59
def prefixEnd_681854 : Nat := 4983230072969 + 3 ^ 40 * 681854 * 2
def baseEnd_681854 : Nat := 34579638339840047090293

theorem tailTrace_681854 : CollatzResearch.WordTrace tailWord_681854 prefixEnd_681854 34579638339840047090293 := by
  unfold tailWord_681854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108657308970860529642577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16579505647844589491427077 3108657308970860529642577)
  ·
    refine ⟨2331492981728145397231933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3108657308970860529642577 2331492981728145397231933)
    ·
      refine ⟨874309868148054523961975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2331492981728145397231933 874309868148054523961975)
      ·
        refine ⟨1311464802222081785942963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874309868148054523961975 1311464802222081785942963)
        ·
          refine ⟨1967197203333122678914445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311464802222081785942963 1967197203333122678914445)
          ·
            refine ⟨737698951249921004592917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1967197203333122678914445 737698951249921004592917)
            ·
              refine ⟨34579638339840047090293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 737698951249921004592917 34579638339840047090293)
              ·
                rfl

theorem cell20_681854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_681854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681854 prefixEnd_681854 := by exact prefixLift 681854
  have htrace : WordTrace (prefixWord ++ tailWord_681854) baseStart_681854 baseEnd_681854 := by
    simpa [prefixWord, tailWord_681854, baseEnd_681854] using wordTrace_append hprefix tailTrace_681854
  have hstable : (prefixWord ++ tailWord_681854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681854).length < 2 ^ (prefixWord ++ tailWord_681854).sum := by decide
  have hdescent : baseEnd_681854 < baseStart_681854 := by decide
  rcases family_descends (prefixWord ++ tailWord_681854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681864 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_681864 : Nat := 118140960795 + 681864 * 2 ^ 59
def prefixEnd_681864 : Nat := 4983230072969 + 3 ^ 40 * 681864 * 2
def baseEnd_681864 : Nat := 311221309331044833479263

theorem tailTrace_681864 : CollatzResearch.WordTrace tailWord_681864 prefixEnd_681864 311221309331044833479263 := by
  unfold tailWord_681864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12434811600865327972502323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16579748801153770630003097 12434811600865327972502323)
  ·
    refine ⟨18652217401297991958753485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12434811600865327972502323 18652217401297991958753485)
    ·
      refine ⟨6994581525486746984532557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18652217401297991958753485 6994581525486746984532557)
      ·
        refine ⟨2622968072057530119199709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6994581525486746984532557 2622968072057530119199709)
        ·
          refine ⟨983613027021573794699891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622968072057530119199709 983613027021573794699891)
          ·
            refine ⟨1475419540532360692049837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983613027021573794699891 1475419540532360692049837)
            ·
              refine ⟨553282327699635259518689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475419540532360692049837 553282327699635259518689)
              ·
                refine ⟨414961745774726444639017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553282327699635259518689 414961745774726444639017)
                ·
                  refine ⟨311221309331044833479263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414961745774726444639017 311221309331044833479263)
                  ·
                    rfl

theorem cell20_681864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_681864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681864 prefixEnd_681864 := by exact prefixLift 681864
  have htrace : WordTrace (prefixWord ++ tailWord_681864) baseStart_681864 baseEnd_681864 := by
    simpa [prefixWord, tailWord_681864, baseEnd_681864] using wordTrace_append hprefix tailTrace_681864
  have hstable : (prefixWord ++ tailWord_681864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681864).length < 2 ^ (prefixWord ++ tailWord_681864).sum := by decide
  have hdescent : baseEnd_681864 < baseStart_681864 := by decide
  rcases family_descends (prefixWord ++ tailWord_681864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681865 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_681865 : Nat := 118140960795 + 681865 * 2 ^ 59
def prefixEnd_681865 : Nat := 4983230072969 + 3 ^ 40 * 681865 * 2
def baseEnd_681865 : Nat := 311221765758293274445925

theorem tailTrace_681865 : CollatzResearch.WordTrace tailWord_681865 prefixEnd_681865 311221765758293274445925 := by
  unfold tailWord_681865
  simp only [CollatzResearch.WordTrace]
  refine ⟨24869659674727033115791049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16579773116484688743860699 24869659674727033115791049)
  ·
    refine ⟨18652244756045274836843287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24869659674727033115791049 18652244756045274836843287)
    ·
      refine ⟨27978367134067912255264931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652244756045274836843287 27978367134067912255264931)
      ·
        refine ⟨41967550701101868382897397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27978367134067912255264931 41967550701101868382897397)
        ·
          refine ⟨3934457878228300160896631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41967550701101868382897397 3934457878228300160896631)
          ·
            refine ⟨5901686817342450241344947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934457878228300160896631 5901686817342450241344947)
            ·
              refine ⟨8852530226013675362017421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901686817342450241344947 8852530226013675362017421)
              ·
                refine ⟨3319698834755128260756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8852530226013675362017421 3319698834755128260756533)
                ·
                  refine ⟨311221765758293274445925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3319698834755128260756533 311221765758293274445925)
                  ·
                    rfl

theorem cell20_681865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_681865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681865 prefixEnd_681865 := by exact prefixLift 681865
  have htrace : WordTrace (prefixWord ++ tailWord_681865) baseStart_681865 baseEnd_681865 := by
    simpa [prefixWord, tailWord_681865, baseEnd_681865] using wordTrace_append hprefix tailTrace_681865
  have hstable : (prefixWord ++ tailWord_681865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681865).length < 2 ^ (prefixWord ++ tailWord_681865).sum := by decide
  have hdescent : baseEnd_681865 < baseStart_681865 := by decide
  rcases family_descends (prefixWord ++ tailWord_681865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681916 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_681916 : Nat := 118140960795 + 681916 * 2 ^ 59
def prefixEnd_681916 : Nat := 4983230072969 + 3 ^ 40 * 681916 * 2
def baseEnd_681916 : Nat := 311245043547963763745717

theorem tailTrace_681916 : CollatzResearch.WordTrace tailWord_681916 prefixEnd_681916 311245043547963763745717 := by
  unfold tailWord_681916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435759898771134412948801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16581013198361512550598401 12435759898771134412948801)
  ·
    refine ⟨9326819924078350809711601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12435759898771134412948801 9326819924078350809711601)
    ·
      refine ⟨6995114943058763107283701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9326819924078350809711601 6995114943058763107283701)
      ·
        refine ⟨655792025911759041307847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6995114943058763107283701 655792025911759041307847)
        ·
          refine ⟨983688038867638561961771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655792025911759041307847 983688038867638561961771)
          ·
            refine ⟨1475532058301457842942657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983688038867638561961771 1475532058301457842942657)
            ·
              refine ⟨1106649043726093382206993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475532058301457842942657 1106649043726093382206993)
              ·
                refine ⟨829986782794570036655245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106649043726093382206993 829986782794570036655245)
                ·
                  refine ⟨311245043547963763745717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829986782794570036655245 311245043547963763745717)
                  ·
                    rfl

theorem cell20_681916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_681916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681916 prefixEnd_681916 := by exact prefixLift 681916
  have htrace : WordTrace (prefixWord ++ tailWord_681916) baseStart_681916 baseEnd_681916 := by
    simpa [prefixWord, tailWord_681916, baseEnd_681916] using wordTrace_append hprefix tailTrace_681916
  have hstable : (prefixWord ++ tailWord_681916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681916).length < 2 ^ (prefixWord ++ tailWord_681916).sum := by decide
  have hdescent : baseEnd_681916 < baseStart_681916 := by decide
  rcases family_descends (prefixWord ++ tailWord_681916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681920 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_681920 : Nat := 118140960795 + 681920 * 2 ^ 59
def prefixEnd_681920 : Nat := 4983230072969 + 3 ^ 40 * 681920 * 2
def baseEnd_681920 : Nat := 311246869256957527612367

theorem tailTrace_681920 : CollatzResearch.WordTrace tailWord_681920 prefixEnd_681920 311246869256957527612367 := by
  unfold tailWord_681920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12435832844763888754521607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16581110459685185006028809 12435832844763888754521607)
  ·
    refine ⟨18653749267145833131782411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12435832844763888754521607 18653749267145833131782411)
    ·
      refine ⟨27980623900718749697673617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18653749267145833131782411 27980623900718749697673617)
      ·
        refine ⟨20985467925539062273255213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27980623900718749697673617 20985467925539062273255213)
        ·
          refine ⟨7869550472077148352470705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20985467925539062273255213 7869550472077148352470705)
          ·
            refine ⟨5902162854057861264353029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7869550472077148352470705 5902162854057861264353029)
            ·
              refine ⟨1106655535135848987066193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5902162854057861264353029 1106655535135848987066193)
              ·
                refine ⟨829991651351886740299645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106655535135848987066193 829991651351886740299645)
                ·
                  refine ⟨311246869256957527612367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829991651351886740299645 311246869256957527612367)
                  ·
                    rfl

theorem cell20_681920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_681920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681920 prefixEnd_681920 := by exact prefixLift 681920
  have htrace : WordTrace (prefixWord ++ tailWord_681920) baseStart_681920 baseEnd_681920 := by
    simpa [prefixWord, tailWord_681920, baseEnd_681920] using wordTrace_append hprefix tailTrace_681920
  have hstable : (prefixWord ++ tailWord_681920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681920).length < 2 ^ (prefixWord ++ tailWord_681920).sum := by decide
  have hdescent : baseEnd_681920 < baseStart_681920 := by decide
  rcases family_descends (prefixWord ++ tailWord_681920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681951 : List Nat := [1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_681951 : Nat := 118140960795 + 681951 * 2 ^ 59
def prefixEnd_681951 : Nat := 4983230072969 + 3 ^ 40 * 681951 * 2
def baseEnd_681951 : Nat := 103753672833886399192969

theorem tailTrace_681951 : CollatzResearch.WordTrace tailWord_681951 prefixEnd_681951 103753672833886399192969 := by
  unfold tailWord_681951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24872796352415469803421707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16581864234943646535614471 24872796352415469803421707)
  ·
    refine ⟨37309194528623204705132561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24872796352415469803421707 37309194528623204705132561)
    ·
      refine ⟨27981895896467403528849421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37309194528623204705132561 27981895896467403528849421)
      ·
        refine ⟨10493210961175276323318533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27981895896467403528849421 10493210961175276323318533)
        ·
          refine ⟨1967477055220364310622225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10493210961175276323318533 1967477055220364310622225)
          ·
            refine ⟨1475607791415273232966669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1967477055220364310622225 1475607791415273232966669)
            ·
              refine ⟨553352921780727462362501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475607791415273232966669 553352921780727462362501)
              ·
                refine ⟨103753672833886399192969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553352921780727462362501 103753672833886399192969)
                ·
                  rfl

theorem cell20_681951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_681951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681951 prefixEnd_681951 := by exact prefixLift 681951
  have htrace : WordTrace (prefixWord ++ tailWord_681951) baseStart_681951 baseEnd_681951 := by
    simpa [prefixWord, tailWord_681951, baseEnd_681951] using wordTrace_append hprefix tailTrace_681951
  have hstable : (prefixWord ++ tailWord_681951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681951).length < 2 ^ (prefixWord ++ tailWord_681951).sum := by decide
  have hdescent : baseEnd_681951 < baseStart_681951 := by decide
  rcases family_descends (prefixWord ++ tailWord_681951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_681982 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_681982 : Nat := 118140960795 + 681982 * 2 ^ 59
def prefixEnd_681982 : Nat := 4983230072969 + 3 ^ 40 * 681982 * 2
def baseEnd_681982 : Nat := 311275167746360867545447

theorem tailTrace_681982 : CollatzResearch.WordTrace tailWord_681982 prefixEnd_681982 311275167746360867545447 := by
  unfold tailWord_681982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109240876912895262225025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16582618010202108065200133 3109240876912895262225025)
  ·
    refine ⟨2331930657684671446668769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3109240876912895262225025 2331930657684671446668769)
    ·
      refine ⟨1748947993263503585001577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2331930657684671446668769 1748947993263503585001577)
      ·
        refine ⟨1311710994947627688751183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1748947993263503585001577 1311710994947627688751183)
        ·
          refine ⟨1967566492421441533126775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311710994947627688751183 1967566492421441533126775)
          ·
            refine ⟨2951349738632162299690163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967566492421441533126775 2951349738632162299690163)
            ·
              refine ⟨4427024607948243449535245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951349738632162299690163 4427024607948243449535245)
              ·
                refine ⟨1660134227980591293575717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4427024607948243449535245 1660134227980591293575717)
                ·
                  refine ⟨311275167746360867545447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660134227980591293575717 311275167746360867545447)
                  ·
                    rfl

theorem cell20_681982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_681982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_681982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_681982 prefixEnd_681982 := by exact prefixLift 681982
  have htrace : WordTrace (prefixWord ++ tailWord_681982) baseStart_681982 baseEnd_681982 := by
    simpa [prefixWord, tailWord_681982, baseEnd_681982] using wordTrace_append hprefix tailTrace_681982
  have hstable : (prefixWord ++ tailWord_681982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_681982).length < 2 ^ (prefixWord ++ tailWord_681982).sum := by decide
  have hdescent : baseEnd_681982 < baseStart_681982 := by decide
  rcases family_descends (prefixWord ++ tailWord_681982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682010 : List Nat := [3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_682010 : Nat := 118140960795 + 682010 * 2 ^ 59
def prefixEnd_682010 : Nat := 4983230072969 + 3 ^ 40 * 682010 * 2
def baseEnd_682010 : Nat := 103762649236439071537333

theorem tailTrace_682010 : CollatzResearch.WordTrace tailWord_682010 prefixEnd_682010 103762649236439071537333 := by
  unfold tailWord_682010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6218737064800430719954871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16583298839467815253212989 6218737064800430719954871)
  ·
    refine ⟨9328105597200646079932307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6218737064800430719954871 9328105597200646079932307)
    ·
      refine ⟨13992158395800969119898461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328105597200646079932307 13992158395800969119898461)
      ·
        refine ⟨5247059398425363419961923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13992158395800969119898461 5247059398425363419961923)
        ·
          refine ⟨7870589097638045129942885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5247059398425363419961923 7870589097638045129942885)
          ·
            refine ⟨1475735455807133461864291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7870589097638045129942885 1475735455807133461864291)
            ·
              refine ⟨2213603183710700192796437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475735455807133461864291 2213603183710700192796437)
              ·
                refine ⟨103762649236439071537333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2213603183710700192796437 103762649236439071537333)
                ·
                  rfl

theorem cell20_682010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_682010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682010 prefixEnd_682010 := by exact prefixLift 682010
  have htrace : WordTrace (prefixWord ++ tailWord_682010) baseStart_682010 baseEnd_682010 := by
    simpa [prefixWord, tailWord_682010, baseEnd_682010] using wordTrace_append hprefix tailTrace_682010
  have hstable : (prefixWord ++ tailWord_682010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682010).length < 2 ^ (prefixWord ++ tailWord_682010).sum := by decide
  have hdescent : baseEnd_682010 < baseStart_682010 := by decide
  rcases family_descends (prefixWord ++ tailWord_682010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682048 : List Nat := [2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_682048 : Nat := 118140960795 + 682048 * 2 ^ 59
def prefixEnd_682048 : Nat := 4983230072969 + 3 ^ 40 * 682048 * 2
def baseEnd_682048 : Nat := 103768430648252657115059

theorem tailTrace_682048 : CollatzResearch.WordTrace tailWord_682048 prefixEnd_682048 103768430648252657115059 := by
  unfold tailWord_682048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12438167116532027684851399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16584222822042703579801865 12438167116532027684851399)
  ·
    refine ⟨18657250674798041527277099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12438167116532027684851399 18657250674798041527277099)
    ·
      refine ⟨27985876012197062290915649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18657250674798041527277099 27985876012197062290915649)
      ·
        refine ⟨20989407009147796718186737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27985876012197062290915649 20989407009147796718186737)
        ·
          refine ⟨15742055256860847538640053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20989407009147796718186737 15742055256860847538640053)
          ·
            refine ⟨1475817680330704456747505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15742055256860847538640053 1475817680330704456747505)
            ·
              refine ⟨1106863260248028342560629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475817680330704456747505 1106863260248028342560629)
              ·
                refine ⟨103768430648252657115059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1106863260248028342560629 103768430648252657115059)
                ·
                  rfl

theorem cell20_682048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_682048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682048 prefixEnd_682048 := by exact prefixLift 682048
  have htrace : WordTrace (prefixWord ++ tailWord_682048) baseStart_682048 baseEnd_682048 := by
    simpa [prefixWord, tailWord_682048, baseEnd_682048] using wordTrace_append hprefix tailTrace_682048
  have hstable : (prefixWord ++ tailWord_682048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682048).length < 2 ^ (prefixWord ++ tailWord_682048).sum := by decide
  have hdescent : baseEnd_682048 < baseStart_682048 := by decide
  rcases family_descends (prefixWord ++ tailWord_682048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682096 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_682096 : Nat := 118140960795 + 682096 * 2 ^ 59
def prefixEnd_682096 : Nat := 4983230072969 + 3 ^ 40 * 682096 * 2
def baseEnd_682096 : Nat := 311327200452683137744981

theorem tailTrace_682096 : CollatzResearch.WordTrace tailWord_682096 prefixEnd_682096 311327200452683137744981 := by
  unfold tailWord_682096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439042468445079783725071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16585389957926773044966761 12439042468445079783725071)
  ·
    refine ⟨18658563702667619675587607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12439042468445079783725071 18658563702667619675587607)
    ·
      refine ⟨27987845554001429513381411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658563702667619675587607 27987845554001429513381411)
      ·
        refine ⟨41981768331002144270072117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27987845554001429513381411 41981768331002144270072117)
        ·
          refine ⟨3935790781031451025319261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41981768331002144270072117 3935790781031451025319261)
          ·
            refine ⟨1475921542886794134494723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3935790781031451025319261 1475921542886794134494723)
            ·
              refine ⟨2213882314330191201742085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475921542886794134494723 2213882314330191201742085)
              ·
                refine ⟨415102933936910850326641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2213882314330191201742085 415102933936910850326641)
                ·
                  refine ⟨311327200452683137744981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415102933936910850326641 311327200452683137744981)
                  ·
                    rfl

theorem cell20_682096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_682096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682096 prefixEnd_682096 := by exact prefixLift 682096
  have htrace : WordTrace (prefixWord ++ tailWord_682096) baseStart_682096 baseEnd_682096 := by
    simpa [prefixWord, tailWord_682096, baseEnd_682096] using wordTrace_append hprefix tailTrace_682096
  have hstable : (prefixWord ++ tailWord_682096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682096).length < 2 ^ (prefixWord ++ tailWord_682096).sum := by decide
  have hdescent : baseEnd_682096 < baseStart_682096 := by decide
  rcases family_descends (prefixWord ++ tailWord_682096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682117 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_682117 : Nat := 118140960795 + 682117 * 2 ^ 59
def prefixEnd_682117 : Nat := 4983230072969 + 3 ^ 40 * 682117 * 2
def baseEnd_682117 : Nat := 311336785424900398044895

theorem tailTrace_682117 : CollatzResearch.WordTrace tailWord_682117 prefixEnd_682117 311336785424900398044895 := by
  unfold tailWord_682117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24878850869814080153964605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16585900579876053435976403 24878850869814080153964605)
  ·
    refine ⟨9329569076180280057736727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24878850869814080153964605 9329569076180280057736727)
    ·
      refine ⟨13994353614270420086605091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9329569076180280057736727 13994353614270420086605091)
      ·
        refine ⟨20991530421405630129907637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13994353614270420086605091 20991530421405630129907637)
        ·
          refine ⟨1967955977006777824678841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20991530421405630129907637 1967955977006777824678841)
          ·
            refine ⟨1475966982755083368509131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1967955977006777824678841 1475966982755083368509131)
            ·
              refine ⟨2213950474132625052763697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475966982755083368509131 2213950474132625052763697)
              ·
                refine ⟨1660462855599468789572773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213950474132625052763697 1660462855599468789572773)
                ·
                  refine ⟨311336785424900398044895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660462855599468789572773 311336785424900398044895)
                  ·
                    rfl

theorem cell20_682117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_682117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682117 prefixEnd_682117 := by exact prefixLift 682117
  have htrace : WordTrace (prefixWord ++ tailWord_682117) baseStart_682117 baseEnd_682117 := by
    simpa [prefixWord, tailWord_682117, baseEnd_682117] using wordTrace_append hprefix tailTrace_682117
  have hstable : (prefixWord ++ tailWord_682117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682117).length < 2 ^ (prefixWord ++ tailWord_682117).sum := by decide
  have hdescent : baseEnd_682117 < baseStart_682117 := by decide
  rcases family_descends (prefixWord ++ tailWord_682117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682148 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_682148 : Nat := 118140960795 + 682148 * 2 ^ 59
def prefixEnd_682148 : Nat := 4983230072969 + 3 ^ 40 * 682148 * 2
def baseEnd_682148 : Nat := 311350934669602068011435

theorem tailTrace_682148 : CollatzResearch.WordTrace tailWord_682148 prefixEnd_682148 311350934669602068011435 := by
  unfold tailWord_682148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439990766350886224171549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16586654355134514965562065 12439990766350886224171549)
  ·
    refine ⟨4664996537381582334064331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12439990766350886224171549 4664996537381582334064331)
    ·
      refine ⟨6997494806072373501096497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664996537381582334064331 6997494806072373501096497)
      ·
        refine ⟨5248121104554280125822373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6997494806072373501096497 5248121104554280125822373)
        ·
          refine ⟨984022707103927523591695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5248121104554280125822373 984022707103927523591695)
          ·
            refine ⟨1476034060655891285387543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984022707103927523591695 1476034060655891285387543)
            ·
              refine ⟨2214051090983836928081315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476034060655891285387543 2214051090983836928081315)
              ·
                refine ⟨3321076636475755392121973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214051090983836928081315 3321076636475755392121973)
                ·
                  refine ⟨311350934669602068011435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321076636475755392121973 311350934669602068011435)
                  ·
                    rfl

theorem cell20_682148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_682148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682148 prefixEnd_682148 := by exact prefixLift 682148
  have htrace : WordTrace (prefixWord ++ tailWord_682148) baseStart_682148 baseEnd_682148 := by
    simpa [prefixWord, tailWord_682148, baseEnd_682148] using wordTrace_append hprefix tailTrace_682148
  have hstable : (prefixWord ++ tailWord_682148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682148).length < 2 ^ (prefixWord ++ tailWord_682148).sum := by decide
  have hdescent : baseEnd_682148 < baseStart_682148 := by decide
  rcases family_descends (prefixWord ++ tailWord_682148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682200 : List Nat := [2, 1, 2, 2, 4, 3, 6]
def baseStart_682200 : Nat := 118140960795 + 682200 * 2 ^ 59
def prefixEnd_682200 : Nat := 4983230072969 + 3 ^ 40 * 682200 * 2
def baseEnd_682200 : Nat := 34597185431835666475321

theorem tailTrace_682200 : CollatzResearch.WordTrace tailWord_682200 prefixEnd_682200 34597185431835666475321 := by
  unfold tailWord_682200
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440939064256692664618027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16587918752342256886157369 12440939064256692664618027)
  ·
    refine ⟨18661408596385038996927041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12440939064256692664618027 18661408596385038996927041)
    ·
      refine ⟨13996056447288779247695281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18661408596385038996927041 13996056447288779247695281)
      ·
        refine ⟨10497042335466584435771461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13996056447288779247695281 10497042335466584435771461)
        ·
          refine ⟨1968195437899984581707149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10497042335466584435771461 1968195437899984581707149)
          ·
            refine ⟨738073289212494218140181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1968195437899984581707149 738073289212494218140181)
            ·
              refine ⟨34597185431835666475321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 738073289212494218140181 34597185431835666475321)
              ·
                rfl

theorem cell20_682200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_682200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682200 prefixEnd_682200 := by exact prefixLift 682200
  have htrace : WordTrace (prefixWord ++ tailWord_682200) baseStart_682200 baseEnd_682200 := by
    simpa [prefixWord, tailWord_682200, baseEnd_682200] using wordTrace_append hprefix tailTrace_682200
  have hstable : (prefixWord ++ tailWord_682200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682200).length < 2 ^ (prefixWord ++ tailWord_682200).sum := by decide
  have hdescent : baseEnd_682200 < baseStart_682200 := by decide
  rcases family_descends (prefixWord ++ tailWord_682200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682207 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_682207 : Nat := 118140960795 + 682207 * 2 ^ 59
def prefixEnd_682207 : Nat := 4983230072969 + 3 ^ 40 * 682207 * 2
def baseEnd_682207 : Nat := 311377863877260085044527

theorem tailTrace_682207 : CollatzResearch.WordTrace tailWord_682207 prefixEnd_682207 311377863877260085044527 := by
  unfold tailWord_682207
  simp only [CollatzResearch.WordTrace]
  refine ⟨24882133439488025524740875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16588088959658683683160583 24882133439488025524740875)
  ·
    refine ⟨37323200159232038287111313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24882133439488025524740875 37323200159232038287111313)
    ·
      refine ⟨27992400119424028715333485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37323200159232038287111313 27992400119424028715333485)
      ·
        refine ⟨10497150044784010768250057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27992400119424028715333485 10497150044784010768250057)
        ·
          refine ⟨7872862533588008076187543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10497150044784010768250057 7872862533588008076187543)
          ·
            refine ⟨11809293800382012114281315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872862533588008076187543 11809293800382012114281315)
            ·
              refine ⟨17713940700573018171421973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11809293800382012114281315 17713940700573018171421973)
              ·
                refine ⟨830340970339360226785405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17713940700573018171421973 830340970339360226785405)
                ·
                  refine ⟨311377863877260085044527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830340970339360226785405 311377863877260085044527)
                  ·
                    rfl

theorem cell20_682207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_682207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682207 prefixEnd_682207 := by exact prefixLift 682207
  have htrace : WordTrace (prefixWord ++ tailWord_682207) baseStart_682207 baseEnd_682207 := by
    simpa [prefixWord, tailWord_682207, baseEnd_682207] using wordTrace_append hprefix tailTrace_682207
  have hstable : (prefixWord ++ tailWord_682207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682207).length < 2 ^ (prefixWord ++ tailWord_682207).sum := by decide
  have hdescent : baseEnd_682207 < baseStart_682207 := by decide
  rcases family_descends (prefixWord ++ tailWord_682207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682238 : List Nat := [4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_682238 : Nat := 118140960795 + 682238 * 2 ^ 59
def prefixEnd_682238 : Nat := 4983230072969 + 3 ^ 40 * 682238 * 2
def baseEnd_682238 : Nat := 103797337707320585003689

theorem tailTrace_682238 : CollatzResearch.WordTrace tailWord_682238 prefixEnd_682238 103797337707320585003689 := by
  unfold tailWord_682238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110408012796964727389921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16588842734917145212746245 3110408012796964727389921)
  ·
    refine ⟨2332806009597723545542441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3110408012796964727389921 2332806009597723545542441)
    ·
      refine ⟨1749604507198292659156831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2332806009597723545542441 1749604507198292659156831)
      ·
        refine ⟨2624406760797438988735247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749604507198292659156831 2624406760797438988735247)
        ·
          refine ⟨3936610141196158483102871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624406760797438988735247 3936610141196158483102871)
          ·
            refine ⟨5904915211794237724654307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936610141196158483102871 5904915211794237724654307)
            ·
              refine ⟨8857372817691356586981461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904915211794237724654307 8857372817691356586981461)
              ·
                refine ⟨103797337707320585003689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8857372817691356586981461 103797337707320585003689)
                ·
                  rfl

theorem cell20_682238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_682238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682238 prefixEnd_682238 := by exact prefixLift 682238
  have htrace : WordTrace (prefixWord ++ tailWord_682238) baseStart_682238 baseEnd_682238 := by
    simpa [prefixWord, tailWord_682238, baseEnd_682238] using wordTrace_append hprefix tailTrace_682238
  have hstable : (prefixWord ++ tailWord_682238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682238).length < 2 ^ (prefixWord ++ tailWord_682238).sum := by decide
  have hdescent : baseEnd_682238 < baseStart_682238 := by decide
  rcases family_descends (prefixWord ++ tailWord_682238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682276 : List Nat := [2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_682276 : Nat := 118140960795 + 682276 * 2 ^ 59
def prefixEnd_682276 : Nat := 4983230072969 + 3 ^ 40 * 682276 * 2
def baseEnd_682276 : Nat := 103803119119134170581415

theorem tailTrace_682276 : CollatzResearch.WordTrace tailWord_682276 prefixEnd_682276 103803119119134170581415 := by
  unfold tailWord_682276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442325038119025154501341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16589766717492033539335121 12442325038119025154501341)
  ·
    refine ⟨4665871889294634432938003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12442325038119025154501341 4665871889294634432938003)
    ·
      refine ⟨6998807833941951649407005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665871889294634432938003 6998807833941951649407005)
      ·
        refine ⟨2624552937728231868527627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6998807833941951649407005 2624552937728231868527627)
        ·
          refine ⟨3936829406592347802791441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624552937728231868527627 3936829406592347802791441)
          ·
            refine ⟨2952622054944260852093581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3936829406592347802791441 2952622054944260852093581)
            ·
              refine ⟨1107233270604097819535093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2952622054944260852093581 1107233270604097819535093)
              ·
                refine ⟨103803119119134170581415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107233270604097819535093 103803119119134170581415)
                ·
                  rfl

theorem cell20_682276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_682276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682276 prefixEnd_682276 := by exact prefixLift 682276
  have htrace : WordTrace (prefixWord ++ tailWord_682276) baseStart_682276 baseEnd_682276 := by
    simpa [prefixWord, tailWord_682276, baseEnd_682276] using wordTrace_append hprefix tailTrace_682276
  have hstable : (prefixWord ++ tailWord_682276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682276).length < 2 ^ (prefixWord ++ tailWord_682276).sum := by decide
  have hdescent : baseEnd_682276 < baseStart_682276 := by decide
  rcases family_descends (prefixWord ++ tailWord_682276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682307 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 2]
def baseStart_682307 : Nat := 118140960795 + 682307 * 2 ^ 59
def prefixEnd_682307 : Nat := 4983230072969 + 3 ^ 40 * 682307 * 2
def baseEnd_682307 : Nat := 311423506602104181710785

theorem tailTrace_682307 : CollatzResearch.WordTrace tailWord_682307 prefixEnd_682307 311423506602104181710785 := by
  unfold tailWord_682307
  simp only [CollatzResearch.WordTrace]
  refine ⟨24885780739125742603381175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16590520492750495068920783 24885780739125742603381175)
  ·
    refine ⟨37328671108688613905071763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24885780739125742603381175 37328671108688613905071763)
    ·
      refine ⟨55993006663032920857607645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37328671108688613905071763 55993006663032920857607645)
      ·
        refine ⟨20997377498637345321602867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55993006663032920857607645 20997377498637345321602867)
        ·
          refine ⟨31496066247956017982404301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20997377498637345321602867 31496066247956017982404301)
          ·
            refine ⟨11811024842983506743401613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31496066247956017982404301 11811024842983506743401613)
            ·
              refine ⟨4429134316118815028775605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11811024842983506743401613 4429134316118815028775605)
              ·
                refine ⟨415231342136138908947713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4429134316118815028775605 415231342136138908947713)
                ·
                  refine ⟨311423506602104181710785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415231342136138908947713 311423506602104181710785)
                  ·
                    rfl

theorem cell20_682307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 2].length) (baseStart_682307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682307 prefixEnd_682307 := by exact prefixLift 682307
  have htrace : WordTrace (prefixWord ++ tailWord_682307) baseStart_682307 baseEnd_682307 := by
    simpa [prefixWord, tailWord_682307, baseEnd_682307] using wordTrace_append hprefix tailTrace_682307
  have hstable : (prefixWord ++ tailWord_682307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682307).length < 2 ^ (prefixWord ++ tailWord_682307).sum := by decide
  have hdescent : baseEnd_682307 < baseStart_682307 := by decide
  rcases family_descends (prefixWord ++ tailWord_682307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682321 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_682321 : Nat := 118140960795 + 682321 * 2 ^ 59
def prefixEnd_682321 : Nat := 4983230072969 + 3 ^ 40 * 682321 * 2
def baseEnd_682321 : Nat := 311429896583582355244061

theorem tailTrace_682321 : CollatzResearch.WordTrace tailWord_682321 prefixEnd_682321 311429896583582355244061 := by
  unfold tailWord_682321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24886291361075022994390817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16590860907383348662927211 24886291361075022994390817)
  ·
    refine ⟨18664718520806267245793113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24886291361075022994390817 18664718520806267245793113)
    ·
      refine ⟨13998538890604700434344835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18664718520806267245793113 13998538890604700434344835)
      ·
        refine ⟨20997808335907050651517253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13998538890604700434344835 20997808335907050651517253)
        ·
          refine ⟨3937089062982571997159485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20997808335907050651517253 3937089062982571997159485)
          ·
            refine ⟨1476408398618464498934807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3937089062982571997159485 1476408398618464498934807)
            ·
              refine ⟨2214612597927696748402211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476408398618464498934807 2214612597927696748402211)
              ·
                refine ⟨3321918896891545122603317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2214612597927696748402211 3321918896891545122603317)
                ·
                  refine ⟨311429896583582355244061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321918896891545122603317 311429896583582355244061)
                  ·
                    rfl

theorem cell20_682321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_682321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682321 prefixEnd_682321 := by exact prefixLift 682321
  have htrace : WordTrace (prefixWord ++ tailWord_682321) baseStart_682321 baseEnd_682321 := by
    simpa [prefixWord, tailWord_682321, baseEnd_682321] using wordTrace_append hprefix tailTrace_682321
  have hstable : (prefixWord ++ tailWord_682321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682321).length < 2 ^ (prefixWord ++ tailWord_682321).sum := by decide
  have hdescent : baseEnd_682321 < baseStart_682321 := by decide
  rcases family_descends (prefixWord ++ tailWord_682321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682324 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_682324 : Nat := 118140960795 + 682324 * 2 ^ 59
def prefixEnd_682324 : Nat := 4983230072969 + 3 ^ 40 * 682324 * 2
def baseEnd_682324 : Nat := 311431265865327678144049

theorem tailTrace_682324 : CollatzResearch.WordTrace tailWord_682324 prefixEnd_682324 311431265865327678144049 := by
  unfold tailWord_682324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443200390032077253375013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16590933853376103004500017 12443200390032077253375013)
  ·
    refine ⟨2333100073131014485007815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12443200390032077253375013 2333100073131014485007815)
    ·
      refine ⟨3499650109696521727511723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333100073131014485007815 3499650109696521727511723)
      ·
        refine ⟨5249475164544782591267585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499650109696521727511723 5249475164544782591267585)
        ·
          refine ⟨3937106373408586943450689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5249475164544782591267585 3937106373408586943450689)
          ·
            refine ⟨2952829780056440207588017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3937106373408586943450689 2952829780056440207588017)
            ·
              refine ⟨2214622335042330155691013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952829780056440207588017 2214622335042330155691013)
              ·
                refine ⟨415241687820436904192065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2214622335042330155691013 415241687820436904192065)
                ·
                  refine ⟨311431265865327678144049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415241687820436904192065 311431265865327678144049)
                  ·
                    rfl

theorem cell20_682324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_682324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682324 prefixEnd_682324 := by exact prefixLift 682324
  have htrace : WordTrace (prefixWord ++ tailWord_682324) baseStart_682324 baseEnd_682324 := by
    simpa [prefixWord, tailWord_682324, baseEnd_682324] using wordTrace_append hprefix tailTrace_682324
  have hstable : (prefixWord ++ tailWord_682324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682324).length < 2 ^ (prefixWord ++ tailWord_682324).sum := by decide
  have hdescent : baseEnd_682324 < baseStart_682324 := by decide
  rcases family_descends (prefixWord ++ tailWord_682324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682348 : List Nat := [2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_682348 : Nat := 118140960795 + 682348 * 2 ^ 59
def prefixEnd_682348 : Nat := 4983230072969 + 3 ^ 40 * 682348 * 2
def baseEnd_682348 : Nat := 103814073373096753781317

theorem tailTrace_682348 : CollatzResearch.WordTrace tailWord_682348 prefixEnd_682348 103814073373096753781317 := by
  unfold tailWord_682348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443638065988603302811849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16591517421318137737082465 12443638065988603302811849)
  ·
    refine ⟨9332728549491452477108887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12443638065988603302811849 9332728549491452477108887)
    ·
      refine ⟨13999092824237178715663331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9332728549491452477108887 13999092824237178715663331)
      ·
        refine ⟨20998639236355768073494997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13999092824237178715663331 20998639236355768073494997)
        ·
          refine ⟨492155607102088314222539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 20998639236355768073494997 492155607102088314222539)
          ·
            refine ⟨738233410653132471333809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492155607102088314222539 738233410653132471333809)
            ·
              refine ⟨553675057989849353500357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738233410653132471333809 553675057989849353500357)
              ·
                refine ⟨103814073373096753781317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553675057989849353500357 103814073373096753781317)
                ·
                  rfl

theorem cell20_682348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_682348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682348 prefixEnd_682348 := by exact prefixLift 682348
  have htrace : WordTrace (prefixWord ++ tailWord_682348) baseStart_682348 baseEnd_682348 := by
    simpa [prefixWord, tailWord_682348, baseEnd_682348] using wordTrace_append hprefix tailTrace_682348
  have hstable : (prefixWord ++ tailWord_682348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682348).length < 2 ^ (prefixWord ++ tailWord_682348).sum := by decide
  have hdescent : baseEnd_682348 < baseStart_682348 := by decide
  rcases family_descends (prefixWord ++ tailWord_682348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682352 : List Nat := [2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_682352 : Nat := 118140960795 + 682352 * 2 ^ 59
def prefixEnd_682352 : Nat := 4983230072969 + 3 ^ 40 * 682352 * 2
def baseEnd_682352 : Nat := 103814681942761341736867

theorem tailTrace_682352 : CollatzResearch.WordTrace tailWord_682352 prefixEnd_682352 103814681942761341736867 := by
  unfold tailWord_682352
  simp only [CollatzResearch.WordTrace]
  refine ⟨12443711011981357644384655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16591614682641810192512873 12443711011981357644384655)
  ·
    refine ⟨18665566517972036466576983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12443711011981357644384655 18665566517972036466576983)
    ·
      refine ⟨27998349776958054699865475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18665566517972036466576983 27998349776958054699865475)
      ·
        refine ⟨41997524665437082049798213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27998349776958054699865475 41997524665437082049798213)
        ·
          refine ⟨7874535874769452884337165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41997524665437082049798213 7874535874769452884337165)
          ·
            refine ⟨2952950953038544831626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7874535874769452884337165 2952950953038544831626437)
            ·
              refine ⟨553678303694727155929957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2952950953038544831626437 553678303694727155929957)
              ·
                refine ⟨103814681942761341736867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 553678303694727155929957 103814681942761341736867)
                ·
                  rfl

theorem cell20_682352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_682352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682352 prefixEnd_682352 := by exact prefixLift 682352
  have htrace : WordTrace (prefixWord ++ tailWord_682352) baseStart_682352 baseEnd_682352 := by
    simpa [prefixWord, tailWord_682352, baseEnd_682352] using wordTrace_append hprefix tailTrace_682352
  have hstable : (prefixWord ++ tailWord_682352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682352).length < 2 ^ (prefixWord ++ tailWord_682352).sum := by decide
  have hdescent : baseEnd_682352 < baseStart_682352 := by decide
  rcases family_descends (prefixWord ++ tailWord_682352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682404 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_682404 : Nat := 118140960795 + 682404 * 2 ^ 59
def prefixEnd_682404 : Nat := 4983230072969 + 3 ^ 40 * 682404 * 2
def baseEnd_682404 : Nat := 311467780045202955477055

theorem tailTrace_682404 : CollatzResearch.WordTrace tailWord_682404 prefixEnd_682404 311467780045202955477055 := by
  unfold tailWord_682404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12444659309887164084831133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16592879079849552113108177 12444659309887164084831133)
  ·
    refine ⟨4666747241207686531811675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12444659309887164084831133 4666747241207686531811675)
    ·
      refine ⟨7000120861811529797717513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666747241207686531811675 7000120861811529797717513)
      ·
        refine ⟨5250090646358647348288135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7000120861811529797717513 5250090646358647348288135)
        ·
          refine ⟨7875135969537971022432203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250090646358647348288135 7875135969537971022432203)
          ·
            refine ⟨11812703954306956533648305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875135969537971022432203 11812703954306956533648305)
            ·
              refine ⟨8859527965730217400236229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11812703954306956533648305 8859527965730217400236229)
              ·
                refine ⟨1661161493574415762544293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8859527965730217400236229 1661161493574415762544293)
                ·
                  refine ⟨311467780045202955477055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661161493574415762544293 311467780045202955477055)
                  ·
                    rfl

theorem cell20_682404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_682404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682404 prefixEnd_682404 := by exact prefixLift 682404
  have htrace : WordTrace (prefixWord ++ tailWord_682404) baseStart_682404 baseEnd_682404 := by
    simpa [prefixWord, tailWord_682404, baseEnd_682404] using wordTrace_append hprefix tailTrace_682404
  have hstable : (prefixWord ++ tailWord_682404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682404).length < 2 ^ (prefixWord ++ tailWord_682404).sum := by decide
  have hdescent : baseEnd_682404 < baseStart_682404 := by decide
  rcases family_descends (prefixWord ++ tailWord_682404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682442 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_682442 : Nat := 118140960795 + 682442 * 2 ^ 59
def prefixEnd_682442 : Nat := 4983230072969 + 3 ^ 40 * 682442 * 2
def baseEnd_682442 : Nat := 311485124280643712210233

theorem tailTrace_682442 : CollatzResearch.WordTrace tailWord_682442 prefixEnd_682442 311485124280643712210233 := by
  unfold tailWord_682442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222676148409165164886395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16593803062424440439697053 6222676148409165164886395)
  ·
    refine ⟨9334014222613747747329593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222676148409165164886395 9334014222613747747329593)
    ·
      refine ⟨7000510666960310810497195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334014222613747747329593 7000510666960310810497195)
      ·
        refine ⟨10500766000440466215745793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000510666960310810497195 10500766000440466215745793)
        ·
          refine ⟨7875574500330349661809345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500766000440466215745793 7875574500330349661809345)
          ·
            refine ⟨5906680875247762246357009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7875574500330349661809345 5906680875247762246357009)
            ·
              refine ⟨4430010656435821684767757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906680875247762246357009 4430010656435821684767757)
              ·
                refine ⟨1661253996163433131787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4430010656435821684767757 1661253996163433131787909)
                ·
                  refine ⟨311485124280643712210233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661253996163433131787909 311485124280643712210233)
                  ·
                    rfl

theorem cell20_682442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_682442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682442 prefixEnd_682442 := by exact prefixLift 682442
  have htrace : WordTrace (prefixWord ++ tailWord_682442) baseStart_682442 baseEnd_682442 := by
    simpa [prefixWord, tailWord_682442, baseEnd_682442] using wordTrace_append hprefix tailTrace_682442
  have hstable : (prefixWord ++ tailWord_682442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682442).length < 2 ^ (prefixWord ++ tailWord_682442).sum := by decide
  have hdescent : baseEnd_682442 < baseStart_682442 := by decide
  rcases family_descends (prefixWord ++ tailWord_682442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682452 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_682452 : Nat := 118140960795 + 682452 * 2 ^ 59
def prefixEnd_682452 : Nat := 4983230072969 + 3 ^ 40 * 682452 * 2
def baseEnd_682452 : Nat := 311489688553128121876859

theorem tailTrace_682452 : CollatzResearch.WordTrace tailWord_682452 prefixEnd_682452 311489688553128121876859 := by
  unfold tailWord_682452
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445534661800216183704805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16594046215733621578273073 12445534661800216183704805)
  ·
    refine ⟨2333537749087540534444651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12445534661800216183704805 2333537749087540534444651)
    ·
      refine ⟨3500306623631310801666977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333537749087540534444651 3500306623631310801666977)
      ·
        refine ⟨2625229967723483101250233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3500306623631310801666977 2625229967723483101250233)
        ·
          refine ⟨1968922475792612325937675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625229967723483101250233 1968922475792612325937675)
          ·
            refine ⟨2953383713688918488906513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968922475792612325937675 2953383713688918488906513)
            ·
              refine ⟨2215037785266688866679885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953383713688918488906513 2215037785266688866679885)
              ·
                refine ⟨830639169475008325004957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2215037785266688866679885 830639169475008325004957)
                ·
                  refine ⟨311489688553128121876859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830639169475008325004957 311489688553128121876859)
                  ·
                    rfl

theorem cell20_682452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_682452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682452 prefixEnd_682452 := by exact prefixLift 682452
  have htrace : WordTrace (prefixWord ++ tailWord_682452) baseStart_682452 baseEnd_682452 := by
    simpa [prefixWord, tailWord_682452, baseEnd_682452] using wordTrace_append hprefix tailTrace_682452
  have hstable : (prefixWord ++ tailWord_682452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682452).length < 2 ^ (prefixWord ++ tailWord_682452).sum := by decide
  have hdescent : baseEnd_682452 < baseStart_682452 := by decide
  rcases family_descends (prefixWord ++ tailWord_682452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682456 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_682456 : Nat := 118140960795 + 682456 * 2 ^ 59
def prefixEnd_682456 : Nat := 4983230072969 + 3 ^ 40 * 682456 * 2
def baseEnd_682456 : Nat := 311491514262121885743509

theorem tailTrace_682456 : CollatzResearch.WordTrace tailWord_682456 prefixEnd_682456 311491514262121885743509 := by
  unfold tailWord_682456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445607607792970525277611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16594143477057294033703481 12445607607792970525277611)
  ·
    refine ⟨18668411411689455787916417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12445607607792970525277611 18668411411689455787916417)
    ·
      refine ⟨14001308558767091840937313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18668411411689455787916417 14001308558767091840937313)
      ·
        refine ⟨10500981419075318880702985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001308558767091840937313 10500981419075318880702985)
        ·
          refine ⟨7875736064306489160527239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500981419075318880702985 7875736064306489160527239)
          ·
            refine ⟨11813604096459733740790859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875736064306489160527239 11813604096459733740790859)
            ·
              refine ⟨17720406144689600611186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11813604096459733740790859 17720406144689600611186289)
              ·
                refine ⟨13290304608517200458389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17720406144689600611186289 13290304608517200458389717)
                ·
                  refine ⟨311491514262121885743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13290304608517200458389717 311491514262121885743509)
                  ·
                    rfl

theorem cell20_682456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_682456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682456 prefixEnd_682456 := by exact prefixLift 682456
  have htrace : WordTrace (prefixWord ++ tailWord_682456) baseStart_682456 baseEnd_682456 := by
    simpa [prefixWord, tailWord_682456, baseEnd_682456] using wordTrace_append hprefix tailTrace_682456
  have hstable : (prefixWord ++ tailWord_682456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682456).length < 2 ^ (prefixWord ++ tailWord_682456).sum := by decide
  have hdescent : baseEnd_682456 < baseStart_682456 := by decide
  rcases family_descends (prefixWord ++ tailWord_682456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682497 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_682497 : Nat := 118140960795 + 682497 * 2 ^ 59
def prefixEnd_682497 : Nat := 4983230072969 + 3 ^ 40 * 682497 * 2
def baseEnd_682497 : Nat := 311510227779307965376675

theorem tailTrace_682497 : CollatzResearch.WordTrace tailWord_682497 prefixEnd_682497 311510227779307965376675 := by
  unfold tailWord_682497
  simp only [CollatzResearch.WordTrace]
  refine ⟨24892710608437405052797745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16595140405624936701865163 24892710608437405052797745)
  ·
    refine ⟨18669532956328053789598309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24892710608437405052797745 18669532956328053789598309)
    ·
      refine ⟨3500537429311510085549683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18669532956328053789598309 3500537429311510085549683)
      ·
        refine ⟨5250806143967265128324525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500537429311510085549683 5250806143967265128324525)
        ·
          refine ⟨1969052303987724423121697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5250806143967265128324525 1969052303987724423121697)
          ·
            refine ⟨1476789227990793317341273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969052303987724423121697 1476789227990793317341273)
            ·
              refine ⟨1107591920993094988005955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476789227990793317341273 1107591920993094988005955)
              ·
                refine ⟨1661387881489642482008933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107591920993094988005955 1661387881489642482008933)
                ·
                  refine ⟨311510227779307965376675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661387881489642482008933 311510227779307965376675)
                  ·
                    rfl

theorem cell20_682497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_682497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682497 prefixEnd_682497 := by exact prefixLift 682497
  have htrace : WordTrace (prefixWord ++ tailWord_682497) baseStart_682497 baseEnd_682497 := by
    simpa [prefixWord, tailWord_682497, baseEnd_682497] using wordTrace_append hprefix tailTrace_682497
  have hstable : (prefixWord ++ tailWord_682497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682497).length < 2 ^ (prefixWord ++ tailWord_682497).sum := by decide
  have hdescent : baseEnd_682497 < baseStart_682497 := by decide
  rcases family_descends (prefixWord ++ tailWord_682497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682539 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_682539 : Nat := 118140960795 + 682539 * 2 ^ 59
def prefixEnd_682539 : Nat := 4983230072969 + 3 ^ 40 * 682539 * 2
def baseEnd_682539 : Nat := 311529397723742485976503

theorem tailTrace_682539 : CollatzResearch.WordTrace tailWord_682539 prefixEnd_682539 311529397723742485976503 := by
  unfold tailWord_682539
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894242474285246225826671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16596161649523497483884447 24894242474285246225826671)
  ·
    refine ⟨37341363711427869338740007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24894242474285246225826671 37341363711427869338740007)
    ·
      refine ⟨56012045567141804008110011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37341363711427869338740007 56012045567141804008110011)
      ·
        refine ⟨84018068350712706012165017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56012045567141804008110011 84018068350712706012165017)
        ·
          refine ⟨63013551263034529509123763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84018068350712706012165017 63013551263034529509123763)
          ·
            refine ⟨94520326894551794263685645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63013551263034529509123763 94520326894551794263685645)
            ·
              refine ⟨35445122585456922848882117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94520326894551794263685645 35445122585456922848882117)
              ·
                refine ⟨6645960484773173034165397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35445122585456922848882117 6645960484773173034165397)
                ·
                  refine ⟨311529397723742485976503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6645960484773173034165397 311529397723742485976503)
                  ·
                    rfl

theorem cell20_682539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_682539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682539 prefixEnd_682539 := by exact prefixLift 682539
  have htrace : WordTrace (prefixWord ++ tailWord_682539) baseStart_682539 baseEnd_682539 := by
    simpa [prefixWord, tailWord_682539, baseEnd_682539] using wordTrace_append hprefix tailTrace_682539
  have hstable : (prefixWord ++ tailWord_682539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682539).length < 2 ^ (prefixWord ++ tailWord_682539).sum := by decide
  have hdescent : baseEnd_682539 < baseStart_682539 := by decide
  rcases family_descends (prefixWord ++ tailWord_682539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682548 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_682548 : Nat := 118140960795 + 682548 * 2 ^ 59
def prefixEnd_682548 : Nat := 4983230072969 + 3 ^ 40 * 682548 * 2
def baseEnd_682548 : Nat := 311533505568978454676467

theorem tailTrace_682548 : CollatzResearch.WordTrace tailWord_682548 prefixEnd_682548 311533505568978454676467 := by
  unfold tailWord_682548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447285365626320381452149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16596380487501760508602865 12447285365626320381452149)
  ·
    refine ⟨1166933003027467535761139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12447285365626320381452149 1166933003027467535761139)
    ·
      refine ⟨1750399504541201303641709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166933003027467535761139 1750399504541201303641709)
      ·
        refine ⟨656399814202950488865641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1750399504541201303641709 656399814202950488865641)
        ·
          refine ⟨492299860652212866649231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656399814202950488865641 492299860652212866649231)
          ·
            refine ⟨738449790978319299973847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492299860652212866649231 738449790978319299973847)
            ·
              refine ⟨1107674686467478949960771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738449790978319299973847 1107674686467478949960771)
              ·
                refine ⟨1661512029701218424941157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107674686467478949960771 1661512029701218424941157)
                ·
                  refine ⟨311533505568978454676467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661512029701218424941157 311533505568978454676467)
                  ·
                    rfl

theorem cell20_682548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_682548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682548 prefixEnd_682548 := by exact prefixLift 682548
  have htrace : WordTrace (prefixWord ++ tailWord_682548) baseStart_682548 baseEnd_682548 := by
    simpa [prefixWord, tailWord_682548, baseEnd_682548] using wordTrace_append hprefix tailTrace_682548
  have hstable : (prefixWord ++ tailWord_682548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682548).length < 2 ^ (prefixWord ++ tailWord_682548).sum := by decide
  have hdescent : baseEnd_682548 < baseStart_682548 := by decide
  rcases family_descends (prefixWord ++ tailWord_682548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682549 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_682549 : Nat := 118140960795 + 682549 * 2 ^ 59
def prefixEnd_682549 : Nat := 4983230072969 + 3 ^ 40 * 682549 * 2
def baseEnd_682549 : Nat := 311533961996226895643129

theorem tailTrace_682549 : CollatzResearch.WordTrace tailWord_682549 prefixEnd_682549 311533961996226895643129 := by
  unfold tailWord_682549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24894607204249017933690701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16596404802832678622460467 24894607204249017933690701)
  ·
    refine ⟨9335477701593381725134013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24894607204249017933690701 9335477701593381725134013)
    ·
      refine ⟨3500804138097518146925255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9335477701593381725134013 3500804138097518146925255)
      ·
        refine ⟨5251206207146277220387883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500804138097518146925255 5251206207146277220387883)
        ·
          refine ⟨7876809310719415830581825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251206207146277220387883 7876809310719415830581825)
          ·
            refine ⟨5907606983039561872936369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7876809310719415830581825 5907606983039561872936369)
            ·
              refine ⟨4430705237279671404702277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907606983039561872936369 4430705237279671404702277)
              ·
                refine ⟨830757231989938388381677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4430705237279671404702277 830757231989938388381677)
                ·
                  refine ⟨311533961996226895643129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830757231989938388381677 311533961996226895643129)
                  ·
                    rfl

theorem cell20_682549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_682549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682549 prefixEnd_682549 := by exact prefixLift 682549
  have htrace : WordTrace (prefixWord ++ tailWord_682549) baseStart_682549 baseEnd_682549 := by
    simpa [prefixWord, tailWord_682549, baseEnd_682549] using wordTrace_append hprefix tailTrace_682549
  have hstable : (prefixWord ++ tailWord_682549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682549).length < 2 ^ (prefixWord ++ tailWord_682549).sum := by decide
  have hdescent : baseEnd_682549 < baseStart_682549 := by decide
  rcases family_descends (prefixWord ++ tailWord_682549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682552 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 2]
def baseStart_682552 : Nat := 118140960795 + 682552 * 2 ^ 59
def prefixEnd_682552 : Nat := 4983230072969 + 3 ^ 40 * 682552 * 2
def baseEnd_682552 : Nat := 311535331277972218543117

theorem tailTrace_682552 : CollatzResearch.WordTrace tailWord_682552 prefixEnd_682552 311535331277972218543117 := by
  unfold tailWord_682552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447358311619074723024955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16596477748825432964033273 12447358311619074723024955)
  ·
    refine ⟨18671037467428612084537433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447358311619074723024955 18671037467428612084537433)
    ·
      refine ⟨14003278100571459063403075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18671037467428612084537433 14003278100571459063403075)
      ·
        refine ⟨21004917150857188595104613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003278100571459063403075 21004917150857188595104613)
        ·
          refine ⟨3938421965785722861582115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21004917150857188595104613 3938421965785722861582115)
          ·
            refine ⟨5907632948678584292373173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938421965785722861582115 5907632948678584292373173)
            ·
              refine ⟨553840588938617277409985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5907632948678584292373173 553840588938617277409985)
              ·
                refine ⟨415380441703962958057489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553840588938617277409985 415380441703962958057489)
                ·
                  refine ⟨311535331277972218543117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415380441703962958057489 311535331277972218543117)
                  ·
                    rfl

theorem cell20_682552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_682552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682552 prefixEnd_682552 := by exact prefixLift 682552
  have htrace : WordTrace (prefixWord ++ tailWord_682552) baseStart_682552 baseEnd_682552 := by
    simpa [prefixWord, tailWord_682552, baseEnd_682552] using wordTrace_append hprefix tailTrace_682552
  have hstable : (prefixWord ++ tailWord_682552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682552).length < 2 ^ (prefixWord ++ tailWord_682552).sum := by decide
  have hdescent : baseEnd_682552 < baseStart_682552 := by decide
  rcases family_descends (prefixWord ++ tailWord_682552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682614 : List Nat := [5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_682614 : Nat := 118140960795 + 682614 * 2 ^ 59
def prefixEnd_682614 : Nat := 4983230072969 + 3 ^ 40 * 682614 * 2
def baseEnd_682614 : Nat := 103854543255791852825399

theorem tailTrace_682614 : CollatzResearch.WordTrace tailWord_682614 prefixEnd_682614 103854543255791852825399 := by
  unfold tailWord_682614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556061121813345877175431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16597985299342356023204597 1556061121813345877175431)
  ·
    refine ⟨2334091682720018815763147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556061121813345877175431 2334091682720018815763147)
    ·
      refine ⟨3501137524080028223644721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2334091682720018815763147 3501137524080028223644721)
      ·
        refine ⟨2625853143060021167733541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501137524080028223644721 2625853143060021167733541)
        ·
          refine ⟨492347464323753968950039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2625853143060021167733541 492347464323753968950039)
          ·
            refine ⟨738521196485630953425059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492347464323753968950039 738521196485630953425059)
            ·
              refine ⟨1107781794728446430137589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738521196485630953425059 1107781794728446430137589)
              ·
                refine ⟨103854543255791852825399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107781794728446430137589 103854543255791852825399)
                ·
                  rfl

theorem cell20_682614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_682614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682614 prefixEnd_682614 := by exact prefixLift 682614
  have htrace : WordTrace (prefixWord ++ tailWord_682614) baseStart_682614 baseEnd_682614 := by
    simpa [prefixWord, tailWord_682614, baseEnd_682614] using wordTrace_append hprefix tailTrace_682614
  have hstable : (prefixWord ++ tailWord_682614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682614).length < 2 ^ (prefixWord ++ tailWord_682614).sum := by decide
  have hdescent : baseEnd_682614 < baseStart_682614 := by decide
  rcases family_descends (prefixWord ++ tailWord_682614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682625 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_682625 : Nat := 118140960795 + 682625 * 2 ^ 59
def prefixEnd_682625 : Nat := 4983230072969 + 3 ^ 40 * 682625 * 2
def baseEnd_682625 : Nat := 311568650467108409109485

theorem tailTrace_682625 : CollatzResearch.WordTrace tailWord_682625 prefixEnd_682625 311568650467108409109485 := by
  unfold tailWord_682625
  simp only [CollatzResearch.WordTrace]
  refine ⟨24897379151973682913457329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16598252767982455275638219 24897379151973682913457329)
  ·
    refine ⟨18673034363980262185092997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24897379151973682913457329 18673034363980262185092997)
    ·
      refine ⟨3501193943246299159704937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18673034363980262185092997 3501193943246299159704937)
      ·
        refine ⟨2625895457434724369778703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501193943246299159704937 2625895457434724369778703)
        ·
          refine ⟨3938843186152086554668055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625895457434724369778703 3938843186152086554668055)
          ·
            refine ⟨5908264779228129832002083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938843186152086554668055 5908264779228129832002083)
            ·
              refine ⟨8862397168842194748003125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908264779228129832002083 8862397168842194748003125)
              ·
                refine ⟨830849734578955757625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8862397168842194748003125 830849734578955757625293)
                ·
                  refine ⟨311568650467108409109485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830849734578955757625293 311568650467108409109485)
                  ·
                    rfl

theorem cell20_682625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_682625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682625 prefixEnd_682625 := by exact prefixLift 682625
  have htrace : WordTrace (prefixWord ++ tailWord_682625) baseStart_682625 baseEnd_682625 := by
    simpa [prefixWord, tailWord_682625, baseEnd_682625] using wordTrace_append hprefix tailTrace_682625
  have hstable : (prefixWord ++ tailWord_682625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682625).length < 2 ^ (prefixWord ++ tailWord_682625).sum := by decide
  have hdescent : baseEnd_682625 < baseStart_682625 := by decide
  rcases family_descends (prefixWord ++ tailWord_682625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682649 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 2]
def baseStart_682649 : Nat := 118140960795 + 682649 * 2 ^ 59
def prefixEnd_682649 : Nat := 4983230072969 + 3 ^ 40 * 682649 * 2
def baseEnd_682649 : Nat := 311579604721070992309387

theorem tailTrace_682649 : CollatzResearch.WordTrace tailWord_682649 prefixEnd_682649 311579604721070992309387 := by
  unfold tailWord_682649
  simp only [CollatzResearch.WordTrace]
  refine ⟨24898254503886735012331001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16598836335924490008220667 24898254503886735012331001)
  ·
    refine ⟨18673690877915051259248251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24898254503886735012331001 18673690877915051259248251)
    ·
      refine ⟨28010536316872576888872377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18673690877915051259248251 28010536316872576888872377)
      ·
        refine ⟨21007902237654432666654283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28010536316872576888872377 21007902237654432666654283)
        ·
          refine ⟨31511853356481648999981425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21007902237654432666654283 31511853356481648999981425)
          ·
            refine ⟨23633890017361236749986069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31511853356481648999981425 23633890017361236749986069)
            ·
              refine ⟨1107838594563807972655597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23633890017361236749986069 1107838594563807972655597)
              ·
                refine ⟨415439472961427989745849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1107838594563807972655597 415439472961427989745849)
                ·
                  refine ⟨311579604721070992309387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415439472961427989745849 311579604721070992309387)
                  ·
                    rfl

theorem cell20_682649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_682649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682649 prefixEnd_682649 := by exact prefixLift 682649
  have htrace : WordTrace (prefixWord ++ tailWord_682649) baseStart_682649 baseEnd_682649 := by
    simpa [prefixWord, tailWord_682649, baseEnd_682649] using wordTrace_append hprefix tailTrace_682649
  have hstable : (prefixWord ++ tailWord_682649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682649).length < 2 ^ (prefixWord ++ tailWord_682649).sum := by decide
  have hdescent : baseEnd_682649 < baseStart_682649 := by decide
  rcases family_descends (prefixWord ++ tailWord_682649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682725 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_682725 : Nat := 118140960795 + 682725 * 2 ^ 59
def prefixEnd_682725 : Nat := 4983230072969 + 3 ^ 40 * 682725 * 2
def baseEnd_682725 : Nat := 311614293191952505775743

theorem tailTrace_682725 : CollatzResearch.WordTrace tailWord_682725 prefixEnd_682725 311614293191952505775743 := by
  unfold tailWord_682725
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901026451611399992097629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16600684301074266661398419 24901026451611399992097629)
  ·
    refine ⟨9337884919354274997036611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24901026451611399992097629 9337884919354274997036611)
    ·
      refine ⟨14006827379031412495554917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9337884919354274997036611 14006827379031412495554917)
      ·
        refine ⟨2626280133568389842916547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14006827379031412495554917 2626280133568389842916547)
        ·
          refine ⟨3939420200352584764374821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626280133568389842916547 3939420200352584764374821)
          ·
            refine ⟨738641287566109643320279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3939420200352584764374821 738641287566109643320279)
            ·
              refine ⟨1107961931349164464980419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738641287566109643320279 1107961931349164464980419)
              ·
                refine ⟨1661942897023746697470629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107961931349164464980419 1661942897023746697470629)
                ·
                  refine ⟨311614293191952505775743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1661942897023746697470629 311614293191952505775743)
                  ·
                    rfl

theorem cell20_682725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_682725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682725 prefixEnd_682725 := by exact prefixLift 682725
  have htrace : WordTrace (prefixWord ++ tailWord_682725) baseStart_682725 baseEnd_682725 := by
    simpa [prefixWord, tailWord_682725, baseEnd_682725] using wordTrace_append hprefix tailTrace_682725
  have hstable : (prefixWord ++ tailWord_682725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682725).length < 2 ^ (prefixWord ++ tailWord_682725).sum := by decide
  have hdescent : baseEnd_682725 < baseStart_682725 := by decide
  rcases family_descends (prefixWord ++ tailWord_682725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682770 : List Nat := [3, 2, 4, 1, 2, 8]
def baseStart_682770 : Nat := 118140960795 + 682770 * 2 ^ 59
def prefixEnd_682770 : Nat := 4983230072969 + 3 ^ 40 * 682770 * 2
def baseEnd_682770 : Nat := 11542030830301198121317

theorem tailTrace_682770 : CollatzResearch.WordTrace tailWord_682770 prefixEnd_682770 11542030830301198121317 := by
  unfold tailWord_682770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225666934112093169371441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16601778490965581784990509 6225666934112093169371441)
  ·
    refine ⟨4669250200584069877028581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6225666934112093169371441 4669250200584069877028581)
    ·
      refine ⟨875484412609513101942859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4669250200584069877028581 875484412609513101942859)
      ·
        refine ⟨1313226618914269652914289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875484412609513101942859 1313226618914269652914289)
        ·
          refine ⟨984919964185702239685717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313226618914269652914289 984919964185702239685717)
          ·
            refine ⟨11542030830301198121317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 984919964185702239685717 11542030830301198121317)
            ·
              rfl

theorem cell20_682770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 8].length) (baseStart_682770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682770 prefixEnd_682770 := by exact prefixLift 682770
  have htrace : WordTrace (prefixWord ++ tailWord_682770) baseStart_682770 baseEnd_682770 := by
    simpa [prefixWord, tailWord_682770, baseEnd_682770] using wordTrace_append hprefix tailTrace_682770
  have hstable : (prefixWord ++ tailWord_682770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682770).length < 2 ^ (prefixWord ++ tailWord_682770).sum := by decide
  have hdescent : baseEnd_682770 < baseStart_682770 := by decide
  rcases family_descends (prefixWord ++ tailWord_682770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682780 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_682780 : Nat := 118140960795 + 682780 * 2 ^ 59
def prefixEnd_682780 : Nat := 4983230072969 + 3 ^ 40 * 682780 * 2
def baseEnd_682780 : Nat := 311639396690616758942185

theorem tailTrace_682780 : CollatzResearch.WordTrace tailWord_682780 prefixEnd_682780 311639396690616758942185 := by
  unfold tailWord_682780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451516233206072192674897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16602021644274762923566529 12451516233206072192674897)
  ·
    refine ⟨9338637174904554144506173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12451516233206072192674897 9338637174904554144506173)
    ·
      refine ⟨3501988940589207804189815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9338637174904554144506173 3501988940589207804189815)
      ·
        refine ⟨5252983410883811706284723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501988940589207804189815 5252983410883811706284723)
        ·
          refine ⟨7879475116325717559427085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252983410883811706284723 7879475116325717559427085)
          ·
            refine ⟨2954803168622144084785157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7879475116325717559427085 2954803168622144084785157)
            ·
              refine ⟨554025594116652015897217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2954803168622144084785157 554025594116652015897217)
              ·
                refine ⟨415519195587489011922913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554025594116652015897217 415519195587489011922913)
                ·
                  refine ⟨311639396690616758942185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415519195587489011922913 311639396690616758942185)
                  ·
                    rfl

theorem cell20_682780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_682780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682780 prefixEnd_682780 := by exact prefixLift 682780
  have htrace : WordTrace (prefixWord ++ tailWord_682780) baseStart_682780 baseEnd_682780 := by
    simpa [prefixWord, tailWord_682780, baseEnd_682780] using wordTrace_append hprefix tailTrace_682780
  have hstable : (prefixWord ++ tailWord_682780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682780).length < 2 ^ (prefixWord ++ tailWord_682780).sum := by decide
  have hdescent : baseEnd_682780 < baseStart_682780 := by decide
  rcases family_descends (prefixWord ++ tailWord_682780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682839 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 2]
def baseStart_682839 : Nat := 118140960795 + 682839 * 2 ^ 59
def prefixEnd_682839 : Nat := 4983230072969 + 3 ^ 40 * 682839 * 2
def baseEnd_682839 : Nat := 311666325898274775975277

theorem tailTrace_682839 : CollatzResearch.WordTrace tailWord_682839 prefixEnd_682839 311666325898274775975277 := by
  unfold tailWord_682839
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905184373198397461747571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16603456248798931641165047 24905184373198397461747571)
  ·
    refine ⟨37357776559797596192621357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24905184373198397461747571 37357776559797596192621357)
    ·
      refine ⟨14009166209924098572233009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37357776559797596192621357 14009166209924098572233009)
      ·
        refine ⟨10506874657443073929174757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14009166209924098572233009 10506874657443073929174757)
        ·
          refine ⟨1970038998270576361720267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10506874657443073929174757 1970038998270576361720267)
          ·
            refine ⟨2955058497405864542580401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970038998270576361720267 2955058497405864542580401)
            ·
              refine ⟨2216293873054398406935301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955058497405864542580401 2216293873054398406935301)
              ·
                refine ⟨415555101197699701300369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2216293873054398406935301 415555101197699701300369)
                ·
                  refine ⟨311666325898274775975277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415555101197699701300369 311666325898274775975277)
                  ·
                    rfl

theorem cell20_682839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2].length) (baseStart_682839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682839 prefixEnd_682839 := by exact prefixLift 682839
  have htrace : WordTrace (prefixWord ++ tailWord_682839) baseStart_682839 baseEnd_682839 := by
    simpa [prefixWord, tailWord_682839, baseEnd_682839] using wordTrace_append hprefix tailTrace_682839
  have hstable : (prefixWord ++ tailWord_682839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682839).length < 2 ^ (prefixWord ++ tailWord_682839).sum := by decide
  have hdescent : baseEnd_682839 < baseStart_682839 := by decide
  rcases family_descends (prefixWord ++ tailWord_682839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682867 : List Nat := [1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_682867 : Nat := 118140960795 + 682867 * 2 ^ 59
def prefixEnd_682867 : Nat := 4983230072969 + 3 ^ 40 * 682867 * 2
def baseEnd_682867 : Nat := 103893035287077041013943

theorem tailTrace_682867 : CollatzResearch.WordTrace tailWord_682867 prefixEnd_682867 103893035287077041013943 := by
  unfold tailWord_682867
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906205617096958243766855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16604137078064638829177903 24906205617096958243766855)
  ·
    refine ⟨37359308425645437365650283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24906205617096958243766855 37359308425645437365650283)
    ·
      refine ⟨56038962638468156048475425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37359308425645437365650283 56038962638468156048475425)
      ·
        refine ⟨42029221978851117036356569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56038962638468156048475425 42029221978851117036356569)
        ·
          refine ⟨31521916484138337777267427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42029221978851117036356569 31521916484138337777267427)
          ·
            refine ⟨47282874726207506665901141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31521916484138337777267427 47282874726207506665901141)
            ·
              refine ⟨554096188197744218741029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 47282874726207506665901141 554096188197744218741029)
              ·
                refine ⟨103893035287077041013943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554096188197744218741029 103893035287077041013943)
                ·
                  rfl

theorem cell20_682867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_682867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682867 prefixEnd_682867 := by exact prefixLift 682867
  have htrace : WordTrace (prefixWord ++ tailWord_682867) baseStart_682867 baseEnd_682867 := by
    simpa [prefixWord, tailWord_682867, baseEnd_682867] using wordTrace_append hprefix tailTrace_682867
  have hstable : (prefixWord ++ tailWord_682867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682867).length < 2 ^ (prefixWord ++ tailWord_682867).sum := by decide
  have hdescent : baseEnd_682867 < baseStart_682867 := by decide
  rcases family_descends (prefixWord ++ tailWord_682867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682877 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 2]
def baseStart_682877 : Nat := 118140960795 + 682877 * 2 ^ 59
def prefixEnd_682877 : Nat := 4983230072969 + 3 ^ 40 * 682877 * 2
def baseEnd_682877 : Nat := 311683670133715532708455

theorem tailTrace_682877 : CollatzResearch.WordTrace tailWord_682877 prefixEnd_682877 311683670133715532708455 := by
  unfold tailWord_682877
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906570347060729951630885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16604380231373819967753923 24906570347060729951630885)
  ·
    refine ⟨4669981940073886865930791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24906570347060729951630885 4669981940073886865930791)
    ·
      refine ⟨7004972910110830298896187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669981940073886865930791 7004972910110830298896187)
      ·
        refine ⟨10507459365166245448344281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7004972910110830298896187 10507459365166245448344281)
        ·
          refine ⟨7880594523874684086258211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10507459365166245448344281 7880594523874684086258211)
          ·
            refine ⟨11820891785812026129387317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880594523874684086258211 11820891785812026129387317)
            ·
              refine ⟨1108208604919877449630061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11820891785812026129387317 1108208604919877449630061)
              ·
                refine ⟨415578226844954043611273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108208604919877449630061 415578226844954043611273)
                ·
                  refine ⟨311683670133715532708455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415578226844954043611273 311683670133715532708455)
                  ·
                    rfl

theorem cell20_682877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_682877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682877 prefixEnd_682877 := by exact prefixLift 682877
  have htrace : WordTrace (prefixWord ++ tailWord_682877) baseStart_682877 baseEnd_682877 := by
    simpa [prefixWord, tailWord_682877, baseEnd_682877] using wordTrace_append hprefix tailTrace_682877
  have hstable : (prefixWord ++ tailWord_682877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682877).length < 2 ^ (prefixWord ++ tailWord_682877).sum := by decide
  have hdescent : baseEnd_682877 < baseStart_682877 := by decide
  rcases family_descends (prefixWord ++ tailWord_682877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682908 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_682908 : Nat := 118140960795 + 682908 * 2 ^ 59
def prefixEnd_682908 : Nat := 4983230072969 + 3 ^ 40 * 682908 * 2
def baseEnd_682908 : Nat := 311697819378417202674995

theorem tailTrace_682908 : CollatzResearch.WordTrace tailWord_682908 prefixEnd_682908 311697819378417202674995 := by
  unfold tailWord_682908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12453850504974211123004689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16605134006632281497339585 12453850504974211123004689)
  ·
    refine ⟨9340387878730658342253517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12453850504974211123004689 9340387878730658342253517)
    ·
      refine ⟨3502645454523996878345069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9340387878730658342253517 3502645454523996878345069)
      ·
        refine ⟨1313492045446498829379401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3502645454523996878345069 1313492045446498829379401)
        ·
          refine ⟨985119034084874122034551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313492045446498829379401 985119034084874122034551)
          ·
            refine ⟨1477678551127311183051827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985119034084874122034551 1477678551127311183051827)
            ·
              refine ⟨2216517826690966774577741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477678551127311183051827 2216517826690966774577741)
              ·
                refine ⟨831194185009112540466653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2216517826690966774577741 831194185009112540466653)
                ·
                  refine ⟨311697819378417202674995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831194185009112540466653 311697819378417202674995)
                  ·
                    rfl

theorem cell20_682908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_682908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682908 prefixEnd_682908 := by exact prefixLift 682908
  have htrace : WordTrace (prefixWord ++ tailWord_682908) baseStart_682908 baseEnd_682908 := by
    simpa [prefixWord, tailWord_682908, baseEnd_682908] using wordTrace_append hprefix tailTrace_682908
  have hstable : (prefixWord ++ tailWord_682908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682908).length < 2 ^ (prefixWord ++ tailWord_682908).sum := by decide
  have hdescent : baseEnd_682908 < baseStart_682908 := by decide
  rcases family_descends (prefixWord ++ tailWord_682908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_682991 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 2]
def baseStart_682991 : Nat := 118140960795 + 682991 * 2 ^ 59
def prefixEnd_682991 : Nat := 4983230072969 + 3 ^ 40 * 682991 * 2
def baseEnd_682991 : Nat := 311735702840037802907989

theorem tailTrace_682991 : CollatzResearch.WordTrace tailWord_682991 prefixEnd_682991 311735702840037802907989 := by
  unfold tailWord_682991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24910728268647727421280827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16607152179098484947520551 24910728268647727421280827)
  ·
    refine ⟨37366092402971591131921241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24910728268647727421280827 37366092402971591131921241)
    ·
      refine ⟨28024569302228693348940931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37366092402971591131921241 28024569302228693348940931)
      ·
        refine ⟨42036853953343040023411397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28024569302228693348940931 42036853953343040023411397)
        ·
          refine ⟨7881910116251820004389637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42036853953343040023411397 7881910116251820004389637)
          ·
            refine ⟨1477858146797216250823057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7881910116251820004389637 1477858146797216250823057)
            ·
              refine ⟨1108393610097912188117293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477858146797216250823057 1108393610097912188117293)
              ·
                refine ⟨415647603786717070543985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108393610097912188117293 415647603786717070543985)
                ·
                  refine ⟨311735702840037802907989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415647603786717070543985 311735702840037802907989)
                  ·
                    rfl

theorem cell20_682991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2].length) (baseStart_682991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_682991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_682991 prefixEnd_682991 := by exact prefixLift 682991
  have htrace : WordTrace (prefixWord ++ tailWord_682991) baseStart_682991 baseEnd_682991 := by
    simpa [prefixWord, tailWord_682991, baseEnd_682991] using wordTrace_append hprefix tailTrace_682991
  have hstable : (prefixWord ++ tailWord_682991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_682991).length < 2 ^ (prefixWord ++ tailWord_682991).sum := by decide
  have hdescent : baseEnd_682991 < baseStart_682991 := by decide
  rcases family_descends (prefixWord ++ tailWord_682991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683022 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_683022 : Nat := 118140960795 + 683022 * 2 ^ 59
def prefixEnd_683022 : Nat := 4983230072969 + 3 ^ 40 * 683022 * 2
def baseEnd_683022 : Nat := 311749852084739472874529

theorem tailTrace_683022 : CollatzResearch.WordTrace tailWord_683022 prefixEnd_683022 311749852084739472874529 := by
  unfold tailWord_683022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113982366441927464457415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16607905954356946477106213 3113982366441927464457415)
  ·
    refine ⟨4670973549662891196686123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113982366441927464457415 4670973549662891196686123)
    ·
      refine ⟨7006460324494336795029185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670973549662891196686123 7006460324494336795029185)
      ·
        refine ⟨5254845243370752596271889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7006460324494336795029185 5254845243370752596271889)
        ·
          refine ⟨3941133932528064447203917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5254845243370752596271889 3941133932528064447203917)
          ·
            refine ⟨1477925224698024167701469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3941133932528064447203917 1477925224698024167701469)
            ·
              refine ⟨554221959261759062888051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1477925224698024167701469 554221959261759062888051)
              ·
                refine ⟨831332938892638594332077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554221959261759062888051 831332938892638594332077)
                ·
                  refine ⟨311749852084739472874529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831332938892638594332077 311749852084739472874529)
                  ·
                    rfl

theorem cell20_683022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_683022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683022 prefixEnd_683022 := by exact prefixLift 683022
  have htrace : WordTrace (prefixWord ++ tailWord_683022) baseStart_683022 baseEnd_683022 := by
    simpa [prefixWord, tailWord_683022, baseEnd_683022] using wordTrace_append hprefix tailTrace_683022
  have hstable : (prefixWord ++ tailWord_683022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683022).length < 2 ^ (prefixWord ++ tailWord_683022).sum := by decide
  have hdescent : baseEnd_683022 < baseStart_683022 := by decide
  rcases family_descends (prefixWord ++ tailWord_683022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683033 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_683033 : Nat := 118140960795 + 683033 * 2 ^ 59
def prefixEnd_683033 : Nat := 4983230072969 + 3 ^ 40 * 683033 * 2
def baseEnd_683033 : Nat := 311754872784472323507817

theorem tailTrace_683033 : CollatzResearch.WordTrace tailWord_683033 prefixEnd_683033 311754872784472323507817 := by
  unfold tailWord_683033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912260134495568594309753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16608173422997045729539835 24912260134495568594309753)
  ·
    refine ⟨18684195100871676445732315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24912260134495568594309753 18684195100871676445732315)
    ·
      refine ⟨28026292651307514668598473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18684195100871676445732315 28026292651307514668598473)
      ·
        refine ⟨21019719488480636001448855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28026292651307514668598473 21019719488480636001448855)
        ·
          refine ⟨31529579232720954002173283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21019719488480636001448855 31529579232720954002173283)
          ·
            refine ⟨47294368849081431003259925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31529579232720954002173283 47294368849081431003259925)
            ·
              refine ⟨2216923539800692078277809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47294368849081431003259925 2216923539800692078277809)
              ·
                refine ⟨1662692654850519058708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216923539800692078277809 1662692654850519058708357)
                ·
                  refine ⟨311754872784472323507817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662692654850519058708357 311754872784472323507817)
                  ·
                    rfl

theorem cell20_683033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_683033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683033 prefixEnd_683033 := by exact prefixLift 683033
  have htrace : WordTrace (prefixWord ++ tailWord_683033) baseStart_683033 baseEnd_683033 := by
    simpa [prefixWord, tailWord_683033, baseEnd_683033] using wordTrace_append hprefix tailTrace_683033
  have hstable : (prefixWord ++ tailWord_683033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683033).length < 2 ^ (prefixWord ++ tailWord_683033).sum := by decide
  have hdescent : baseEnd_683033 < baseStart_683033 := by decide
  rcases family_descends (prefixWord ++ tailWord_683033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683064 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_683064 : Nat := 118140960795 + 683064 * 2 ^ 59
def prefixEnd_683064 : Nat := 4983230072969 + 3 ^ 40 * 683064 * 2
def baseEnd_683064 : Nat := 311769022029173993474357

theorem tailTrace_683064 : CollatzResearch.WordTrace tailWord_683064 prefixEnd_683064 311769022029173993474357 := by
  unfold tailWord_683064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456695398691630444344123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16608927198255507259125497 12456695398691630444344123)
  ·
    refine ⟨18685043098037445666516185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12456695398691630444344123 18685043098037445666516185)
    ·
      refine ⟨14013782323528084249887139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18685043098037445666516185 14013782323528084249887139)
      ·
        refine ⟨21020673485292126374830709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14013782323528084249887139 21020673485292126374830709)
        ·
          refine ⟨1970688139246136847640379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21020673485292126374830709 1970688139246136847640379)
          ·
            refine ⟨2956032208869205271460569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970688139246136847640379 2956032208869205271460569)
            ·
              refine ⟨2217024156651903953595427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956032208869205271460569 2217024156651903953595427)
              ·
                refine ⟨3325536234977855930393141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217024156651903953595427 3325536234977855930393141)
                ·
                  refine ⟨311769022029173993474357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3325536234977855930393141 311769022029173993474357)
                  ·
                    rfl

theorem cell20_683064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_683064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683064 prefixEnd_683064 := by exact prefixLift 683064
  have htrace : WordTrace (prefixWord ++ tailWord_683064) baseStart_683064 baseEnd_683064 := by
    simpa [prefixWord, tailWord_683064, baseEnd_683064] using wordTrace_append hprefix tailTrace_683064
  have hstable : (prefixWord ++ tailWord_683064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683064).length < 2 ^ (prefixWord ++ tailWord_683064).sum := by decide
  have hdescent : baseEnd_683064 < baseStart_683064 := by decide
  rcases family_descends (prefixWord ++ tailWord_683064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683112 : List Nat := [2, 1, 4, 4, 2, 7]
def baseStart_683112 : Nat := 118140960795 + 683112 * 2 ^ 59
def prefixEnd_683112 : Nat := 4983230072969 + 3 ^ 40 * 683112 * 2
def baseEnd_683112 : Nat := 11547812242114783699043

theorem tailTrace_683112 : CollatzResearch.WordTrace tailWord_683112 prefixEnd_683112 11547812242114783699043 := by
  unfold tailWord_683112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457570750604682543217795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16610094334139576724290393 12457570750604682543217795)
  ·
    refine ⟨18686356125907023814826693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12457570750604682543217795 18686356125907023814826693)
    ·
      refine ⟨3503691773607566965280005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18686356125907023814826693 3503691773607566965280005)
      ·
        refine ⟨656942207551418805990001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3503691773607566965280005 656942207551418805990001)
        ·
          refine ⟨492706655663564104492501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656942207551418805990001 492706655663564104492501)
          ·
            refine ⟨11547812242114783699043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 492706655663564104492501 11547812242114783699043)
            ·
              rfl

theorem cell20_683112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 7].length) (baseStart_683112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683112 prefixEnd_683112 := by exact prefixLift 683112
  have htrace : WordTrace (prefixWord ++ tailWord_683112) baseStart_683112 baseEnd_683112 := by
    simpa [prefixWord, tailWord_683112, baseEnd_683112] using wordTrace_append hprefix tailTrace_683112
  have hstable : (prefixWord ++ tailWord_683112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683112).length < 2 ^ (prefixWord ++ tailWord_683112).sum := by decide
  have hdescent : baseEnd_683112 < baseStart_683112 := by decide
  rcases family_descends (prefixWord ++ tailWord_683112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683126 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_683126 : Nat := 118140960795 + 683126 * 2 ^ 59
def prefixEnd_683126 : Nat := 4983230072969 + 3 ^ 40 * 683126 * 2
def baseEnd_683126 : Nat := 311797320518577333407437

theorem tailTrace_683126 : CollatzResearch.WordTrace tailWord_683126 prefixEnd_683126 311797320518577333407437 := by
  unfold tailWord_683126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557228257697415342340327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16610434748772430318296821 1557228257697415342340327)
  ·
    refine ⟨2335842386546123013510491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1557228257697415342340327 2335842386546123013510491)
    ·
      refine ⟨3503763579819184520265737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335842386546123013510491 3503763579819184520265737)
      ·
        refine ⟨2627822684864388390199303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3503763579819184520265737 2627822684864388390199303)
        ·
          refine ⟨3941734027296582585298955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627822684864388390199303 3941734027296582585298955)
          ·
            refine ⟨5912601040944873877948433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941734027296582585298955 5912601040944873877948433)
            ·
              refine ⟨4434450780708655408461325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912601040944873877948433 4434450780708655408461325)
              ·
                refine ⟨1662919042765745778172997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4434450780708655408461325 1662919042765745778172997)
                ·
                  refine ⟨311797320518577333407437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1662919042765745778172997 311797320518577333407437)
                  ·
                    rfl

theorem cell20_683126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_683126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683126 prefixEnd_683126 := by exact prefixLift 683126
  have htrace : WordTrace (prefixWord ++ tailWord_683126) baseStart_683126 baseEnd_683126 := by
    simpa [prefixWord, tailWord_683126, baseEnd_683126] using wordTrace_append hprefix tailTrace_683126
  have hstable : (prefixWord ++ tailWord_683126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683126).length < 2 ^ (prefixWord ++ tailWord_683126).sum := by decide
  have hdescent : baseEnd_683126 < baseStart_683126 := by decide
  rcases family_descends (prefixWord ++ tailWord_683126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683150 : List Nat := [4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_683150 : Nat := 118140960795 + 683150 * 2 ^ 59
def prefixEnd_683150 : Nat := 4983230072969 + 3 ^ 40 * 683150 * 2
def baseEnd_683150 : Nat := 103936091590846638869113

theorem tailTrace_683150 : CollatzResearch.WordTrace tailWord_683150 prefixEnd_683150 103936091590846638869113 := by
  unfold tailWord_683150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114565934383962197039863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16611018316714465050879269 3114565934383962197039863)
  ·
    refine ⟨4671848901575943295559795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114565934383962197039863 4671848901575943295559795)
    ·
      refine ⟨7007773352363914943339693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4671848901575943295559795 7007773352363914943339693)
      ·
        refine ⟨2627915007136468103752385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7007773352363914943339693 2627915007136468103752385)
        ·
          refine ⟨1970936255352351077814289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627915007136468103752385 1970936255352351077814289)
          ·
            refine ⟨1478202191514263308360717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970936255352351077814289 1478202191514263308360717)
            ·
              refine ⟨554325821817848740635269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1478202191514263308360717 554325821817848740635269)
              ·
                refine ⟨103936091590846638869113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554325821817848740635269 103936091590846638869113)
                ·
                  rfl

theorem cell20_683150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_683150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683150 prefixEnd_683150 := by exact prefixLift 683150
  have htrace : WordTrace (prefixWord ++ tailWord_683150) baseStart_683150 baseEnd_683150 := by
    simpa [prefixWord, tailWord_683150, baseEnd_683150] using wordTrace_append hprefix tailTrace_683150
  have hstable : (prefixWord ++ tailWord_683150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683150).length < 2 ^ (prefixWord ++ tailWord_683150).sum := by decide
  have hdescent : baseEnd_683150 < baseStart_683150 := by decide
  rcases family_descends (prefixWord ++ tailWord_683150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683181 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_683181 : Nat := 118140960795 + 683181 * 2 ^ 59
def prefixEnd_683181 : Nat := 4983230072969 + 3 ^ 40 * 683181 * 2
def baseEnd_683181 : Nat := 311822424017241586573879

theorem tailTrace_683181 : CollatzResearch.WordTrace tailWord_683181 prefixEnd_683181 311822424017241586573879 := by
  unfold tailWord_683181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24917658137959389870697397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16611772091972926580464931 24917658137959389870697397)
  ·
    refine ⟨2336030450433692800377881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24917658137959389870697397 2336030450433692800377881)
    ·
      refine ⟨1752022837825269600283411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2336030450433692800377881 1752022837825269600283411)
      ·
        refine ⟨2628034256737904400425117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752022837825269600283411 2628034256737904400425117)
        ·
          refine ⟨985512846276714150159419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2628034256737904400425117 985512846276714150159419)
          ·
            refine ⟨1478269269415071225239129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985512846276714150159419 1478269269415071225239129)
            ·
              refine ⟨1108701952061303418929347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478269269415071225239129 1108701952061303418929347)
              ·
                refine ⟨1663052928091955128394021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108701952061303418929347 1663052928091955128394021)
                ·
                  refine ⟨311822424017241586573879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663052928091955128394021 311822424017241586573879)
                  ·
                    rfl

theorem cell20_683181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_683181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683181 prefixEnd_683181 := by exact prefixLift 683181
  have htrace : WordTrace (prefixWord ++ tailWord_683181) baseStart_683181 baseEnd_683181 := by
    simpa [prefixWord, tailWord_683181, baseEnd_683181] using wordTrace_append hprefix tailTrace_683181
  have hstable : (prefixWord ++ tailWord_683181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683181).length < 2 ^ (prefixWord ++ tailWord_683181).sum := by decide
  have hdescent : baseEnd_683181 < baseStart_683181 := by decide
  rcases family_descends (prefixWord ++ tailWord_683181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683247 : List Nat := [1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_683247 : Nat := 118140960795 + 683247 * 2 ^ 59
def prefixEnd_683247 : Nat := 4983230072969 + 3 ^ 40 * 683247 * 2
def baseEnd_683247 : Nat := 103950849405212896791203

theorem tailTrace_683247 : CollatzResearch.WordTrace tailWord_683247 prefixEnd_683247 103950849405212896791203 := by
  unfold tailWord_683247
  simp only [CollatzResearch.WordTrace]
  refine ⟨24920065355720283142599995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16613376903813522095066663 24920065355720283142599995)
  ·
    refine ⟨37380098033580424713899993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24920065355720283142599995 37380098033580424713899993)
    ·
      refine ⟨28035073525185318535424995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37380098033580424713899993 28035073525185318535424995)
      ·
        refine ⟨42052610287777977803137493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28035073525185318535424995 42052610287777977803137493)
        ·
          refine ⟨985608053619796354761035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42052610287777977803137493 985608053619796354761035)
          ·
            refine ⟨1478412080429694532141553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985608053619796354761035 1478412080429694532141553)
            ·
              refine ⟨1108809060322270899106165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478412080429694532141553 1108809060322270899106165)
              ·
                refine ⟨103950849405212896791203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1108809060322270899106165 103950849405212896791203)
                ·
                  rfl

theorem cell20_683247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_683247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683247 prefixEnd_683247 := by exact prefixLift 683247
  have htrace : WordTrace (prefixWord ++ tailWord_683247) baseStart_683247 baseEnd_683247 := by
    simpa [prefixWord, tailWord_683247, baseEnd_683247] using wordTrace_append hprefix tailTrace_683247
  have hstable : (prefixWord ++ tailWord_683247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683247).length < 2 ^ (prefixWord ++ tailWord_683247).sum := by decide
  have hdescent : baseEnd_683247 < baseStart_683247 := by decide
  rcases family_descends (prefixWord ++ tailWord_683247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683292 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_683292 : Nat := 118140960795 + 683292 * 2 ^ 59
def prefixEnd_683292 : Nat := 4983230072969 + 3 ^ 40 * 683292 * 2
def baseEnd_683292 : Nat := 311873087441818533873425

theorem tailTrace_683292 : CollatzResearch.WordTrace tailWord_683292 prefixEnd_683292 311873087441818533873425 := by
  unfold tailWord_683292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12460853320278627913994065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16614471093704837218658753 12460853320278627913994065)
  ·
    refine ⟨9345639990208970935495549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12460853320278627913994065 9345639990208970935495549)
    ·
      refine ⟨3504614996328364100810831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9345639990208970935495549 3504614996328364100810831)
      ·
        refine ⟨5256922494492546151216247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504614996328364100810831 5256922494492546151216247)
        ·
          refine ⟨7885383741738819226824371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256922494492546151216247 7885383741738819226824371)
          ·
            refine ⟨11828075612608228840236557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7885383741738819226824371 11828075612608228840236557)
            ·
              refine ⟨4435528354728085815088709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11828075612608228840236557 4435528354728085815088709)
              ·
                refine ⟨831661566511516090329133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4435528354728085815088709 831661566511516090329133)
                ·
                  refine ⟨311873087441818533873425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831661566511516090329133 311873087441818533873425)
                  ·
                    rfl

theorem cell20_683292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_683292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683292 prefixEnd_683292 := by exact prefixLift 683292
  have htrace : WordTrace (prefixWord ++ tailWord_683292) baseStart_683292 baseEnd_683292 := by
    simpa [prefixWord, tailWord_683292, baseEnd_683292] using wordTrace_append hprefix tailTrace_683292
  have hstable : (prefixWord ++ tailWord_683292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683292).length < 2 ^ (prefixWord ++ tailWord_683292).sum := by decide
  have hdescent : baseEnd_683292 < baseStart_683292 := by decide
  rcases family_descends (prefixWord ++ tailWord_683292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683295 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 2]
def baseStart_683295 : Nat := 118140960795 + 683295 * 2 ^ 59
def prefixEnd_683295 : Nat := 4983230072969 + 3 ^ 40 * 683295 * 2
def baseEnd_683295 : Nat := 311874456723563856773413

theorem tailTrace_683295 : CollatzResearch.WordTrace tailWord_683295 prefixEnd_683295 311874456723563856773413 := by
  unfold tailWord_683295
  simp only [CollatzResearch.WordTrace]
  refine ⟨24921816059546387340347339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16614544039697591560231559 24921816059546387340347339)
  ·
    refine ⟨37382724089319581010521009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24921816059546387340347339 37382724089319581010521009)
    ·
      refine ⟨28037043066989685757890757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37382724089319581010521009 28037043066989685757890757)
      ·
        refine ⟨5256945575060566079604517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28037043066989685757890757 5256945575060566079604517)
        ·
          refine ⟨985677295323856139925847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5256945575060566079604517 985677295323856139925847)
          ·
            refine ⟨1478515942985784209888771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985677295323856139925847 1478515942985784209888771)
            ·
              refine ⟨2217773914478676314833157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478515942985784209888771 2217773914478676314833157)
              ·
                refine ⟨415832608964751809031217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2217773914478676314833157 415832608964751809031217)
                ·
                  refine ⟨311874456723563856773413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415832608964751809031217 311874456723563856773413)
                  ·
                    rfl

theorem cell20_683295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2].length) (baseStart_683295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683295 prefixEnd_683295 := by exact prefixLift 683295
  have htrace : WordTrace (prefixWord ++ tailWord_683295) baseStart_683295 baseEnd_683295 := by
    simpa [prefixWord, tailWord_683295, baseEnd_683295] using wordTrace_append hprefix tailTrace_683295
  have hstable : (prefixWord ++ tailWord_683295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683295).length < 2 ^ (prefixWord ++ tailWord_683295).sum := by decide
  have hdescent : baseEnd_683295 < baseStart_683295 := by decide
  rcases family_descends (prefixWord ++ tailWord_683295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683316 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_683316 : Nat := 118140960795 + 683316 * 2 ^ 59
def prefixEnd_683316 : Nat := 4983230072969 + 3 ^ 40 * 683316 * 2
def baseEnd_683316 : Nat := 311884041695781117073327

theorem tailTrace_683316 : CollatzResearch.WordTrace tailWord_683316 prefixEnd_683316 311884041695781117073327 := by
  unfold tailWord_683316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12461290996235153963430901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16615054661646871951241201 12461290996235153963430901)
  ·
    refine ⟨1168246030897045684071647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12461290996235153963430901 1168246030897045684071647)
    ·
      refine ⟨1752369046345568526107471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168246030897045684071647 1752369046345568526107471)
      ·
        refine ⟨2628553569518352789161207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752369046345568526107471 2628553569518352789161207)
        ·
          refine ⟨3942830354277529183741811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628553569518352789161207 3942830354277529183741811)
          ·
            refine ⟨5914245531416293775612717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942830354277529183741811 5914245531416293775612717)
            ·
              refine ⟨2217842074281110165854769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5914245531416293775612717 2217842074281110165854769)
              ·
                refine ⟨1663381555710832624391077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217842074281110165854769 1663381555710832624391077)
                ·
                  refine ⟨311884041695781117073327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663381555710832624391077 311884041695781117073327)
                  ·
                    rfl

theorem cell20_683316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_683316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683316 prefixEnd_683316 := by exact prefixLift 683316
  have htrace : WordTrace (prefixWord ++ tailWord_683316) baseStart_683316 baseEnd_683316 := by
    simpa [prefixWord, tailWord_683316, baseEnd_683316] using wordTrace_append hprefix tailTrace_683316
  have hstable : (prefixWord ++ tailWord_683316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683316).length < 2 ^ (prefixWord ++ tailWord_683316).sum := by decide
  have hdescent : baseEnd_683316 < baseStart_683316 := by decide
  rcases family_descends (prefixWord ++ tailWord_683316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683354 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_683354 : Nat := 118140960795 + 683354 * 2 ^ 59
def prefixEnd_683354 : Nat := 4983230072969 + 3 ^ 40 * 683354 * 2
def baseEnd_683354 : Nat := 311901385931221873806505

theorem tailTrace_683354 : CollatzResearch.WordTrace tailWord_683354 prefixEnd_683354 311901385931221873806505 := by
  unfold tailWord_683354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230991991583160104186279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16615978644221760277830077 6230991991583160104186279)
  ·
    refine ⟨9346487987374740156279419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6230991991583160104186279 9346487987374740156279419)
    ·
      refine ⟨14019731981062110234419129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9346487987374740156279419 14019731981062110234419129)
      ·
        refine ⟨10514798985796582675814347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14019731981062110234419129 10514798985796582675814347)
        ·
          refine ⟨15772198478694874013721521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10514798985796582675814347 15772198478694874013721521)
          ·
            refine ⟨11829148859021155510291141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15772198478694874013721521 11829148859021155510291141)
            ·
              refine ⟨2217965411066466658179589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11829148859021155510291141 2217965411066466658179589)
              ·
                refine ⟨415868514574962498408673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2217965411066466658179589 415868514574962498408673)
                ·
                  refine ⟨311901385931221873806505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415868514574962498408673 311901385931221873806505)
                  ·
                    rfl

theorem cell20_683354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_683354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683354 prefixEnd_683354 := by exact prefixLift 683354
  have htrace : WordTrace (prefixWord ++ tailWord_683354) baseStart_683354 baseEnd_683354 := by
    simpa [prefixWord, tailWord_683354, baseEnd_683354] using wordTrace_append hprefix tailTrace_683354
  have hstable : (prefixWord ++ tailWord_683354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683354).length < 2 ^ (prefixWord ++ tailWord_683354).sum := by decide
  have hdescent : baseEnd_683354 < baseStart_683354 := by decide
  rcases family_descends (prefixWord ++ tailWord_683354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683374 : List Nat := [4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_683374 : Nat := 118140960795 + 683374 * 2 ^ 59
def prefixEnd_683374 : Nat := 4983230072969 + 3 ^ 40 * 683374 * 2
def baseEnd_683374 : Nat := 103970171492063564379919

theorem tailTrace_683374 : CollatzResearch.WordTrace tailWord_683374 prefixEnd_683374 103970171492063564379919 := by
  unfold tailWord_683374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115587178282522979059147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16616464950840122554982117 3115587178282522979059147)
  ·
    refine ⟨4673380767423784468588721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3115587178282522979059147 4673380767423784468588721)
    ·
      refine ⟨3505035575567838351441541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673380767423784468588721 3505035575567838351441541)
      ·
        refine ⟨657194170418969690895289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3505035575567838351441541 657194170418969690895289)
        ·
          refine ⟨492895627814227268171467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657194170418969690895289 492895627814227268171467)
          ·
            refine ⟨739343441721340902257201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492895627814227268171467 739343441721340902257201)
            ·
              refine ⟨554507581291005676692901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739343441721340902257201 554507581291005676692901)
              ·
                refine ⟨103970171492063564379919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554507581291005676692901 103970171492063564379919)
                ·
                  rfl

theorem cell20_683374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_683374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683374 prefixEnd_683374 := by exact prefixLift 683374
  have htrace : WordTrace (prefixWord ++ tailWord_683374) baseStart_683374 baseEnd_683374 := by
    simpa [prefixWord, tailWord_683374, baseEnd_683374] using wordTrace_append hprefix tailTrace_683374
  have hstable : (prefixWord ++ tailWord_683374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683374).length < 2 ^ (prefixWord ++ tailWord_683374).sum := by decide
  have hdescent : baseEnd_683374 < baseStart_683374 := by decide
  rcases family_descends (prefixWord ++ tailWord_683374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683389 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_683389 : Nat := 118140960795 + 683389 * 2 ^ 59
def prefixEnd_683389 : Nat := 4983230072969 + 3 ^ 40 * 683389 * 2
def baseEnd_683389 : Nat := 311917360884917307639695

theorem tailTrace_683389 : CollatzResearch.WordTrace tailWord_683389 prefixEnd_683389 311917360884917307639695 := by
  unfold tailWord_683389
  simp only [CollatzResearch.WordTrace]
  refine ⟨24925244521205841394269221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16616829680803894262846147 24925244521205841394269221)
  ·
    refine ⟨4673483347726095261425479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24925244521205841394269221 4673483347726095261425479)
    ·
      refine ⟨7010225021589142892138219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673483347726095261425479 7010225021589142892138219)
      ·
        refine ⟨10515337532383714338207329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010225021589142892138219 10515337532383714338207329)
        ·
          refine ⟨7886503149287785753655497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515337532383714338207329 7886503149287785753655497)
          ·
            refine ⟨5914877361965839315241623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886503149287785753655497 5914877361965839315241623)
            ·
              refine ⟨8872316042948758972862435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5914877361965839315241623 8872316042948758972862435)
              ·
                refine ⟨13308474064423138459293653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8872316042948758972862435 13308474064423138459293653)
                ·
                  refine ⟨311917360884917307639695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13308474064423138459293653 311917360884917307639695)
                  ·
                    rfl

theorem cell20_683389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_683389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683389 prefixEnd_683389 := by exact prefixLift 683389
  have htrace : WordTrace (prefixWord ++ tailWord_683389) baseStart_683389 baseEnd_683389 := by
    simpa [prefixWord, tailWord_683389, baseEnd_683389] using wordTrace_append hprefix tailTrace_683389
  have hstable : (prefixWord ++ tailWord_683389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683389).length < 2 ^ (prefixWord ++ tailWord_683389).sum := by decide
  have hdescent : baseEnd_683389 < baseStart_683389 := by decide
  rcases family_descends (prefixWord ++ tailWord_683389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683413 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_683413 : Nat := 118140960795 + 683413 * 2 ^ 59
def prefixEnd_683413 : Nat := 4983230072969 + 3 ^ 40 * 683413 * 2
def baseEnd_683413 : Nat := 311928315138879890839597

theorem tailTrace_683413 : CollatzResearch.WordTrace tailWord_683413 prefixEnd_683413 311928315138879890839597 := by
  unfold tailWord_683413
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926119873118893493142893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16617413248745928995428595 24926119873118893493142893)
  ·
    refine ⟨9347294952419585059928585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24926119873118893493142893 9347294952419585059928585)
    ·
      refine ⟨7010471214314688794946439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347294952419585059928585 7010471214314688794946439)
      ·
        refine ⟨10515706821472033192419659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010471214314688794946439 10515706821472033192419659)
        ·
          refine ⟨15773560232208049788629489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10515706821472033192419659 15773560232208049788629489)
          ·
            refine ⟨11830170174156037341472117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15773560232208049788629489 11830170174156037341472117)
            ·
              refine ⟨1109078453827128500763011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11830170174156037341472117 1109078453827128500763011)
              ·
                refine ⟨1663617680740692751144517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109078453827128500763011 1663617680740692751144517)
                ·
                  refine ⟨311928315138879890839597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663617680740692751144517 311928315138879890839597)
                  ·
                    rfl

theorem cell20_683413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_683413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683413 prefixEnd_683413 := by exact prefixLift 683413
  have htrace : WordTrace (prefixWord ++ tailWord_683413) baseStart_683413 baseEnd_683413 := by
    simpa [prefixWord, tailWord_683413, baseEnd_683413] using wordTrace_append hprefix tailTrace_683413
  have hstable : (prefixWord ++ tailWord_683413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683413).length < 2 ^ (prefixWord ++ tailWord_683413).sum := by decide
  have hdescent : baseEnd_683413 < baseStart_683413 := by decide
  rcases family_descends (prefixWord ++ tailWord_683413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683423 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_683423 : Nat := 118140960795 + 683423 * 2 ^ 59
def prefixEnd_683423 : Nat := 4983230072969 + 3 ^ 40 * 683423 * 2
def baseEnd_683423 : Nat := 311932879411364300506223

theorem tailTrace_683423 : CollatzResearch.WordTrace tailWord_683423 prefixEnd_683423 311932879411364300506223 := by
  unfold tailWord_683423
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926484603082665201006923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16617656402055110134004615 24926484603082665201006923)
  ·
    refine ⟨37389726904623997801510385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24926484603082665201006923 37389726904623997801510385)
    ·
      refine ⟨28042295178467998351132789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37389726904623997801510385 28042295178467998351132789)
      ·
        refine ⟨2628965172981374845418699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28042295178467998351132789 2628965172981374845418699)
        ·
          refine ⟨3943447759472062268128049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628965172981374845418699 3943447759472062268128049)
          ·
            refine ⟨2957585819604046701096037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3943447759472062268128049 2957585819604046701096037)
            ·
              refine ⟨554547341175758756455507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2957585819604046701096037 554547341175758756455507)
              ·
                refine ⟨831821011763638134683261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554547341175758756455507 831821011763638134683261)
                ·
                  refine ⟨311932879411364300506223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831821011763638134683261 311932879411364300506223)
                  ·
                    rfl

theorem cell20_683423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_683423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683423 prefixEnd_683423 := by exact prefixLift 683423
  have htrace : WordTrace (prefixWord ++ tailWord_683423) baseStart_683423 baseEnd_683423 := by
    simpa [prefixWord, tailWord_683423, baseEnd_683423] using wordTrace_append hprefix tailTrace_683423
  have hstable : (prefixWord ++ tailWord_683423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683423).length < 2 ^ (prefixWord ++ tailWord_683423).sum := by decide
  have hdescent : baseEnd_683423 < baseStart_683423 := by decide
  rcases family_descends (prefixWord ++ tailWord_683423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683437 : List Nat := [1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_683437 : Nat := 118140960795 + 683437 * 2 ^ 59
def prefixEnd_683437 : Nat := 4983230072969 + 3 ^ 40 * 683437 * 2
def baseEnd_683437 : Nat := 103979756464280824679833

theorem tailTrace_683437 : CollatzResearch.WordTrace tailWord_683437 prefixEnd_683437 103979756464280824679833 := by
  unfold tailWord_683437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24926995225031945592016565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16617996816687963728011043 24926995225031945592016565)
  ·
    refine ⟨2336905802346744899251553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24926995225031945592016565 2336905802346744899251553)
    ·
      refine ⟨1752679351760058674438665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2336905802346744899251553 1752679351760058674438665)
      ·
        refine ⟨1314509513820044005828999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1752679351760058674438665 1314509513820044005828999)
        ·
          refine ⟨1971764270730066008743499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314509513820044005828999 1971764270730066008743499)
          ·
            refine ⟨2957646406095099013115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971764270730066008743499 2957646406095099013115249)
            ·
              refine ⟨2218234804571324259836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957646406095099013115249 2218234804571324259836437)
              ·
                refine ⟨103979756464280824679833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2218234804571324259836437 103979756464280824679833)
                ·
                  rfl

theorem cell20_683437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_683437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683437 prefixEnd_683437 := by exact prefixLift 683437
  have htrace : WordTrace (prefixWord ++ tailWord_683437) baseStart_683437 baseEnd_683437 := by
    simpa [prefixWord, tailWord_683437, baseEnd_683437] using wordTrace_append hprefix tailTrace_683437
  have hstable : (prefixWord ++ tailWord_683437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683437).length < 2 ^ (prefixWord ++ tailWord_683437).sum := by decide
  have hdescent : baseEnd_683437 < baseStart_683437 := by decide
  rcases family_descends (prefixWord ++ tailWord_683437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683482 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_683482 : Nat := 118140960795 + 683482 * 2 ^ 59
def prefixEnd_683482 : Nat := 4983230072969 + 3 ^ 40 * 683482 * 2
def baseEnd_683482 : Nat := 311959808619022317539315

theorem tailTrace_683482 : CollatzResearch.WordTrace tailWord_683482 prefixEnd_683482 311959808619022317539315 := by
  unfold tailWord_683482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232159127467229569351175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16619091006579278851603133 6232159127467229569351175)
  ·
    refine ⟨9348238691200844354026763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6232159127467229569351175 9348238691200844354026763)
    ·
      refine ⟨14022358036801266531040145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9348238691200844354026763 14022358036801266531040145)
      ·
        refine ⟨10516768527600949898280109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14022358036801266531040145 10516768527600949898280109)
        ·
          refine ⟨3943788197850356211855041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10516768527600949898280109 3943788197850356211855041)
          ·
            refine ⟨2957841148387767158891281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3943788197850356211855041 2957841148387767158891281)
            ·
              refine ⟨2218380861290825369168461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957841148387767158891281 2218380861290825369168461)
              ·
                refine ⟨831892822984059513438173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218380861290825369168461 831892822984059513438173)
                ·
                  refine ⟨311959808619022317539315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 831892822984059513438173 311959808619022317539315)
                  ·
                    rfl

theorem cell20_683482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_683482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683482 prefixEnd_683482 := by exact prefixLift 683482
  have htrace : WordTrace (prefixWord ++ tailWord_683482) baseStart_683482 baseEnd_683482 := by
    simpa [prefixWord, tailWord_683482, baseEnd_683482] using wordTrace_append hprefix tailTrace_683482
  have hstable : (prefixWord ++ tailWord_683482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683482).length < 2 ^ (prefixWord ++ tailWord_683482).sum := by decide
  have hdescent : baseEnd_683482 < baseStart_683482 := by decide
  rcases family_descends (prefixWord ++ tailWord_683482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683489 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_683489 : Nat := 118140960795 + 683489 * 2 ^ 59
def prefixEnd_683489 : Nat := 4983230072969 + 3 ^ 40 * 683489 * 2
def baseEnd_683489 : Nat := 311963003609761404305953

theorem tailTrace_683489 : CollatzResearch.WordTrace tailWord_683489 prefixEnd_683489 311963003609761404305953 := by
  unfold tailWord_683489
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928891820843558472909521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16619261213895705648606347 24928891820843558472909521)
  ·
    refine ⟨18696668865632668854682141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24928891820843558472909521 18696668865632668854682141)
    ·
      refine ⟨7011250824612250820505803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18696668865632668854682141 7011250824612250820505803)
      ·
        refine ⟨10516876236918376230758705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011250824612250820505803 10516876236918376230758705)
        ·
          refine ⟨7887657177688782173069029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10516876236918376230758705 7887657177688782173069029)
          ·
            refine ⟨1478935720816646657450443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7887657177688782173069029 1478935720816646657450443)
            ·
              refine ⟨2218403581224969986175665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478935720816646657450443 2218403581224969986175665)
              ·
                refine ⟨1663802685918727489631749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218403581224969986175665 1663802685918727489631749)
                ·
                  refine ⟨311963003609761404305953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663802685918727489631749 311963003609761404305953)
                  ·
                    rfl

theorem cell20_683489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_683489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683489 prefixEnd_683489 := by exact prefixLift 683489
  have htrace : WordTrace (prefixWord ++ tailWord_683489) baseStart_683489 baseEnd_683489 := by
    simpa [prefixWord, tailWord_683489, baseEnd_683489] using wordTrace_append hprefix tailTrace_683489
  have hstable : (prefixWord ++ tailWord_683489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683489).length < 2 ^ (prefixWord ++ tailWord_683489).sum := by decide
  have hdescent : baseEnd_683489 < baseStart_683489 := by decide
  rcases family_descends (prefixWord ++ tailWord_683489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683527 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_683527 : Nat := 118140960795 + 683527 * 2 ^ 59
def prefixEnd_683527 : Nat := 4983230072969 + 3 ^ 40 * 683527 * 2
def baseEnd_683527 : Nat := 311980347845202161039131

theorem tailTrace_683527 : CollatzResearch.WordTrace tailWord_683527 prefixEnd_683527 311980347845202161039131 := by
  unfold tailWord_683527
  simp only [CollatzResearch.WordTrace]
  refine ⟨24930277794705890962792835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16620185196470593975195223 24930277794705890962792835)
  ·
    refine ⟨37395416692058836444189253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24930277794705890962792835 37395416692058836444189253)
    ·
      refine ⟨7011640629761031833285485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37395416692058836444189253 7011640629761031833285485)
      ·
        refine ⟨2629365236160386937482057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7011640629761031833285485 2629365236160386937482057)
        ·
          refine ⟨1972023927120290203111543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629365236160386937482057 1972023927120290203111543)
          ·
            refine ⟨2958035890680435304667315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972023927120290203111543 2958035890680435304667315)
            ·
              refine ⟨4437053836020652957000973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958035890680435304667315 4437053836020652957000973)
              ·
                refine ⟨1663895188507744858875365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437053836020652957000973 1663895188507744858875365)
                ·
                  refine ⟨311980347845202161039131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1663895188507744858875365 311980347845202161039131)
                  ·
                    rfl

theorem cell20_683527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_683527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683527 prefixEnd_683527 := by exact prefixLift 683527
  have htrace : WordTrace (prefixWord ++ tailWord_683527) baseStart_683527 baseEnd_683527 := by
    simpa [prefixWord, tailWord_683527, baseEnd_683527] using wordTrace_append hprefix tailTrace_683527
  have hstable : (prefixWord ++ tailWord_683527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683527).length < 2 ^ (prefixWord ++ tailWord_683527).sum := by decide
  have hdescent : baseEnd_683527 < baseStart_683527 := by decide
  rcases family_descends (prefixWord ++ tailWord_683527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683596 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_683596 : Nat := 118140960795 + 683596 * 2 ^ 59
def prefixEnd_683596 : Nat := 4983230072969 + 3 ^ 40 * 683596 * 2
def baseEnd_683596 : Nat := 312011841325344587738849

theorem tailTrace_683596 : CollatzResearch.WordTrace tailWord_683596 prefixEnd_683596 312011841325344587738849 := by
  unfold tailWord_683596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466397215727957873527321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16621862954303943831369761 12466397215727957873527321)
  ·
    refine ⟨9349797911795968405145491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12466397215727957873527321 9349797911795968405145491)
    ·
      refine ⟨14024696867693952607718237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349797911795968405145491 14024696867693952607718237)
      ·
        refine ⟨5259261325385232227894339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14024696867693952607718237 5259261325385232227894339)
        ·
          refine ⟨7888891988077848341841509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259261325385232227894339 7888891988077848341841509)
          ·
            refine ⟨1479167247764596564095283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7888891988077848341841509 1479167247764596564095283)
            ·
              refine ⟨2218750871646894846142925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479167247764596564095283 2218750871646894846142925)
              ·
                refine ⟨832031576867585567303597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218750871646894846142925 832031576867585567303597)
                ·
                  refine ⟨312011841325344587738849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832031576867585567303597 312011841325344587738849)
                  ·
                    rfl

theorem cell20_683596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_683596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683596 prefixEnd_683596 := by exact prefixLift 683596
  have htrace : WordTrace (prefixWord ++ tailWord_683596) baseStart_683596 baseEnd_683596 := by
    simpa [prefixWord, tailWord_683596, baseEnd_683596] using wordTrace_append hprefix tailTrace_683596
  have hstable : (prefixWord ++ tailWord_683596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683596).length < 2 ^ (prefixWord ++ tailWord_683596).sum := by decide
  have hdescent : baseEnd_683596 < baseStart_683596 := by decide
  rcases family_descends (prefixWord ++ tailWord_683596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683634 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_683634 : Nat := 118140960795 + 683634 * 2 ^ 59
def prefixEnd_683634 : Nat := 4983230072969 + 3 ^ 40 * 683634 * 2
def baseEnd_683634 : Nat := 312029185560785344472027

theorem tailTrace_683634 : CollatzResearch.WordTrace tailWord_683634 prefixEnd_683634 312029185560785344472027 := by
  unfold tailWord_683634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233545101329562059234489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16622786936878832157958637 6233545101329562059234489)
  ·
    refine ⟨4675158825997171544425867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6233545101329562059234489 4675158825997171544425867)
    ·
      refine ⟨7012738238995757316638801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4675158825997171544425867 7012738238995757316638801)
      ·
        refine ⟨5259553679246817987479101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7012738238995757316638801 5259553679246817987479101)
        ·
          refine ⟨1972332629717556745304663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5259553679246817987479101 1972332629717556745304663)
          ·
            refine ⟨2958498944576335117956995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972332629717556745304663 2958498944576335117956995)
            ·
              refine ⟨4437748416864502676935493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958498944576335117956995 4437748416864502676935493)
              ·
                refine ⟨832077828162094251925405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4437748416864502676935493 832077828162094251925405)
                ·
                  refine ⟨312029185560785344472027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832077828162094251925405 312029185560785344472027)
                  ·
                    rfl

theorem cell20_683634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_683634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683634 prefixEnd_683634 := by exact prefixLift 683634
  have htrace : WordTrace (prefixWord ++ tailWord_683634) baseStart_683634 baseEnd_683634 := by
    simpa [prefixWord, tailWord_683634, baseEnd_683634] using wordTrace_append hprefix tailTrace_683634
  have hstable : (prefixWord ++ tailWord_683634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683634).length < 2 ^ (prefixWord ++ tailWord_683634).sum := by decide
  have hdescent : baseEnd_683634 < baseStart_683634 := by decide
  rcases family_descends (prefixWord ++ tailWord_683634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683637 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 2]
def baseStart_683637 : Nat := 118140960795 + 683637 * 2 ^ 59
def prefixEnd_683637 : Nat := 4983230072969 + 3 ^ 40 * 683637 * 2
def baseEnd_683637 : Nat := 312030554842530667372015

theorem tailTrace_683637 : CollatzResearch.WordTrace tailWord_683637 prefixEnd_683637 312030554842530667372015 := by
  unfold tailWord_683637
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934289824307379749297165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16622859882871586499531443 24934289824307379749297165)
  ·
    refine ⟨9350358684115267405986437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24934289824307379749297165 9350358684115267405986437)
    ·
      refine ⟨1753192253271612638622457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9350358684115267405986437 1753192253271612638622457)
      ·
        refine ⟨1314894189953709478966843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1753192253271612638622457 1314894189953709478966843)
        ·
          refine ⟨1972341284930564218450265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314894189953709478966843 1972341284930564218450265)
          ·
            refine ⟨1479255963697923163837699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1972341284930564218450265 1479255963697923163837699)
            ·
              refine ⟨2218883945546884745756549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479255963697923163837699 2218883945546884745756549)
              ·
                refine ⟨416040739790040889829353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2218883945546884745756549 416040739790040889829353)
                ·
                  refine ⟨312030554842530667372015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416040739790040889829353 312030554842530667372015)
                  ·
                    rfl

theorem cell20_683637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_683637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683637 prefixEnd_683637 := by exact prefixLift 683637
  have htrace : WordTrace (prefixWord ++ tailWord_683637) baseStart_683637 baseEnd_683637 := by
    simpa [prefixWord, tailWord_683637, baseEnd_683637] using wordTrace_append hprefix tailTrace_683637
  have hstable : (prefixWord ++ tailWord_683637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683637).length < 2 ^ (prefixWord ++ tailWord_683637).sum := by decide
  have hdescent : baseEnd_683637 < baseStart_683637 := by decide
  rcases family_descends (prefixWord ++ tailWord_683637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683669 : List Nat := [1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_683669 : Nat := 118140960795 + 683669 * 2 ^ 59
def prefixEnd_683669 : Nat := 4983230072969 + 3 ^ 40 * 683669 * 2
def baseEnd_683669 : Nat := 104015053504826926101739

theorem tailTrace_683669 : CollatzResearch.WordTrace tailWord_683669 prefixEnd_683669 104015053504826926101739 := by
  unfold tailWord_683669
  simp only [CollatzResearch.WordTrace]
  refine ⟨24935456960191449214462061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16623637973460966142974707 24935456960191449214462061)
  ·
    refine ⟨9350796360071793455423273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24935456960191449214462061 9350796360071793455423273)
    ·
      refine ⟨7013097270053845091567455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9350796360071793455423273 7013097270053845091567455)
      ·
        refine ⟨10519645905080767637351183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013097270053845091567455 10519645905080767637351183)
        ·
          refine ⟨15779468857621151456026775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10519645905080767637351183 15779468857621151456026775)
          ·
            refine ⟨23669203286431727184040163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15779468857621151456026775 23669203286431727184040163)
            ·
              refine ⟨35503804929647590776060245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23669203286431727184040163 35503804929647590776060245)
              ·
                refine ⟨104015053504826926101739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35503804929647590776060245 104015053504826926101739)
                ·
                  rfl

theorem cell20_683669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_683669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683669 prefixEnd_683669 := by exact prefixLift 683669
  have htrace : WordTrace (prefixWord ++ tailWord_683669) baseStart_683669 baseEnd_683669 := by
    simpa [prefixWord, tailWord_683669, baseEnd_683669] using wordTrace_append hprefix tailTrace_683669
  have hstable : (prefixWord ++ tailWord_683669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683669).length < 2 ^ (prefixWord ++ tailWord_683669).sum := by decide
  have hdescent : baseEnd_683669 < baseStart_683669 := by decide
  rcases family_descends (prefixWord ++ tailWord_683669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683751 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_683751 : Nat := 118140960795 + 683751 * 2 ^ 59
def prefixEnd_683751 : Nat := 4983230072969 + 3 ^ 40 * 683751 * 2
def baseEnd_683751 : Nat := 312082587548852937571549

theorem tailTrace_683751 : CollatzResearch.WordTrace tailWord_683751 prefixEnd_683751 312082587548852937571549 := by
  unfold tailWord_683751
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938447745894377218947107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16625631830596251479298071 24938447745894377218947107)
  ·
    refine ⟨37407671618841565828420661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938447745894377218947107 37407671618841565828420661)
    ·
      refine ⟨3506969214266396796414437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37407671618841565828420661 3506969214266396796414437)
      ·
        refine ⟨657556727674949399327707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3506969214266396796414437 657556727674949399327707)
        ·
          refine ⟨986335091512424098991561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657556727674949399327707 986335091512424098991561)
          ·
            refine ⟨739751318634318074243671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986335091512424098991561 739751318634318074243671)
            ·
              refine ⟨1109626977951477111365507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739751318634318074243671 1109626977951477111365507)
              ·
                refine ⟨1664440466927215667048261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109626977951477111365507 1664440466927215667048261)
                ·
                  refine ⟨312082587548852937571549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664440466927215667048261 312082587548852937571549)
                  ·
                    rfl

theorem cell20_683751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_683751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683751 prefixEnd_683751 := by exact prefixLift 683751
  have htrace : WordTrace (prefixWord ++ tailWord_683751) baseStart_683751 baseEnd_683751 := by
    simpa [prefixWord, tailWord_683751, baseEnd_683751] using wordTrace_append hprefix tailTrace_683751
  have hstable : (prefixWord ++ tailWord_683751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683751).length < 2 ^ (prefixWord ++ tailWord_683751).sum := by decide
  have hdescent : baseEnd_683751 < baseStart_683751 := by decide
  rcases family_descends (prefixWord ++ tailWord_683751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683755 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 2]
def baseStart_683755 : Nat := 118140960795 + 683755 * 2 ^ 59
def prefixEnd_683755 : Nat := 4983230072969 + 3 ^ 40 * 683755 * 2
def baseEnd_683755 : Nat := 312084413257846701438199

theorem tailTrace_683755 : CollatzResearch.WordTrace tailWord_683755 prefixEnd_683755 312084413257846701438199 := by
  unfold tailWord_683755
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938593637879885902092719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16625729091919923934728479 24938593637879885902092719)
  ·
    refine ⟨37407890456819828853139079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938593637879885902092719 37407890456819828853139079)
    ·
      refine ⟨56111835685229743279708619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37407890456819828853139079 56111835685229743279708619)
      ·
        refine ⟨84167753527844614919562929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56111835685229743279708619 84167753527844614919562929)
        ·
          refine ⟨63125815145883461189672197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84167753527844614919562929 63125815145883461189672197)
          ·
            refine ⟨11836090339853148973063537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63125815145883461189672197 11836090339853148973063537)
            ·
              refine ⟨8877067754889861729797653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11836090339853148973063537 8877067754889861729797653)
              ·
                refine ⟨416112551010462268584265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8877067754889861729797653 416112551010462268584265)
                ·
                  refine ⟨312084413257846701438199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416112551010462268584265 312084413257846701438199)
                  ·
                    rfl

theorem cell20_683755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 2].length) (baseStart_683755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683755 prefixEnd_683755 := by exact prefixLift 683755
  have htrace : WordTrace (prefixWord ++ tailWord_683755) baseStart_683755 baseEnd_683755 := by
    simpa [prefixWord, tailWord_683755, baseEnd_683755] using wordTrace_append hprefix tailTrace_683755
  have hstable : (prefixWord ++ tailWord_683755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683755).length < 2 ^ (prefixWord ++ tailWord_683755).sum := by decide
  have hdescent : baseEnd_683755 < baseStart_683755 := by decide
  rcases family_descends (prefixWord ++ tailWord_683755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683762 : List Nat := [3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_683762 : Nat := 118140960795 + 683762 * 2 ^ 59
def prefixEnd_683762 : Nat := 4983230072969 + 3 ^ 40 * 683762 * 2
def baseEnd_683762 : Nat := 104029202749528596068279

theorem tailTrace_683762 : CollatzResearch.WordTrace tailWord_683762 prefixEnd_683762 104029202749528596068279 := by
  unfold tailWord_683762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234712237213631524399385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16625899299236350731731693 6234712237213631524399385)
  ·
    refine ⟨4676034177910223643299539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6234712237213631524399385 4676034177910223643299539)
    ·
      refine ⟨7014051266865335464949309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676034177910223643299539 7014051266865335464949309)
      ·
        refine ⟨2630269225074500799355991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7014051266865335464949309 2630269225074500799355991)
        ·
          refine ⟨3945403837611751199033987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630269225074500799355991 3945403837611751199033987)
          ·
            refine ⟨5918105756417626798550981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945403837611751199033987 5918105756417626798550981)
            ·
              refine ⟨1109644829328305024728309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5918105756417626798550981 1109644829328305024728309)
              ·
                refine ⟨104029202749528596068279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1109644829328305024728309 104029202749528596068279)
                ·
                  rfl

theorem cell20_683762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_683762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683762 prefixEnd_683762 := by exact prefixLift 683762
  have htrace : WordTrace (prefixWord ++ tailWord_683762) baseStart_683762 baseEnd_683762 := by
    simpa [prefixWord, tailWord_683762, baseEnd_683762] using wordTrace_append hprefix tailTrace_683762
  have hstable : (prefixWord ++ tailWord_683762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683762).length < 2 ^ (prefixWord ++ tailWord_683762).sum := by decide
  have hdescent : baseEnd_683762 < baseStart_683762 := by decide
  rcases family_descends (prefixWord ++ tailWord_683762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683793 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 2]
def baseStart_683793 : Nat := 118140960795 + 683793 * 2 ^ 59
def prefixEnd_683793 : Nat := 4983230072969 + 3 ^ 40 * 683793 * 2
def baseEnd_683793 : Nat := 312101757493287458171377

theorem tailTrace_683793 : CollatzResearch.WordTrace tailWord_683793 prefixEnd_683793 312101757493287458171377 := by
  unfold tailWord_683793
  simp only [CollatzResearch.WordTrace]
  refine ⟨24939979611742218391976033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16626653074494812261317355 24939979611742218391976033)
  ·
    refine ⟨18704984708806663793982025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24939979611742218391976033 18704984708806663793982025)
    ·
      refine ⟨14028738531604997845486519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18704984708806663793982025 14028738531604997845486519)
      ·
        refine ⟨21043107797407496768229779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14028738531604997845486519 21043107797407496768229779)
        ·
          refine ⟨31564661696111245152344669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21043107797407496768229779 31564661696111245152344669)
          ·
            refine ⟨11836748136041716932129251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31564661696111245152344669 11836748136041716932129251)
            ·
              refine ⟨17755122204062575398193877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836748136041716932129251 17755122204062575398193877)
              ·
                refine ⟨416135676657716610895169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17755122204062575398193877 416135676657716610895169)
                ·
                  refine ⟨312101757493287458171377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416135676657716610895169 312101757493287458171377)
                  ·
                    rfl

theorem cell20_683793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_683793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683793 prefixEnd_683793 := by exact prefixLift 683793
  have htrace : WordTrace (prefixWord ++ tailWord_683793) baseStart_683793 baseEnd_683793 := by
    simpa [prefixWord, tailWord_683793, baseEnd_683793] using wordTrace_append hprefix tailTrace_683793
  have hstable : (prefixWord ++ tailWord_683793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683793).length < 2 ^ (prefixWord ++ tailWord_683793).sum := by decide
  have hdescent : baseEnd_683793 < baseStart_683793 := by decide
  rcases family_descends (prefixWord ++ tailWord_683793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683796 : List Nat := [2, 4, 4, 1, 1, 8]
def baseStart_683796 : Nat := 118140960795 + 683796 * 2 ^ 59
def prefixEnd_683796 : Nat := 4983230072969 + 3 ^ 40 * 683796 * 2
def baseEnd_683796 : Nat := 11559375065741954854495

theorem tailTrace_683796 : CollatzResearch.WordTrace tailWord_683796 prefixEnd_683796 11559375065741954854495 := by
  unfold tailWord_683796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470044515365674952167621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16626726020487566602890161 12470044515365674952167621)
  ·
    refine ⟨2338133346631064053531429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12470044515365674952167621 2338133346631064053531429)
    ·
      refine ⟨438400002493324510037143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2338133346631064053531429 438400002493324510037143)
      ·
        refine ⟨657600003739986765055715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438400002493324510037143 657600003739986765055715)
        ·
          refine ⟨986400005609980147583573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657600003739986765055715 986400005609980147583573)
          ·
            refine ⟨11559375065741954854495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 986400005609980147583573 11559375065741954854495)
            ·
              rfl

theorem cell20_683796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 8].length) (baseStart_683796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683796 prefixEnd_683796 := by exact prefixLift 683796
  have htrace : WordTrace (prefixWord ++ tailWord_683796) baseStart_683796 baseEnd_683796 := by
    simpa [prefixWord, tailWord_683796, baseEnd_683796] using wordTrace_append hprefix tailTrace_683796
  have hstable : (prefixWord ++ tailWord_683796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683796).length < 2 ^ (prefixWord ++ tailWord_683796).sum := by decide
  have hdescent : baseEnd_683796 < baseStart_683796 := by decide
  rcases family_descends (prefixWord ++ tailWord_683796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683810 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_683810 : Nat := 118140960795 + 683810 * 2 ^ 59
def prefixEnd_683810 : Nat := 4983230072969 + 3 ^ 40 * 683810 * 2
def baseEnd_683810 : Nat := 312109516756510954604641

theorem tailTrace_683810 : CollatzResearch.WordTrace tailWord_683810 prefixEnd_683810 312109516756510954604641 := by
  unfold tailWord_683810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235149913170157573836221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16627066435120420196896589 6235149913170157573836221)
  ·
    refine ⟨2338181217438809090188583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6235149913170157573836221 2338181217438809090188583)
    ·
      refine ⟨3507271826158213635282875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2338181217438809090188583 3507271826158213635282875)
      ·
        refine ⟨5260907739237320452924313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507271826158213635282875 5260907739237320452924313)
        ·
          refine ⟨3945680804427990339693235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5260907739237320452924313 3945680804427990339693235)
          ·
            refine ⟨5918521206641985509539853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945680804427990339693235 5918521206641985509539853)
            ·
              refine ⟨2219445452490744566077445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5918521206641985509539853 2219445452490744566077445)
              ·
                refine ⟨416146022342014606139521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2219445452490744566077445 416146022342014606139521)
                ·
                  refine ⟨312109516756510954604641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416146022342014606139521 312109516756510954604641)
                  ·
                    rfl

theorem cell20_683810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_683810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683810 prefixEnd_683810 := by exact prefixLift 683810
  have htrace : WordTrace (prefixWord ++ tailWord_683810) baseStart_683810 baseEnd_683810 := by
    simpa [prefixWord, tailWord_683810, baseEnd_683810] using wordTrace_append hprefix tailTrace_683810
  have hstable : (prefixWord ++ tailWord_683810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683810).length < 2 ^ (prefixWord ++ tailWord_683810).sum := by decide
  have hdescent : baseEnd_683810 < baseStart_683810 := by decide
  rcases family_descends (prefixWord ++ tailWord_683810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683848 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 2]
def baseStart_683848 : Nat := 118140960795 + 683848 * 2 ^ 59
def prefixEnd_683848 : Nat := 4983230072969 + 3 ^ 40 * 683848 * 2
def baseEnd_683848 : Nat := 312126860991951711337819

theorem tailTrace_683848 : CollatzResearch.WordTrace tailWord_683848 prefixEnd_683848 312126860991951711337819 := by
  unfold tailWord_683848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470992813271481392614099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16627990417695308523485465 12470992813271481392614099)
  ·
    refine ⟨18706489219907222088921149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12470992813271481392614099 18706489219907222088921149)
    ·
      refine ⟨7014933457465208283345431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18706489219907222088921149 7014933457465208283345431)
      ·
        refine ⟨10522400186197812425018147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7014933457465208283345431 10522400186197812425018147)
        ·
          refine ⟨15783600279296718637527221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10522400186197812425018147 15783600279296718637527221)
          ·
            refine ⟨1479712526184067372268177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15783600279296718637527221 1479712526184067372268177)
            ·
              refine ⟨1109784394638050529201133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479712526184067372268177 1109784394638050529201133)
              ·
                refine ⟨416169147989268948450425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109784394638050529201133 416169147989268948450425)
                ·
                  refine ⟨312126860991951711337819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416169147989268948450425 312126860991951711337819)
                  ·
                    rfl

theorem cell20_683848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_683848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683848 prefixEnd_683848 := by exact prefixLift 683848
  have htrace : WordTrace (prefixWord ++ tailWord_683848) baseStart_683848 baseEnd_683848 := by
    simpa [prefixWord, tailWord_683848, baseEnd_683848] using wordTrace_append hprefix tailTrace_683848
  have hstable : (prefixWord ++ tailWord_683848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683848).length < 2 ^ (prefixWord ++ tailWord_683848).sum := by decide
  have hdescent : baseEnd_683848 < baseStart_683848 := by decide
  rcases family_descends (prefixWord ++ tailWord_683848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683897 : List Nat := [1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_683897 : Nat := 118140960795 + 683897 * 2 ^ 59
def prefixEnd_683897 : Nat := 4983230072969 + 3 ^ 40 * 683897 * 2
def baseEnd_683897 : Nat := 104049741975708439568095

theorem tailTrace_683897 : CollatzResearch.WordTrace tailWord_683897 prefixEnd_683897 104049741975708439568095 := by
  unfold tailWord_683897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943772803365444153761945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16629181868910296102507963 24943772803365444153761945)
  ·
    refine ⟨18707829602524083115321459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24943772803365444153761945 18707829602524083115321459)
    ·
      refine ⟨28061744403786124672982189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18707829602524083115321459 28061744403786124672982189)
      ·
        refine ⟨10523154151419796752368321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28061744403786124672982189 10523154151419796752368321)
        ·
          refine ⟨7892365613564847564276241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10523154151419796752368321 7892365613564847564276241)
          ·
            refine ⟨5919274210173635673207181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892365613564847564276241 5919274210173635673207181)
            ·
              refine ⟨2219727828815113377452693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5919274210173635673207181 2219727828815113377452693)
              ·
                refine ⟨104049741975708439568095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2219727828815113377452693 104049741975708439568095)
                ·
                  rfl

theorem cell20_683897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_683897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683897 prefixEnd_683897 := by exact prefixLift 683897
  have htrace : WordTrace (prefixWord ++ tailWord_683897) baseStart_683897 baseEnd_683897 := by
    simpa [prefixWord, tailWord_683897, baseEnd_683897] using wordTrace_append hprefix tailTrace_683897
  have hstable : (prefixWord ++ tailWord_683897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683897).length < 2 ^ (prefixWord ++ tailWord_683897).sum := by decide
  have hdescent : baseEnd_683897 < baseStart_683897 := by decide
  rcases family_descends (prefixWord ++ tailWord_683897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683904 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_683904 : Nat := 118140960795 + 683904 * 2 ^ 59
def prefixEnd_683904 : Nat := 4983230072969 + 3 ^ 40 * 683904 * 2
def baseEnd_683904 : Nat := 312152420917864405470923

theorem tailTrace_683904 : CollatzResearch.WordTrace tailWord_683904 prefixEnd_683904 312152420917864405470923 := by
  unfold tailWord_683904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472014057170042174633383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16629352076226722899511177 12472014057170042174633383)
  ·
    refine ⟨18708021085755063261950075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472014057170042174633383 18708021085755063261950075)
    ·
      refine ⟨28062031628632594892925113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18708021085755063261950075 28062031628632594892925113)
      ·
        refine ⟨21046523721474446169693835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28062031628632594892925113 21046523721474446169693835)
        ·
          refine ⟨31569785582211669254540753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21046523721474446169693835 31569785582211669254540753)
          ·
            refine ⟨23677339186658751940905565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31569785582211669254540753 23677339186658751940905565)
            ·
              refine ⟨8879002194997031977839587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23677339186658751940905565 8879002194997031977839587)
              ·
                refine ⟨13318503292495547966759381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8879002194997031977839587 13318503292495547966759381)
                ·
                  refine ⟨312152420917864405470923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13318503292495547966759381 312152420917864405470923)
                  ·
                    rfl

theorem cell20_683904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_683904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683904 prefixEnd_683904 := by exact prefixLift 683904
  have htrace : WordTrace (prefixWord ++ tailWord_683904) baseStart_683904 baseEnd_683904 := by
    simpa [prefixWord, tailWord_683904, baseEnd_683904] using wordTrace_append hprefix tailTrace_683904
  have hstable : (prefixWord ++ tailWord_683904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683904).length < 2 ^ (prefixWord ++ tailWord_683904).sum := by decide
  have hdescent : baseEnd_683904 < baseStart_683904 := by decide
  rcases family_descends (prefixWord ++ tailWord_683904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683924 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_683924 : Nat := 118140960795 + 683924 * 2 ^ 59
def prefixEnd_683924 : Nat := 4983230072969 + 3 ^ 40 * 683924 * 2
def baseEnd_683924 : Nat := 312161549462833224804175

theorem tailTrace_683924 : CollatzResearch.WordTrace tailWord_683924 prefixEnd_683924 312161549462833224804175 := by
  unfold tailWord_683924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472378787133813882497413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16629838382845085176663217 12472378787133813882497413)
  ·
    refine ⟨2338571022587590102968265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12472378787133813882497413 2338571022587590102968265)
    ·
      refine ⟨1753928266940692577226199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338571022587590102968265 1753928266940692577226199)
      ·
        refine ⟨2630892400411038865839299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753928266940692577226199 2630892400411038865839299)
        ·
          refine ⟨3946338600616558298758949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630892400411038865839299 3946338600616558298758949)
          ·
            refine ⟨739938487615604681017303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3946338600616558298758949 739938487615604681017303)
            ·
              refine ⟨1109907731423407021525955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739938487615604681017303 1109907731423407021525955)
              ·
                refine ⟨1664861597135110532288933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109907731423407021525955 1664861597135110532288933)
                ·
                  refine ⟨312161549462833224804175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1664861597135110532288933 312161549462833224804175)
                  ·
                    rfl

theorem cell20_683924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_683924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683924 prefixEnd_683924 := by exact prefixLift 683924
  have htrace : WordTrace (prefixWord ++ tailWord_683924) baseStart_683924 baseEnd_683924 := by
    simpa [prefixWord, tailWord_683924, baseEnd_683924] using wordTrace_append hprefix tailTrace_683924
  have hstable : (prefixWord ++ tailWord_683924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683924).length < 2 ^ (prefixWord ++ tailWord_683924).sum := by decide
  have hdescent : baseEnd_683924 < baseStart_683924 := by decide
  rcases family_descends (prefixWord ++ tailWord_683924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683934 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_683934 : Nat := 118140960795 + 683934 * 2 ^ 59
def prefixEnd_683934 : Nat := 4983230072969 + 3 ^ 40 * 683934 * 2
def baseEnd_683934 : Nat := 312166113735317634470801

theorem tailTrace_683934 : CollatzResearch.WordTrace tailWord_683934 prefixEnd_683934 312166113735317634470801 := by
  unfold tailWord_683934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118140288028924934107357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16630081536154266315239237 3118140288028924934107357)
  ·
    refine ⟨1169302608010846850290259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3118140288028924934107357 1169302608010846850290259)
    ·
      refine ⟨1753953912016270275435389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169302608010846850290259 1753953912016270275435389)
      ·
        refine ⟨657732717006101353288271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1753953912016270275435389 657732717006101353288271)
        ·
          refine ⟨986599075509152029932407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657732717006101353288271 986599075509152029932407)
          ·
            refine ⟨1479898613263728044898611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986599075509152029932407 1479898613263728044898611)
            ·
              refine ⟨2219847919895592067347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479898613263728044898611 2219847919895592067347917)
              ·
                refine ⟨832442969960847025255469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2219847919895592067347917 832442969960847025255469)
                ·
                  refine ⟨312166113735317634470801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832442969960847025255469 312166113735317634470801)
                  ·
                    rfl

theorem cell20_683934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_683934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683934 prefixEnd_683934 := by exact prefixLift 683934
  have htrace : WordTrace (prefixWord ++ tailWord_683934) baseStart_683934 baseEnd_683934 := by
    simpa [prefixWord, tailWord_683934, baseEnd_683934] using wordTrace_append hprefix tailTrace_683934
  have hstable : (prefixWord ++ tailWord_683934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683934).length < 2 ^ (prefixWord ++ tailWord_683934).sum := by decide
  have hdescent : baseEnd_683934 < baseStart_683934 := by decide
  rcases family_descends (prefixWord ++ tailWord_683934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683976 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_683976 : Nat := 118140960795 + 683976 * 2 ^ 59
def prefixEnd_683976 : Nat := 4983230072969 + 3 ^ 40 * 683976 * 2
def baseEnd_683976 : Nat := 312185283679752155070629

theorem tailTrace_683976 : CollatzResearch.WordTrace tailWord_683976 prefixEnd_683976 312185283679752155070629 := by
  unfold tailWord_683976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473327085039620322943891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16631102780052827097258521 12473327085039620322943891)
  ·
    refine ⟨18709990627559430484415837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473327085039620322943891 18709990627559430484415837)
    ·
      refine ⟨7016246485334786431655939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18709990627559430484415837 7016246485334786431655939)
      ·
        refine ⟨10524369728002179647483909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7016246485334786431655939 10524369728002179647483909)
        ·
          refine ⟨1973319324000408683903233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10524369728002179647483909 1973319324000408683903233)
          ·
            refine ⟨1479989493000306512927425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973319324000408683903233 1479989493000306512927425)
            ·
              refine ⟨1109992119750229884695569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479989493000306512927425 1109992119750229884695569)
              ·
                refine ⟨832494089812672413521677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109992119750229884695569 832494089812672413521677)
                ·
                  refine ⟨312185283679752155070629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832494089812672413521677 312185283679752155070629)
                  ·
                    rfl

theorem cell20_683976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_683976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683976 prefixEnd_683976 := by exact prefixLift 683976
  have htrace : WordTrace (prefixWord ++ tailWord_683976) baseStart_683976 baseEnd_683976 := by
    simpa [prefixWord, tailWord_683976, baseEnd_683976] using wordTrace_append hprefix tailTrace_683976
  have hstable : (prefixWord ++ tailWord_683976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683976).length < 2 ^ (prefixWord ++ tailWord_683976).sum := by decide
  have hdescent : baseEnd_683976 < baseStart_683976 := by decide
  rcases family_descends (prefixWord ++ tailWord_683976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683983 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 2]
def baseStart_683983 : Nat := 118140960795 + 683983 * 2 ^ 59
def prefixEnd_683983 : Nat := 4983230072969 + 3 ^ 40 * 683983 * 2
def baseEnd_683983 : Nat := 312188478670491241837267

theorem tailTrace_683983 : CollatzResearch.WordTrace tailWord_683983 prefixEnd_683983 312188478670491241837267 := by
  unfold tailWord_683983
  simp only [CollatzResearch.WordTrace]
  refine ⟨24946909481053880841392603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16631272987369253894261735 24946909481053880841392603)
  ·
    refine ⟨37420364221580821262088905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24946909481053880841392603 37420364221580821262088905)
    ·
      refine ⟨28065273166185615946566679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37420364221580821262088905 28065273166185615946566679)
      ·
        refine ⟨42097909749278423919850019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28065273166185615946566679 42097909749278423919850019)
        ·
          refine ⟨63146864623917635879775029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42097909749278423919850019 63146864623917635879775029)
          ·
            refine ⟨5920018558492278363728909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63146864623917635879775029 5920018558492278363728909)
            ·
              refine ⟨2220006959434604386398341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5920018558492278363728909 2220006959434604386398341)
              ·
                refine ⟨416251304893988322449689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2220006959434604386398341 416251304893988322449689)
                ·
                  refine ⟨312188478670491241837267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416251304893988322449689 312188478670491241837267)
                  ·
                    rfl

theorem cell20_683983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2].length) (baseStart_683983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683983 prefixEnd_683983 := by exact prefixLift 683983
  have htrace : WordTrace (prefixWord ++ tailWord_683983) baseStart_683983 baseEnd_683983 := by
    simpa [prefixWord, tailWord_683983, baseEnd_683983] using wordTrace_append hprefix tailTrace_683983
  have hstable : (prefixWord ++ tailWord_683983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683983).length < 2 ^ (prefixWord ++ tailWord_683983).sum := by decide
  have hdescent : baseEnd_683983 < baseStart_683983 := by decide
  rcases family_descends (prefixWord ++ tailWord_683983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_683986 : List Nat := [3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_683986 : Nat := 118140960795 + 683986 * 2 ^ 59
def prefixEnd_683986 : Nat := 4983230072969 + 3 ^ 40 * 683986 * 2
def baseEnd_683986 : Nat := 104063282650745521579085

theorem tailTrace_683986 : CollatzResearch.WordTrace tailWord_683986 prefixEnd_683986 104063282650745521579085 := by
  unfold tailWord_683986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6236754725010753088437953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16631345933362008235834541 6236754725010753088437953)
  ·
    refine ⟨4677566043758064816328465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6236754725010753088437953 4677566043758064816328465)
    ·
      refine ⟨3508174532818548612246349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4677566043758064816328465 3508174532818548612246349)
      ·
        refine ⟨1315565449806955729592381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3508174532818548612246349 1315565449806955729592381)
        ·
          refine ⟨493337043677608398597143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1315565449806955729592381 493337043677608398597143)
          ·
            refine ⟨740005565516412597895715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493337043677608398597143 740005565516412597895715)
            ·
              refine ⟨1110008348274618896843573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740005565516412597895715 1110008348274618896843573)
              ·
                refine ⟨104063282650745521579085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1110008348274618896843573 104063282650745521579085)
                ·
                  rfl

theorem cell20_683986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_683986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_683986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_683986 prefixEnd_683986 := by exact prefixLift 683986
  have htrace : WordTrace (prefixWord ++ tailWord_683986) baseStart_683986 baseEnd_683986 := by
    simpa [prefixWord, tailWord_683986, baseEnd_683986] using wordTrace_append hprefix tailTrace_683986
  have hstable : (prefixWord ++ tailWord_683986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_683986).length < 2 ^ (prefixWord ++ tailWord_683986).sum := by decide
  have hdescent : baseEnd_683986 < baseStart_683986 := by decide
  rcases family_descends (prefixWord ++ tailWord_683986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684004 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_684004 : Nat := 118140960795 + 684004 * 2 ^ 59
def prefixEnd_684004 : Nat := 4983230072969 + 3 ^ 40 * 684004 * 2
def baseEnd_684004 : Nat := 312198063642708502137181

theorem tailTrace_684004 : CollatzResearch.WordTrace tailWord_684004 prefixEnd_684004 312198063642708502137181 := by
  unfold tailWord_684004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473837706988900713953533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16631783609318534285271377 12473837706988900713953533)
  ·
    refine ⟨4677689140120837767732575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12473837706988900713953533 4677689140120837767732575)
    ·
      refine ⟨7016533710181256651598863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4677689140120837767732575 7016533710181256651598863)
      ·
        refine ⟨10524800565271884977398295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7016533710181256651598863 10524800565271884977398295)
        ·
          refine ⟨15787200847907827466097443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10524800565271884977398295 15787200847907827466097443)
          ·
            refine ⟨23680801271861741199146165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15787200847907827466097443 23680801271861741199146165)
            ·
              refine ⟨2220075119237038237419953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23680801271861741199146165 2220075119237038237419953)
              ·
                refine ⟨1665056339427778678064965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220075119237038237419953 1665056339427778678064965)
                ·
                  refine ⟨312198063642708502137181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665056339427778678064965 312198063642708502137181)
                  ·
                    rfl

theorem cell20_684004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_684004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684004 prefixEnd_684004 := by exact prefixLift 684004
  have htrace : WordTrace (prefixWord ++ tailWord_684004) baseStart_684004 baseEnd_684004 := by
    simpa [prefixWord, tailWord_684004, baseEnd_684004] using wordTrace_append hprefix tailTrace_684004
  have hstable : (prefixWord ++ tailWord_684004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684004).length < 2 ^ (prefixWord ++ tailWord_684004).sum := by decide
  have hdescent : baseEnd_684004 < baseStart_684004 := by decide
  rcases family_descends (prefixWord ++ tailWord_684004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684007 : List Nat := [1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_684007 : Nat := 118140960795 + 684007 * 2 ^ 59
def prefixEnd_684007 : Nat := 4983230072969 + 3 ^ 40 * 684007 * 2
def baseEnd_684007 : Nat := 104066477641484608345723

theorem tailTrace_684007 : CollatzResearch.WordTrace tailWord_684007 prefixEnd_684007 104066477641484608345723 := by
  unfold tailWord_684007
  simp only [CollatzResearch.WordTrace]
  refine ⟨24947784832966932940266275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16631856555311288626844183 24947784832966932940266275)
  ·
    refine ⟨37421677249450399410399413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24947784832966932940266275 37421677249450399410399413)
    ·
      refine ⟨3508282242135974944724945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37421677249450399410399413 3508282242135974944724945)
      ·
        refine ⟨2631211681601981208543709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3508282242135974944724945 2631211681601981208543709)
        ·
          refine ⟨986704380600742953203891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2631211681601981208543709 986704380600742953203891)
          ·
            refine ⟨1480056570901114429805837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986704380600742953203891 1480056570901114429805837)
            ·
              refine ⟨555021214087917911177189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1480056570901114429805837 555021214087917911177189)
              ·
                refine ⟨104066477641484608345723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555021214087917911177189 104066477641484608345723)
                ·
                  rfl

theorem cell20_684007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_684007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684007 prefixEnd_684007 := by exact prefixLift 684007
  have htrace : WordTrace (prefixWord ++ tailWord_684007) baseStart_684007 baseEnd_684007 := by
    simpa [prefixWord, tailWord_684007, baseEnd_684007] using wordTrace_append hprefix tailTrace_684007
  have hstable : (prefixWord ++ tailWord_684007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684007).length < 2 ^ (prefixWord ++ tailWord_684007).sum := by decide
  have hdescent : baseEnd_684007 < baseStart_684007 := by decide
  rcases family_descends (prefixWord ++ tailWord_684007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684072 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_684072 : Nat := 118140960795 + 684072 * 2 ^ 59
def prefixEnd_684072 : Nat := 4983230072969 + 3 ^ 40 * 684072 * 2
def baseEnd_684072 : Nat := 312229100695602487870237

theorem tailTrace_684072 : CollatzResearch.WordTrace tailWord_684072 prefixEnd_684072 312229100695602487870237 := by
  unfold tailWord_684072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12475077788865724520691235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16633437051820966027588313 12475077788865724520691235)
  ·
    refine ⟨18712616683298586781036853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12475077788865724520691235 18712616683298586781036853)
    ·
      refine ⟨1754307814059242510722205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18712616683298586781036853 1754307814059242510722205)
      ·
        refine ⟨657865430272215941520827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1754307814059242510722205 657865430272215941520827)
        ·
          refine ⟨986798145408323912281241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657865430272215941520827 986798145408323912281241)
          ·
            refine ⟨740098609056242934210931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986798145408323912281241 740098609056242934210931)
            ·
              refine ⟨1110147913584364401316397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740098609056242934210931 1110147913584364401316397)
              ·
                refine ⟨416305467594136650493649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110147913584364401316397 416305467594136650493649)
                ·
                  refine ⟨312229100695602487870237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416305467594136650493649 312229100695602487870237)
                  ·
                    rfl

theorem cell20_684072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_684072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684072 prefixEnd_684072 := by exact prefixLift 684072
  have htrace : WordTrace (prefixWord ++ tailWord_684072) baseStart_684072 baseEnd_684072 := by
    simpa [prefixWord, tailWord_684072, baseEnd_684072] using wordTrace_append hprefix tailTrace_684072
  have hstable : (prefixWord ++ tailWord_684072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684072).length < 2 ^ (prefixWord ++ tailWord_684072).sum := by decide
  have hdescent : baseEnd_684072 < baseStart_684072 := by decide
  rcases family_descends (prefixWord ++ tailWord_684072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684097 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_684097 : Nat := 118140960795 + 684097 * 2 ^ 59
def prefixEnd_684097 : Nat := 4983230072969 + 3 ^ 40 * 684097 * 2
def baseEnd_684097 : Nat := 312240511376813512036801

theorem tailTrace_684097 : CollatzResearch.WordTrace tailWord_684097 prefixEnd_684097 312240511376813512036801 := by
  unfold tailWord_684097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24951067402640878311042545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16634044935093918874028363 24951067402640878311042545)
  ·
    refine ⟨18713300551980658733281909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24951067402640878311042545 18713300551980658733281909)
    ·
      refine ⟨1754371926748186756245179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18713300551980658733281909 1754371926748186756245179)
      ·
        refine ⟨2631557890122280134367769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754371926748186756245179 2631557890122280134367769)
        ·
          refine ⟨1973668417591710100775827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631557890122280134367769 1973668417591710100775827)
          ·
            refine ⟨2960502626387565151163741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973668417591710100775827 2960502626387565151163741)
            ·
              refine ⟨1110188484895336931686403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2960502626387565151163741 1110188484895336931686403)
              ·
                refine ⟨1665282727343005397529605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110188484895336931686403 1665282727343005397529605)
                ·
                  refine ⟨312240511376813512036801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665282727343005397529605 312240511376813512036801)
                  ·
                    rfl

theorem cell20_684097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_684097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684097 prefixEnd_684097 := by exact prefixLift 684097
  have htrace : WordTrace (prefixWord ++ tailWord_684097) baseStart_684097 baseEnd_684097 := by
    simpa [prefixWord, tailWord_684097, baseEnd_684097] using wordTrace_append hprefix tailTrace_684097
  have hstable : (prefixWord ++ tailWord_684097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684097).length < 2 ^ (prefixWord ++ tailWord_684097).sum := by decide
  have hdescent : baseEnd_684097 < baseStart_684097 := by decide
  rcases family_descends (prefixWord ++ tailWord_684097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684132 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_684132 : Nat := 118140960795 + 684132 * 2 ^ 59
def prefixEnd_684132 : Nat := 4983230072969 + 3 ^ 40 * 684132 * 2
def baseEnd_684132 : Nat := 312256486330508945869991

theorem tailTrace_684132 : CollatzResearch.WordTrace tailWord_684132 prefixEnd_684132 312256486330508945869991 := by
  unfold tailWord_684132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476171978757039644283325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16634895971676052859044433 12476171978757039644283325)
  ·
    refine ⟨4678564492033889866606247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12476171978757039644283325 4678564492033889866606247)
    ·
      refine ⟨7017846738050834799909371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4678564492033889866606247 7017846738050834799909371)
      ·
        refine ⟨10526770107076252199864057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7017846738050834799909371 10526770107076252199864057)
        ·
          refine ⟨7895077580307189149898043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10526770107076252199864057 7895077580307189149898043)
          ·
            refine ⟨11842616370460783724847065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7895077580307189149898043 11842616370460783724847065)
            ·
              refine ⟨8881962277845587793635299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11842616370460783724847065 8881962277845587793635299)
              ·
                refine ⟨13322943416768381690452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8881962277845587793635299 13322943416768381690452949)
                ·
                  refine ⟨312256486330508945869991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13322943416768381690452949 312256486330508945869991)
                  ·
                    rfl

theorem cell20_684132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_684132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684132 prefixEnd_684132 := by exact prefixLift 684132
  have htrace : WordTrace (prefixWord ++ tailWord_684132) baseStart_684132 baseEnd_684132 := by
    simpa [prefixWord, tailWord_684132, baseEnd_684132] using wordTrace_append hprefix tailTrace_684132
  have hstable : (prefixWord ++ tailWord_684132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684132).length < 2 ^ (prefixWord ++ tailWord_684132).sum := by decide
  have hdescent : baseEnd_684132 < baseStart_684132 := by decide
  rcases family_descends (prefixWord ++ tailWord_684132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684135 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 2]
def baseStart_684135 : Nat := 118140960795 + 684135 * 2 ^ 59
def prefixEnd_684135 : Nat := 4983230072969 + 3 ^ 40 * 684135 * 2
def baseEnd_684135 : Nat := 312257855612254268769979

theorem tailTrace_684135 : CollatzResearch.WordTrace tailWord_684135 prefixEnd_684135 312257855612254268769979 := by
  unfold tailWord_684135
  simp only [CollatzResearch.WordTrace]
  refine ⟨24952453376503210800925859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16634968917668807200617239 24952453376503210800925859)
  ·
    refine ⟨37428680064754816201388789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24952453376503210800925859 37428680064754816201388789)
    ·
      refine ⟨3508938756070764018880199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37428680064754816201388789 3508938756070764018880199)
      ·
        refine ⟨5263408134106146028320299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508938756070764018880199 5263408134106146028320299)
        ·
          refine ⟨7895112201159219042480449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5263408134106146028320299 7895112201159219042480449)
          ·
            refine ⟨5921334150869414281860337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7895112201159219042480449 5921334150869414281860337)
            ·
              refine ⟨4441000613152060711395253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5921334150869414281860337 4441000613152060711395253)
              ·
                refine ⟨416343807483005691693305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4441000613152060711395253 416343807483005691693305)
                ·
                  refine ⟨312257855612254268769979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416343807483005691693305 312257855612254268769979)
                  ·
                    rfl

theorem cell20_684135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2].length) (baseStart_684135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684135 prefixEnd_684135 := by exact prefixLift 684135
  have htrace : WordTrace (prefixWord ++ tailWord_684135) baseStart_684135 baseEnd_684135 := by
    simpa [prefixWord, tailWord_684135, baseEnd_684135] using wordTrace_append hprefix tailTrace_684135
  have hstable : (prefixWord ++ tailWord_684135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684135).length < 2 ^ (prefixWord ++ tailWord_684135).sum := by decide
  have hdescent : baseEnd_684135 < baseStart_684135 := by decide
  rcases family_descends (prefixWord ++ tailWord_684135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684163 : List Nat := [1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_684163 : Nat := 118140960795 + 684163 * 2 ^ 59
def prefixEnd_684163 : Nat := 4983230072969 + 3 ^ 40 * 684163 * 2
def baseEnd_684163 : Nat := 104090211858403538612177

theorem tailTrace_684163 : CollatzResearch.WordTrace tailWord_684163 prefixEnd_684163 104090211858403538612177 := by
  unfold tailWord_684163
  simp only [CollatzResearch.WordTrace]
  refine ⟨24953474620401771582945143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16635649746934514388630095 24953474620401771582945143)
  ·
    refine ⟨37430211930602657374417715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24953474620401771582945143 37430211930602657374417715)
    ·
      refine ⟨56145317895903986061626573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37430211930602657374417715 56145317895903986061626573)
      ·
        refine ⟨21054494210963994773109965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56145317895903986061626573 21054494210963994773109965)
        ·
          refine ⟨7895435329111498039916237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21054494210963994773109965 7895435329111498039916237)
          ·
            refine ⟨2960788248416811764968589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7895435329111498039916237 2960788248416811764968589)
            ·
              refine ⟨1110295593156304411863221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2960788248416811764968589 1110295593156304411863221)
              ·
                refine ⟨104090211858403538612177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1110295593156304411863221 104090211858403538612177)
                ·
                  rfl

theorem cell20_684163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_684163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684163 prefixEnd_684163 := by exact prefixLift 684163
  have htrace : WordTrace (prefixWord ++ tailWord_684163) baseStart_684163 baseEnd_684163 := by
    simpa [prefixWord, tailWord_684163, baseEnd_684163] using wordTrace_append hprefix tailTrace_684163
  have hstable : (prefixWord ++ tailWord_684163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684163).length < 2 ^ (prefixWord ++ tailWord_684163).sum := by decide
  have hdescent : baseEnd_684163 < baseStart_684163 := by decide
  rcases family_descends (prefixWord ++ tailWord_684163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684182 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_684182 : Nat := 118140960795 + 684182 * 2 ^ 59
def prefixEnd_684182 : Nat := 4983230072969 + 3 ^ 40 * 684182 * 2
def baseEnd_684182 : Nat := 312279307692930994203121

theorem tailTrace_684182 : CollatzResearch.WordTrace tailWord_684182 prefixEnd_684182 312279307692930994203121 := by
  unfold tailWord_684182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559635475458308614242925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16636111738221958551924533 1559635475458308614242925)
  ·
    refine ⟨584863303296865730341097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1559635475458308614242925 584863303296865730341097)
    ·
      refine ⟨438647477472649297755823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584863303296865730341097 438647477472649297755823)
      ·
        refine ⟨657971216208973946633735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438647477472649297755823 657971216208973946633735)
        ·
          refine ⟨986956824313460919950603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657971216208973946633735 986956824313460919950603)
          ·
            refine ⟨1480435236470191379925905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986956824313460919950603 1480435236470191379925905)
            ·
              refine ⟨1110326427352643534944429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480435236470191379925905 1110326427352643534944429)
              ·
                refine ⟨416372410257241325604161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110326427352643534944429 416372410257241325604161)
                ·
                  refine ⟨312279307692930994203121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416372410257241325604161 312279307692930994203121)
                  ·
                    rfl

theorem cell20_684182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_684182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684182 prefixEnd_684182 := by exact prefixLift 684182
  have htrace : WordTrace (prefixWord ++ tailWord_684182) baseStart_684182 baseEnd_684182 := by
    simpa [prefixWord, tailWord_684182, baseEnd_684182] using wordTrace_append hprefix tailTrace_684182
  have hstable : (prefixWord ++ tailWord_684182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684182).length < 2 ^ (prefixWord ++ tailWord_684182).sum := by decide
  have hdescent : baseEnd_684182 < baseStart_684182 := by decide
  rcases family_descends (prefixWord ++ tailWord_684182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684245 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 2]
def baseStart_684245 : Nat := 118140960795 + 684245 * 2 ^ 59
def prefixEnd_684245 : Nat := 4983230072969 + 3 ^ 40 * 684245 * 2
def baseEnd_684245 : Nat := 312308062609582775102863

theorem tailTrace_684245 : CollatzResearch.WordTrace tailWord_684245 prefixEnd_684245 312308062609582775102863 := by
  unfold tailWord_684245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24956465406104699587430189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16637643604069799724953459 24956465406104699587430189)
  ·
    refine ⟨9358674527289262345286321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24956465406104699587430189 9358674527289262345286321)
    ·
      refine ⟨7019005895466946758964741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9358674527289262345286321 7019005895466946758964741)
      ·
        refine ⟨1316063605400052517305889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7019005895466946758964741 1316063605400052517305889)
        ·
          refine ⟨987047704050039387979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316063605400052517305889 987047704050039387979417)
          ·
            refine ⟨740285778037529540984563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987047704050039387979417 740285778037529540984563)
            ·
              refine ⟨1110428667056294311476845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740285778037529540984563 1110428667056294311476845)
              ·
                refine ⟨416410750146110366803817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110428667056294311476845 416410750146110366803817)
                ·
                  refine ⟨312308062609582775102863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416410750146110366803817 312308062609582775102863)
                  ·
                    rfl

theorem cell20_684245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_684245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684245 prefixEnd_684245 := by exact prefixLift 684245
  have htrace : WordTrace (prefixWord ++ tailWord_684245) baseStart_684245 baseEnd_684245 := by
    simpa [prefixWord, tailWord_684245, baseEnd_684245] using wordTrace_append hprefix tailTrace_684245
  have hstable : (prefixWord ++ tailWord_684245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684245).length < 2 ^ (prefixWord ++ tailWord_684245).sum := by decide
  have hdescent : baseEnd_684245 < baseStart_684245 := by decide
  rcases family_descends (prefixWord ++ tailWord_684245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684249 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 2]
def baseStart_684249 : Nat := 118140960795 + 684249 * 2 ^ 59
def prefixEnd_684249 : Nat := 4983230072969 + 3 ^ 40 * 684249 * 2
def baseEnd_684249 : Nat := 312309888318576538969513

theorem tailTrace_684249 : CollatzResearch.WordTrace tailWord_684249 prefixEnd_684249 312309888318576538969513 := by
  unfold tailWord_684249
  simp only [CollatzResearch.WordTrace]
  refine ⟨24956611298090208270575801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16637740865393472180383867 24956611298090208270575801)
  ·
    refine ⟨18717458473567656202931851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24956611298090208270575801 18717458473567656202931851)
    ·
      refine ⟨28076187710351484304397777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18717458473567656202931851 28076187710351484304397777)
      ·
        refine ⟨21057140782763613228298333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28076187710351484304397777 21057140782763613228298333)
        ·
          refine ⟨7896427793536354960611875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21057140782763613228298333 7896427793536354960611875)
          ·
            refine ⟨11844641690304532440917813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7896427793536354960611875 11844641690304532440917813)
            ·
              refine ⟨1110435158466049916336045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11844641690304532440917813 1110435158466049916336045)
              ·
                refine ⟨416413184424768718626017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110435158466049916336045 416413184424768718626017)
                ·
                  refine ⟨312309888318576538969513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416413184424768718626017 312309888318576538969513)
                  ·
                    rfl

theorem cell20_684249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_684249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684249 prefixEnd_684249 := by exact prefixLift 684249
  have htrace : WordTrace (prefixWord ++ tailWord_684249) baseStart_684249 baseEnd_684249 := by
    simpa [prefixWord, tailWord_684249, baseEnd_684249] using wordTrace_append hprefix tailTrace_684249
  have hstable : (prefixWord ++ tailWord_684249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684249).length < 2 ^ (prefixWord ++ tailWord_684249).sum := by decide
  have hdescent : baseEnd_684249 < baseStart_684249 := by decide
  rcases family_descends (prefixWord ++ tailWord_684249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684252 : List Nat := [2, 2, 5, 2, 2, 1, 6]
def baseStart_684252 : Nat := 118140960795 + 684252 * 2 ^ 59
def prefixEnd_684252 : Nat := 4983230072969 + 3 ^ 40 * 684252 * 2
def baseEnd_684252 : Nat := 34701250844480206874389

theorem tailTrace_684252 : CollatzResearch.WordTrace tailWord_684252 prefixEnd_684252 34701250844480206874389 := by
  unfold tailWord_684252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478360358539669891467505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16637813811386226521956673 12478360358539669891467505)
  ·
    refine ⟨9358770268904752418600629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12478360358539669891467505 9358770268904752418600629)
    ·
      refine ⟨877384712709820539243809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9358770268904752418600629 877384712709820539243809)
      ·
        refine ⟨658038534532365404432857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877384712709820539243809 658038534532365404432857)
        ·
          refine ⟨493528900899274053324643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658038534532365404432857 493528900899274053324643)
          ·
            refine ⟨740293351348911079986965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493528900899274053324643 740293351348911079986965)
            ·
              refine ⟨34701250844480206874389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 740293351348911079986965 34701250844480206874389)
              ·
                rfl

theorem cell20_684252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_684252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684252 prefixEnd_684252 := by exact prefixLift 684252
  have htrace : WordTrace (prefixWord ++ tailWord_684252) baseStart_684252 baseEnd_684252 := by
    simpa [prefixWord, tailWord_684252, baseEnd_684252] using wordTrace_append hprefix tailTrace_684252
  have hstable : (prefixWord ++ tailWord_684252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684252).length < 2 ^ (prefixWord ++ tailWord_684252).sum := by decide
  have hdescent : baseEnd_684252 < baseStart_684252 := by decide
  rcases family_descends (prefixWord ++ tailWord_684252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684263 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_684263 : Nat := 118140960795 + 684263 * 2 ^ 59
def prefixEnd_684263 : Nat := 4983230072969 + 3 ^ 40 * 684263 * 2
def baseEnd_684263 : Nat := 312316278300054712502789

theorem tailTrace_684263 : CollatzResearch.WordTrace tailWord_684263 prefixEnd_684263 312316278300054712502789 := by
  unfold tailWord_684263
  simp only [CollatzResearch.WordTrace]
  refine ⟨24957121920039488661585443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16638081280026325774390295 24957121920039488661585443)
  ·
    refine ⟨37435682880059232992378165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24957121920039488661585443 37435682880059232992378165)
    ·
      refine ⟨3509595270005553093035453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37435682880059232992378165 3509595270005553093035453)
      ·
        refine ⟨1316098226252082409888295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3509595270005553093035453 1316098226252082409888295)
        ·
          refine ⟨1974147339378123614832443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316098226252082409888295 1974147339378123614832443)
          ·
            refine ⟨2961221009067185422248665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974147339378123614832443 2961221009067185422248665)
            ·
              refine ⟨2220915756800389066686499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961221009067185422248665 2220915756800389066686499)
              ·
                refine ⟨3331373635200583600029749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220915756800389066686499 3331373635200583600029749)
                ·
                  refine ⟨312316278300054712502789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3331373635200583600029749 312316278300054712502789)
                  ·
                    rfl

theorem cell20_684263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_684263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684263 prefixEnd_684263 := by exact prefixLift 684263
  have htrace : WordTrace (prefixWord ++ tailWord_684263) baseStart_684263 baseEnd_684263 := by
    simpa [prefixWord, tailWord_684263, baseEnd_684263] using wordTrace_append hprefix tailTrace_684263
  have hstable : (prefixWord ++ tailWord_684263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684263).length < 2 ^ (prefixWord ++ tailWord_684263).sum := by decide
  have hdescent : baseEnd_684263 < baseStart_684263 := by decide
  rcases family_descends (prefixWord ++ tailWord_684263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684266 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_684266 : Nat := 118140960795 + 684266 * 2 ^ 59
def prefixEnd_684266 : Nat := 4983230072969 + 3 ^ 40 * 684266 * 2
def baseEnd_684266 : Nat := 312317647581800035402777

theorem tailTrace_684266 : CollatzResearch.WordTrace tailWord_684266 prefixEnd_684266 312317647581800035402777 := by
  unfold tailWord_684266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239307834757155043486163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16638154226019080115963101 6239307834757155043486163)
  ·
    refine ⟨9358961752135732565229245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6239307834757155043486163 9358961752135732565229245)
    ·
      refine ⟨3509610657050899711960967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9358961752135732565229245 3509610657050899711960967)
      ·
        refine ⟨5264415985576349567941451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509610657050899711960967 5264415985576349567941451)
        ·
          refine ⟨7896623978364524351912177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264415985576349567941451 7896623978364524351912177)
          ·
            refine ⟨5922467983773393263934133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7896623978364524351912177 5922467983773393263934133)
            ·
              refine ⟨555231373478755618493825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5922467983773393263934133 555231373478755618493825)
              ·
                refine ⟨416423530109066713870369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555231373478755618493825 416423530109066713870369)
                ·
                  refine ⟨312317647581800035402777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416423530109066713870369 312317647581800035402777)
                  ·
                    rfl

theorem cell20_684266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_684266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684266 prefixEnd_684266 := by exact prefixLift 684266
  have htrace : WordTrace (prefixWord ++ tailWord_684266) baseStart_684266 baseEnd_684266 := by
    simpa [prefixWord, tailWord_684266, baseEnd_684266] using wordTrace_append hprefix tailTrace_684266
  have hstable : (prefixWord ++ tailWord_684266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684266).length < 2 ^ (prefixWord ++ tailWord_684266).sum := by decide
  have hdescent : baseEnd_684266 < baseStart_684266 := by decide
  rcases family_descends (prefixWord ++ tailWord_684266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684291 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_684291 : Nat := 118140960795 + 684291 * 2 ^ 59
def prefixEnd_684291 : Nat := 4983230072969 + 3 ^ 40 * 684291 * 2
def baseEnd_684291 : Nat := 312329058263011059569341

theorem tailTrace_684291 : CollatzResearch.WordTrace tailWord_684291 prefixEnd_684291 312329058263011059569341 := by
  unfold tailWord_684291
  simp only [CollatzResearch.WordTrace]
  refine ⟨24958143163938049443604727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16638762109292032962403151 24958143163938049443604727)
  ·
    refine ⟨37437214745907074165407091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24958143163938049443604727 37437214745907074165407091)
    ·
      refine ⟨56155822118860611248110637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37437214745907074165407091 56155822118860611248110637)
      ·
        refine ⟨21058433294572729218041489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56155822118860611248110637 21058433294572729218041489)
        ·
          refine ⟨15793824970929546913531117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21058433294572729218041489 15793824970929546913531117)
          ·
            refine ⟨5922684364098580092574169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15793824970929546913531117 5922684364098580092574169)
            ·
              refine ⟨4442013273073935069430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922684364098580092574169 4442013273073935069430627)
              ·
                refine ⟨6663019909610902604145941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442013273073935069430627 6663019909610902604145941)
                ·
                  refine ⟨312329058263011059569341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6663019909610902604145941 312329058263011059569341)
                  ·
                    rfl

theorem cell20_684291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_684291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684291 prefixEnd_684291 := by exact prefixLift 684291
  have htrace : WordTrace (prefixWord ++ tailWord_684291) baseStart_684291 baseEnd_684291 := by
    simpa [prefixWord, tailWord_684291, baseEnd_684291] using wordTrace_append hprefix tailTrace_684291
  have hstable : (prefixWord ++ tailWord_684291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684291).length < 2 ^ (prefixWord ++ tailWord_684291).sum := by decide
  have hdescent : baseEnd_684291 < baseStart_684291 := by decide
  rcases family_descends (prefixWord ++ tailWord_684291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684336 : List Nat := [2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_684336 : Nat := 118140960795 + 684336 * 2 ^ 59
def prefixEnd_684336 : Nat := 4983230072969 + 3 ^ 40 * 684336 * 2
def baseEnd_684336 : Nat := 104116532496396967689719

theorem tailTrace_684336 : CollatzResearch.WordTrace tailWord_684336 prefixEnd_684336 104116532496396967689719 := by
  unfold tailWord_684336
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479892224387511064496431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16639856299183348085995241 12479892224387511064496431)
  ·
    refine ⟨18719838336581266596744647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479892224387511064496431 18719838336581266596744647)
    ·
      refine ⟨28079757504871899895116971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18719838336581266596744647 28079757504871899895116971)
      ·
        refine ⟨42119636257307849842675457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28079757504871899895116971 42119636257307849842675457)
        ·
          refine ⟨31589727192980887382006593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42119636257307849842675457 31589727192980887382006593)
          ·
            refine ⟨23692295394735665536504945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31589727192980887382006593 23692295394735665536504945)
            ·
              refine ⟨17769221546051749152378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23692295394735665536504945 17769221546051749152378709)
              ·
                refine ⟨104116532496396967689719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17769221546051749152378709 104116532496396967689719)
                ·
                  rfl

theorem cell20_684336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_684336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684336 prefixEnd_684336 := by exact prefixLift 684336
  have htrace : WordTrace (prefixWord ++ tailWord_684336) baseStart_684336 baseEnd_684336 := by
    simpa [prefixWord, tailWord_684336, baseEnd_684336] using wordTrace_append hprefix tailTrace_684336
  have hstable : (prefixWord ++ tailWord_684336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684336).length < 2 ^ (prefixWord ++ tailWord_684336).sum := by decide
  have hdescent : baseEnd_684336 < baseStart_684336 := by decide
  rcases family_descends (prefixWord ++ tailWord_684336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684346 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_684346 : Nat := 118140960795 + 684346 * 2 ^ 59
def prefixEnd_684346 : Nat := 4983230072969 + 3 ^ 40 * 684346 * 2
def baseEnd_684346 : Nat := 312354161761675312735783

theorem tailTrace_684346 : CollatzResearch.WordTrace tailWord_684346 prefixEnd_684346 312354161761675312735783 := by
  unfold tailWord_684346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240037294684698459214223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16640099452492529224571261 6240037294684698459214223)
  ·
    refine ⟨9360055942027047688821335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240037294684698459214223 9360055942027047688821335)
    ·
      refine ⟨14040083913040571533232003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360055942027047688821335 14040083913040571533232003)
      ·
        refine ⟨21060125869560857299848005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040083913040571533232003 21060125869560857299848005)
        ·
          refine ⟨3948773600542660743721501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21060125869560857299848005 3948773600542660743721501)
          ·
            refine ⟨1480790100203497778895563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3948773600542660743721501 1480790100203497778895563)
            ·
              refine ⟨2221185150305246668343345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480790100203497778895563 2221185150305246668343345)
              ·
                refine ⟨1665888862728935001257509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221185150305246668343345 1665888862728935001257509)
                ·
                  refine ⟨312354161761675312735783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665888862728935001257509 312354161761675312735783)
                  ·
                    rfl

theorem cell20_684346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_684346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684346 prefixEnd_684346 := by exact prefixLift 684346
  have htrace : WordTrace (prefixWord ++ tailWord_684346) baseStart_684346 baseEnd_684346 := by
    simpa [prefixWord, tailWord_684346, baseEnd_684346] using wordTrace_append hprefix tailTrace_684346
  have hstable : (prefixWord ++ tailWord_684346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684346).length < 2 ^ (prefixWord ++ tailWord_684346).sum := by decide
  have hdescent : baseEnd_684346 < baseStart_684346 := by decide
  rcases family_descends (prefixWord ++ tailWord_684346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684373 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 3]
def baseStart_684373 : Nat := 118140960795 + 684373 * 2 ^ 59
def prefixEnd_684373 : Nat := 4983230072969 + 3 ^ 40 * 684373 * 2
def baseEnd_684373 : Nat := 312366485297383218835673

theorem tailTrace_684373 : CollatzResearch.WordTrace tailWord_684373 prefixEnd_684373 312366485297383218835673 := by
  unfold tailWord_684373
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961133949640977448089773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16640755966427318298726515 24961133949640977448089773)
  ·
    refine ⟨9360425231115366543033665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24961133949640977448089773 9360425231115366543033665)
    ·
      refine ⟨7020318923336524907275249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9360425231115366543033665 7020318923336524907275249)
      ·
        refine ⟨5265239192502393680456437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7020318923336524907275249 5265239192502393680456437)
        ·
          refine ⟨493616174297099407542791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5265239192502393680456437 493616174297099407542791)
          ·
            refine ⟨740424261445649111314187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493616174297099407542791 740424261445649111314187)
            ·
              refine ⟨1110636392168473666971281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740424261445649111314187 1110636392168473666971281)
              ·
                refine ⟨832977294126355250228461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110636392168473666971281 832977294126355250228461)
                ·
                  refine ⟨312366485297383218835673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 832977294126355250228461 312366485297383218835673)
                  ·
                    rfl

theorem cell20_684373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_684373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684373 prefixEnd_684373 := by exact prefixLift 684373
  have htrace : WordTrace (prefixWord ++ tailWord_684373) baseStart_684373 baseEnd_684373 := by
    simpa [prefixWord, tailWord_684373, baseEnd_684373] using wordTrace_append hprefix tailTrace_684373
  have hstable : (prefixWord ++ tailWord_684373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684373).length < 2 ^ (prefixWord ++ tailWord_684373).sum := by decide
  have hdescent : baseEnd_684373 < baseStart_684373 := by decide
  rcases family_descends (prefixWord ++ tailWord_684373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684380 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_684380 : Nat := 118140960795 + 684380 * 2 ^ 59
def prefixEnd_684380 : Nat := 4983230072969 + 3 ^ 40 * 684380 * 2
def baseEnd_684380 : Nat := 312369680288122305602311

theorem tailTrace_684380 : CollatzResearch.WordTrace tailWord_684380 prefixEnd_684380 312369680288122305602311 := by
  unfold tailWord_684380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12480694630307808821797297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16640926173743745095729729 12480694630307808821797297)
  ·
    refine ⟨9360520972730856616347973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12480694630307808821797297 9360520972730856616347973)
    ·
      refine ⟨1755097682387035615565245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9360520972730856616347973 1755097682387035615565245)
      ·
        refine ⟨658161630895138355836967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1755097682387035615565245 658161630895138355836967)
        ·
          refine ⟨987242446342707533755451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658161630895138355836967 987242446342707533755451)
          ·
            refine ⟨1480863669514061300633177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987242446342707533755451 1480863669514061300633177)
            ·
              refine ⟨1110647752135545975474883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480863669514061300633177 1110647752135545975474883)
              ·
                refine ⟨1665971628203318963212325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110647752135545975474883 1665971628203318963212325)
                ·
                  refine ⟨312369680288122305602311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665971628203318963212325 312369680288122305602311)
                  ·
                    rfl

theorem cell20_684380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_684380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684380 prefixEnd_684380 := by exact prefixLift 684380
  have htrace : WordTrace (prefixWord ++ tailWord_684380) baseStart_684380 baseEnd_684380 := by
    simpa [prefixWord, tailWord_684380, baseEnd_684380] using wordTrace_append hprefix tailTrace_684380
  have hstable : (prefixWord ++ tailWord_684380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684380).length < 2 ^ (prefixWord ++ tailWord_684380).sum := by decide
  have hdescent : baseEnd_684380 < baseStart_684380 := by decide
  rcases family_descends (prefixWord ++ tailWord_684380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684446 : List Nat := [4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_684446 : Nat := 118140960795 + 684446 * 2 ^ 59
def prefixEnd_684446 : Nat := 4983230072969 + 3 ^ 40 * 684446 * 2
def baseEnd_684446 : Nat := 104133268162173136467347

theorem tailTrace_684446 : CollatzResearch.WordTrace tailWord_684446 prefixEnd_684446 104133268162173136467347 := by
  unfold tailWord_684446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120474559797063864437149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16642530985584340610331461 3120474559797063864437149)
  ·
    refine ⟨1170177959923898949163931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3120474559797063864437149 1170177959923898949163931)
    ·
      refine ⟨1755266939885848423745897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170177959923898949163931 1755266939885848423745897)
      ·
        refine ⟨1316450204914386317809423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755266939885848423745897 1316450204914386317809423)
        ·
          refine ⟨1974675307371579476714135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316450204914386317809423 1974675307371579476714135)
          ·
            refine ⟨2962012961057369215071203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974675307371579476714135 2962012961057369215071203)
            ·
              refine ⟨4443019441586053822606805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962012961057369215071203 4443019441586053822606805)
              ·
                refine ⟨104133268162173136467347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4443019441586053822606805 104133268162173136467347)
                ·
                  rfl

theorem cell20_684446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_684446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684446 prefixEnd_684446 := by exact prefixLift 684446
  have htrace : WordTrace (prefixWord ++ tailWord_684446) baseStart_684446 baseEnd_684446 := by
    simpa [prefixWord, tailWord_684446, baseEnd_684446] using wordTrace_append hprefix tailTrace_684446
  have hstable : (prefixWord ++ tailWord_684446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684446).length < 2 ^ (prefixWord ++ tailWord_684446).sum := by decide
  have hdescent : baseEnd_684446 < baseStart_684446 := by decide
  rcases family_descends (prefixWord ++ tailWord_684446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684484 : List Nat := [2, 3, 3, 2, 3, 7]
def baseStart_684484 : Nat := 118140960795 + 684484 * 2 ^ 59
def prefixEnd_684484 : Nat := 4983230072969 + 3 ^ 40 * 684484 * 2
def baseEnd_684484 : Nat := 11571005508220746893897

theorem tailTrace_684484 : CollatzResearch.WordTrace tailWord_684484 prefixEnd_684484 11571005508220746893897 := by
  unfold tailWord_684484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12482591226119421702690253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16643454968159228936920337 12482591226119421702690253)
  ·
    refine ⟨4680971709794783138508845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12482591226119421702690253 4680971709794783138508845)
    ·
      refine ⟨1755364391173043676940817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4680971709794783138508845 1755364391173043676940817)
      ·
        refine ⟨1316523293379782757705613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755364391173043676940817 1316523293379782757705613)
        ·
          refine ⟨493696235017418534139605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1316523293379782757705613 493696235017418534139605)
          ·
            refine ⟨11571005508220746893897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 493696235017418534139605 11571005508220746893897)
            ·
              rfl

theorem cell20_684484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 7].length) (baseStart_684484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684484 prefixEnd_684484 := by exact prefixLift 684484
  have htrace : WordTrace (prefixWord ++ tailWord_684484) baseStart_684484 baseEnd_684484 := by
    simpa [prefixWord, tailWord_684484, baseEnd_684484] using wordTrace_append hprefix tailTrace_684484
  have hstable : (prefixWord ++ tailWord_684484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684484).length < 2 ^ (prefixWord ++ tailWord_684484).sum := by decide
  have hdescent : baseEnd_684484 < baseStart_684484 := by decide
  rcases family_descends (prefixWord ++ tailWord_684484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684488 : List Nat := [2, 1, 3, 1, 3, 10]
def baseStart_684488 : Nat := 118140960795 + 684488 * 2 ^ 59
def prefixEnd_684488 : Nat := 4983230072969 + 3 ^ 40 * 684488 * 2
def baseEnd_684488 : Nat := 11571073127072367777847

theorem tailTrace_684488 : CollatzResearch.WordTrace tailWord_684488 prefixEnd_684488 11571073127072367777847 := by
  unfold tailWord_684488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12482664172112176044263059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16643552229482901392350745 12482664172112176044263059)
  ·
    refine ⟨18723996258168264066394589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12482664172112176044263059 18723996258168264066394589)
    ·
      refine ⟨7021498596813099024897971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18723996258168264066394589 7021498596813099024897971)
      ·
        refine ⟨10532247895219648537346957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021498596813099024897971 10532247895219648537346957)
        ·
          refine ⟨3949592960707368201505109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10532247895219648537346957 3949592960707368201505109)
          ·
            refine ⟨11571073127072367777847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3949592960707368201505109 11571073127072367777847)
            ·
              rfl

theorem cell20_684488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 10].length) (baseStart_684488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684488 prefixEnd_684488 := by exact prefixLift 684488
  have htrace : WordTrace (prefixWord ++ tailWord_684488) baseStart_684488 baseEnd_684488 := by
    simpa [prefixWord, tailWord_684488, baseEnd_684488] using wordTrace_append hprefix tailTrace_684488
  have hstable : (prefixWord ++ tailWord_684488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684488).length < 2 ^ (prefixWord ++ tailWord_684488).sum := by decide
  have hdescent : baseEnd_684488 < baseStart_684488 := by decide
  rcases family_descends (prefixWord ++ tailWord_684488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684512 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_684512 : Nat := 118140960795 + 684512 * 2 ^ 59
def prefixEnd_684512 : Nat := 4983230072969 + 3 ^ 40 * 684512 * 2
def baseEnd_684512 : Nat := 312429928684916513201771

theorem tailTrace_684512 : CollatzResearch.WordTrace tailWord_684512 prefixEnd_684512 312429928684916513201771 := by
  unfold tailWord_684512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483101848068702093699895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16644135797424936124933193 12483101848068702093699895)
  ·
    refine ⟨18724652772103053140549843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483101848068702093699895 18724652772103053140549843)
    ·
      refine ⟨28086979158154579710824765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18724652772103053140549843 28086979158154579710824765)
      ·
        refine ⟨10532617184307967391559287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28086979158154579710824765 10532617184307967391559287)
        ·
          refine ⟨15798925776461951087338931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10532617184307967391559287 15798925776461951087338931)
          ·
            refine ⟨23698388664692926631008397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15798925776461951087338931 23698388664692926631008397)
            ·
              refine ⟨8886895749259847486628149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23698388664692926631008397 8886895749259847486628149)
              ·
                refine ⟨833146476493110701871389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8886895749259847486628149 833146476493110701871389)
                ·
                  refine ⟨312429928684916513201771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833146476493110701871389 312429928684916513201771)
                  ·
                    rfl

theorem cell20_684512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_684512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684512 prefixEnd_684512 := by exact prefixLift 684512
  have htrace : WordTrace (prefixWord ++ tailWord_684512) baseStart_684512 baseEnd_684512 := by
    simpa [prefixWord, tailWord_684512, baseEnd_684512] using wordTrace_append hprefix tailTrace_684512
  have hstable : (prefixWord ++ tailWord_684512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684512).length < 2 ^ (prefixWord ++ tailWord_684512).sum := by decide
  have hdescent : baseEnd_684512 < baseStart_684512 := by decide
  rcases family_descends (prefixWord ++ tailWord_684512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684522 : List Nat := [3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_684522 : Nat := 118140960795 + 684522 * 2 ^ 59
def prefixEnd_684522 : Nat := 4983230072969 + 3 ^ 40 * 684522 * 2
def baseEnd_684522 : Nat := 104144830985800307622799

theorem tailTrace_684522 : CollatzResearch.WordTrace tailWord_684522 prefixEnd_684522 104144830985800307622799 := by
  unfold tailWord_684522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241642106525293973815955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16644378950734117263509213 6241642106525293973815955)
  ·
    refine ⟨9362463159787940960723933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6241642106525293973815955 9362463159787940960723933)
    ·
      refine ⟨3510923684920477860271475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9362463159787940960723933 3510923684920477860271475)
      ·
        refine ⟨5266385527380716790407213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3510923684920477860271475 5266385527380716790407213)
        ·
          refine ⟨1974894572767768796402705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5266385527380716790407213 1974894572767768796402705)
          ·
            refine ⟨1481170929575826597302029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974894572767768796402705 1481170929575826597302029)
            ·
              refine ⟨555439098590934973988261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1481170929575826597302029 555439098590934973988261)
              ·
                refine ⟨104144830985800307622799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555439098590934973988261 104144830985800307622799)
                ·
                  rfl

theorem cell20_684522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_684522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684522 prefixEnd_684522 := by exact prefixLift 684522
  have htrace : WordTrace (prefixWord ++ tailWord_684522) baseStart_684522 baseEnd_684522 := by
    simpa [prefixWord, tailWord_684522, baseEnd_684522] using wordTrace_append hprefix tailTrace_684522
  have hstable : (prefixWord ++ tailWord_684522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684522).length < 2 ^ (prefixWord ++ tailWord_684522).sum := by decide
  have hdescent : baseEnd_684522 < baseStart_684522 := by decide
  rcases family_descends (prefixWord ++ tailWord_684522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684546 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_684546 : Nat := 118140960795 + 684546 * 2 ^ 59
def prefixEnd_684546 : Nat := 4983230072969 + 3 ^ 40 * 684546 * 2
def baseEnd_684546 : Nat := 312445447211363506068299

theorem tailTrace_684546 : CollatzResearch.WordTrace tailWord_684546 prefixEnd_684546 312445447211363506068299 := by
  unfold tailWord_684546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241860944503556998534373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16644962518676151996091661 6241860944503556998534373)
  ·
    refine ⟨1170348927094416937225195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6241860944503556998534373 1170348927094416937225195)
    ·
      refine ⟨1755523390641625405837793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170348927094416937225195 1755523390641625405837793)
      ·
        refine ⟨1316642542981219054378345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755523390641625405837793 1316642542981219054378345)
        ·
          refine ⟨987481907235914290783759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316642542981219054378345 987481907235914290783759)
          ·
            refine ⟨1481222860853871436175639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987481907235914290783759 1481222860853871436175639)
            ·
              refine ⟨2221834291280807154263459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481222860853871436175639 2221834291280807154263459)
              ·
                refine ⟨3332751436921210731395189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221834291280807154263459 3332751436921210731395189)
                ·
                  refine ⟨312445447211363506068299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332751436921210731395189 312445447211363506068299)
                  ·
                    rfl

theorem cell20_684546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_684546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684546 prefixEnd_684546 := by exact prefixLift 684546
  have htrace : WordTrace (prefixWord ++ tailWord_684546) baseStart_684546 baseEnd_684546 := by
    simpa [prefixWord, tailWord_684546, baseEnd_684546] using wordTrace_append hprefix tailTrace_684546
  have hstable : (prefixWord ++ tailWord_684546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684546).length < 2 ^ (prefixWord ++ tailWord_684546).sum := by decide
  have hdescent : baseEnd_684546 < baseStart_684546 := by decide
  rcases family_descends (prefixWord ++ tailWord_684546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684581 : List Nat := [1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_684581 : Nat := 118140960795 + 684581 * 2 ^ 59
def prefixEnd_684581 : Nat := 4983230072969 + 3 ^ 40 * 684581 * 2
def baseEnd_684581 : Nat := 104153807388352979967163

theorem tailTrace_684581 : CollatzResearch.WordTrace tailWord_684581 prefixEnd_684581 104153807388352979967163 := by
  unfold tailWord_684581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968720332887428971661597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16645813555258285981107731 24968720332887428971661597)
  ·
    refine ⟨9363270124832785864373099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24968720332887428971661597 9363270124832785864373099)
    ·
      refine ⟨14044905187249178796559649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9363270124832785864373099 14044905187249178796559649)
      ·
        refine ⟨10533678890436884097419737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14044905187249178796559649 10533678890436884097419737)
        ·
          refine ⟨7900259167827663073064803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10533678890436884097419737 7900259167827663073064803)
          ·
            refine ⟨11850388751741494609597205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900259167827663073064803 11850388751741494609597205)
            ·
              refine ⟨555486972737882559824869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11850388751741494609597205 555486972737882559824869)
              ·
                refine ⟨104153807388352979967163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555486972737882559824869 104153807388352979967163)
                ·
                  rfl

theorem cell20_684581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_684581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684581 prefixEnd_684581 := by exact prefixLift 684581
  have htrace : WordTrace (prefixWord ++ tailWord_684581) baseStart_684581 baseEnd_684581 := by
    simpa [prefixWord, tailWord_684581, baseEnd_684581] using wordTrace_append hprefix tailTrace_684581
  have hstable : (prefixWord ++ tailWord_684581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684581).length < 2 ^ (prefixWord ++ tailWord_684581).sum := by decide
  have hdescent : baseEnd_684581 < baseStart_684581 := by decide
  rcases family_descends (prefixWord ++ tailWord_684581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684598 : List Nat := [5, 1, 2, 1, 2, 3, 6]
def baseStart_684598 : Nat := 118140960795 + 684598 * 2 ^ 59
def prefixEnd_684598 : Nat := 4983230072969 + 3 ^ 40 * 684598 * 2
def baseEnd_684598 : Nat := 34718797936475826259417

theorem tailTrace_684598 : CollatzResearch.WordTrace tailWord_684598 prefixEnd_684598 34718797936475826259417 := by
  unfold tailWord_684598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560583773364115054689403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16646226915883893916686965 1560583773364115054689403)
  ·
    refine ⟨2340875660046172582034105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560583773364115054689403 2340875660046172582034105)
    ·
      refine ⟨1755656745034629436525579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2340875660046172582034105 1755656745034629436525579)
      ·
        refine ⟨2633485117551944154788369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755656745034629436525579 2633485117551944154788369)
        ·
          refine ⟨1975113838163958116091277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2633485117551944154788369 1975113838163958116091277)
          ·
            refine ⟨740667689311484293534229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1975113838163958116091277 740667689311484293534229)
            ·
              refine ⟨34718797936475826259417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 740667689311484293534229 34718797936475826259417)
              ·
                rfl

theorem cell20_684598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_684598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684598 prefixEnd_684598 := by exact prefixLift 684598
  have htrace : WordTrace (prefixWord ++ tailWord_684598) baseStart_684598 baseEnd_684598 := by
    simpa [prefixWord, tailWord_684598, baseEnd_684598] using wordTrace_append hprefix tailTrace_684598
  have hstable : (prefixWord ++ tailWord_684598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684598).length < 2 ^ (prefixWord ++ tailWord_684598).sum := by decide
  have hdescent : baseEnd_684598 < baseStart_684598 := by decide
  rcases family_descends (prefixWord ++ tailWord_684598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684602 : List Nat := [3, 1, 1, 1, 3, 3, 8]
def baseStart_684602 : Nat := 118140960795 + 684602 * 2 ^ 59
def prefixEnd_684602 : Nat := 4983230072969 + 3 ^ 40 * 684602 * 2
def baseEnd_684602 : Nat := 34719000793030688911267

theorem tailTrace_684602 : CollatzResearch.WordTrace tailWord_684602 prefixEnd_684602 34719000793030688911267 := by
  unfold tailWord_684602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6242371566452837389544015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16646324177207566372117373 6242371566452837389544015)
  ·
    refine ⟨9363557349679256084316023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6242371566452837389544015 9363557349679256084316023)
    ·
      refine ⟨14045336024518884126474035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9363557349679256084316023 14045336024518884126474035)
      ·
        refine ⟨21068004036778326189711053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14045336024518884126474035 21068004036778326189711053)
        ·
          refine ⟨7900501513791872321141645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21068004036778326189711053 7900501513791872321141645)
          ·
            refine ⟨2962688067671952120428117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7900501513791872321141645 2962688067671952120428117)
            ·
              refine ⟨34719000793030688911267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2962688067671952120428117 34719000793030688911267)
              ·
                rfl

theorem cell20_684602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_684602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684602 prefixEnd_684602 := by exact prefixLift 684602
  have htrace : WordTrace (prefixWord ++ tailWord_684602) baseStart_684602 baseEnd_684602 := by
    simpa [prefixWord, tailWord_684602, baseEnd_684602] using wordTrace_append hprefix tailTrace_684602
  have hstable : (prefixWord ++ tailWord_684602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684602).length < 2 ^ (prefixWord ++ tailWord_684602).sum := by decide
  have hdescent : baseEnd_684602 < baseStart_684602 := by decide
  rcases family_descends (prefixWord ++ tailWord_684602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684640 : List Nat := [2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_684640 : Nat := 118140960795 + 684640 * 2 ^ 59
def prefixEnd_684640 : Nat := 4983230072969 + 3 ^ 40 * 684640 * 2
def baseEnd_684640 : Nat := 104162783790905652311527

theorem tailTrace_684640 : CollatzResearch.WordTrace tailWord_684640 prefixEnd_684640 104162783790905652311527 := by
  unfold tailWord_684640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12485436119836841024029687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16647248159782454698706249 12485436119836841024029687)
  ·
    refine ⟨18728154179755261536044531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12485436119836841024029687 18728154179755261536044531)
    ·
      refine ⟨28092231269632892304066797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18728154179755261536044531 28092231269632892304066797)
      ·
        refine ⟨10534586726112334614025049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28092231269632892304066797 10534586726112334614025049)
        ·
          refine ⟨7900940044584250960518787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10534586726112334614025049 7900940044584250960518787)
          ·
            refine ⟨11851410066876376440778181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900940044584250960518787 11851410066876376440778181)
            ·
              refine ⟨2222139387539320582645909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11851410066876376440778181 2222139387539320582645909)
              ·
                refine ⟨104162783790905652311527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2222139387539320582645909 104162783790905652311527)
                ·
                  rfl

theorem cell20_684640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_684640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684640 prefixEnd_684640 := by exact prefixLift 684640
  have htrace : WordTrace (prefixWord ++ tailWord_684640) baseStart_684640 baseEnd_684640 := by
    simpa [prefixWord, tailWord_684640, baseEnd_684640] using wordTrace_append hprefix tailTrace_684640
  have hstable : (prefixWord ++ tailWord_684640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684640).length < 2 ^ (prefixWord ++ tailWord_684640).sum := by decide
  have hdescent : baseEnd_684640 < baseStart_684640 := by decide
  rcases family_descends (prefixWord ++ tailWord_684640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684695 : List Nat := [1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_684695 : Nat := 118140960795 + 684695 * 2 ^ 59
def prefixEnd_684695 : Nat := 4983230072969 + 3 ^ 40 * 684695 * 2
def baseEnd_684695 : Nat := 104171151623793736700341

theorem tailTrace_684695 : CollatzResearch.WordTrace tailWord_684695 prefixEnd_684695 104171151623793736700341 := by
  unfold tailWord_684695
  simp only [CollatzResearch.WordTrace]
  refine ⟨24972878254474426441311539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16648585502982950960874359 24972878254474426441311539)
  ·
    refine ⟨37459317381711639661967309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24972878254474426441311539 37459317381711639661967309)
    ·
      refine ⟨14047244018141864873237741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37459317381711639661967309 14047244018141864873237741)
      ·
        refine ⟨5267716506803199327464153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14047244018141864873237741 5267716506803199327464153)
        ·
          refine ⟨3950787380102399495598115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5267716506803199327464153 3950787380102399495598115)
          ·
            refine ⟨5926181070153599243397173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950787380102399495598115 5926181070153599243397173)
            ·
              refine ⟨555579475326899929068485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5926181070153599243397173 555579475326899929068485)
              ·
                refine ⟨104171151623793736700341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555579475326899929068485 104171151623793736700341)
                ·
                  rfl

theorem cell20_684695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_684695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684695 prefixEnd_684695 := by exact prefixLift 684695
  have htrace : WordTrace (prefixWord ++ tailWord_684695) baseStart_684695 baseEnd_684695 := by
    simpa [prefixWord, tailWord_684695, baseEnd_684695] using wordTrace_append hprefix tailTrace_684695
  have hstable : (prefixWord ++ tailWord_684695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684695).length < 2 ^ (prefixWord ++ tailWord_684695).sum := by decide
  have hdescent : baseEnd_684695 < baseStart_684695 := by decide
  rcases family_descends (prefixWord ++ tailWord_684695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684719 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_684719 : Nat := 118140960795 + 684719 * 2 ^ 59
def prefixEnd_684719 : Nat := 4983230072969 + 3 ^ 40 * 684719 * 2
def baseEnd_684719 : Nat := 312524409125343793300925

theorem tailTrace_684719 : CollatzResearch.WordTrace tailWord_684719 prefixEnd_684719 312524409125343793300925 := by
  unfold tailWord_684719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24973753606387478540185211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16649169070924985693456807 24973753606387478540185211)
  ·
    refine ⟨37460630409581217810277817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24973753606387478540185211 37460630409581217810277817)
    ·
      refine ⟨28095472807185913357708363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37460630409581217810277817 28095472807185913357708363)
      ·
        refine ⟨42143209210778870036562545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28095472807185913357708363 42143209210778870036562545)
        ·
          refine ⟨31607406908084152527421909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42143209210778870036562545 31607406908084152527421909)
          ·
            refine ⟨740798599408222324861451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31607406908084152527421909 740798599408222324861451)
            ·
              refine ⟨1111197899112333487292177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740798599408222324861451 1111197899112333487292177)
              ·
                refine ⟨833398424334250115469133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111197899112333487292177 833398424334250115469133)
                ·
                  refine ⟨312524409125343793300925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833398424334250115469133 312524409125343793300925)
                  ·
                    rfl

theorem cell20_684719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_684719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684719 prefixEnd_684719 := by exact prefixLift 684719
  have htrace : WordTrace (prefixWord ++ tailWord_684719) baseStart_684719 baseEnd_684719 := by
    simpa [prefixWord, tailWord_684719, baseEnd_684719] using wordTrace_append hprefix tailTrace_684719
  have hstable : (prefixWord ++ tailWord_684719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684719).length < 2 ^ (prefixWord ++ tailWord_684719).sum := by decide
  have hdescent : baseEnd_684719 < baseStart_684719 := by decide
  rcases family_descends (prefixWord ++ tailWord_684719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684750 : List Nat := [4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_684750 : Nat := 118140960795 + 684750 * 2 ^ 59
def prefixEnd_684750 : Nat := 4983230072969 + 3 ^ 40 * 684750 * 2
def baseEnd_684750 : Nat := 104179519456681821089155

theorem tailTrace_684750 : CollatzResearch.WordTrace tailWord_684750 prefixEnd_684750 104179519456681821089155 := by
  unfold tailWord_684750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121860533659396354320463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16649922846183447223042469 3121860533659396354320463)
  ·
    refine ⟨4682790800489094531480695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3121860533659396354320463 4682790800489094531480695)
    ·
      refine ⟨7024186200733641797221043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4682790800489094531480695 7024186200733641797221043)
      ·
        refine ⟨10536279301100462695831565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024186200733641797221043 10536279301100462695831565)
        ·
          refine ⟨3951104737912673510936837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10536279301100462695831565 3951104737912673510936837)
          ·
            refine ⟨740832138358626283300657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3951104737912673510936837 740832138358626283300657)
            ·
              refine ⟨555624103768969712475493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740832138358626283300657 555624103768969712475493)
              ·
                refine ⟨104179519456681821089155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555624103768969712475493 104179519456681821089155)
                ·
                  rfl

theorem cell20_684750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_684750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684750 prefixEnd_684750 := by exact prefixLift 684750
  have htrace : WordTrace (prefixWord ++ tailWord_684750) baseStart_684750 baseEnd_684750 := by
    simpa [prefixWord, tailWord_684750, baseEnd_684750] using wordTrace_append hprefix tailTrace_684750
  have hstable : (prefixWord ++ tailWord_684750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684750).length < 2 ^ (prefixWord ++ tailWord_684750).sum := by decide
  have hdescent : baseEnd_684750 < baseStart_684750 := by decide
  rcases family_descends (prefixWord ++ tailWord_684750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684761 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_684761 : Nat := 118140960795 + 684761 * 2 ^ 59
def prefixEnd_684761 : Nat := 4983230072969 + 3 ^ 40 * 684761 * 2
def baseEnd_684761 : Nat := 312543579069778313900753

theorem tailTrace_684761 : CollatzResearch.WordTrace tailWord_684761 prefixEnd_684761 312543579069778313900753 := by
  unfold tailWord_684761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975285472235319713214137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16650190314823546475476091 24975285472235319713214137)
  ·
    refine ⟨18731464104176489784910603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24975285472235319713214137 18731464104176489784910603)
    ·
      refine ⟨28097196156264734677365905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731464104176489784910603 28097196156264734677365905)
      ·
        refine ⟨21072897117198551008024429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28097196156264734677365905 21072897117198551008024429)
        ·
          refine ⟨7902336418949456628009161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21072897117198551008024429 7902336418949456628009161)
          ·
            refine ⟨5926752314212092471006871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7902336418949456628009161 5926752314212092471006871)
            ·
              refine ⟨8890128471318138706510307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926752314212092471006871 8890128471318138706510307)
              ·
                refine ⟨13335192706977208059765461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8890128471318138706510307 13335192706977208059765461)
                ·
                  refine ⟨312543579069778313900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13335192706977208059765461 312543579069778313900753)
                  ·
                    rfl

theorem cell20_684761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_684761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684761 prefixEnd_684761 := by exact prefixLift 684761
  have htrace : WordTrace (prefixWord ++ tailWord_684761) baseStart_684761 baseEnd_684761 := by
    simpa [prefixWord, tailWord_684761, baseEnd_684761] using wordTrace_append hprefix tailTrace_684761
  have hstable : (prefixWord ++ tailWord_684761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684761).length < 2 ^ (prefixWord ++ tailWord_684761).sum := by decide
  have hdescent : baseEnd_684761 < baseStart_684761 := by decide
  rcases family_descends (prefixWord ++ tailWord_684761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684771 : List Nat := [1, 1, 1, 7, 1, 3, 6]
def baseStart_684771 : Nat := 118140960795 + 684771 * 2 ^ 59
def prefixEnd_684771 : Nat := 4983230072969 + 3 ^ 40 * 684771 * 2
def baseEnd_684771 : Nat := 34727571482473635951931

theorem tailTrace_684771 : CollatzResearch.WordTrace tailWord_684771 prefixEnd_684771 34727571482473635951931 := by
  unfold tailWord_684771
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975650202199091421078167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16650433468132727614052111 24975650202199091421078167)
  ·
    refine ⟨37463475303298637131617251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24975650202199091421078167 37463475303298637131617251)
    ·
      refine ⟨56195212954947955697425877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37463475303298637131617251 56195212954947955697425877)
      ·
        refine ⟨1317075303631592711658419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 56195212954947955697425877 1317075303631592711658419)
        ·
          refine ⟨1975612955447389067487629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317075303631592711658419 1975612955447389067487629)
          ·
            refine ⟨740854858292770900307861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1975612955447389067487629 740854858292770900307861)
            ·
              refine ⟨34727571482473635951931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 740854858292770900307861 34727571482473635951931)
              ·
                rfl

theorem cell20_684771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_684771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684771 prefixEnd_684771 := by exact prefixLift 684771
  have htrace : WordTrace (prefixWord ++ tailWord_684771) baseStart_684771 baseEnd_684771 := by
    simpa [prefixWord, tailWord_684771, baseEnd_684771] using wordTrace_append hprefix tailTrace_684771
  have hstable : (prefixWord ++ tailWord_684771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684771).length < 2 ^ (prefixWord ++ tailWord_684771).sum := by decide
  have hdescent : baseEnd_684771 < baseStart_684771 := by decide
  rcases family_descends (prefixWord ++ tailWord_684771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684778 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_684778 : Nat := 118140960795 + 684778 * 2 ^ 59
def prefixEnd_684778 : Nat := 4983230072969 + 3 ^ 40 * 684778 * 2
def baseEnd_684778 : Nat := 312551338333001810334017

theorem tailTrace_684778 : CollatzResearch.WordTrace tailWord_684778 prefixEnd_684778 312551338333001810334017 := by
  unfold tailWord_684778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243976378293432904145747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16650603675449154411055325 6243976378293432904145747)
  ·
    refine ⟨9365964567440149356218621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243976378293432904145747 9365964567440149356218621)
    ·
      refine ⟨3512236712790056008581983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9365964567440149356218621 3512236712790056008581983)
      ·
        refine ⟨5268355069185084012872975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512236712790056008581983 5268355069185084012872975)
        ·
          refine ⟨7902532603777626019309463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268355069185084012872975 7902532603777626019309463)
          ·
            refine ⟨11853798905666439028964195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902532603777626019309463 11853798905666439028964195)
            ·
              refine ⟨17780698358499658543446293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853798905666439028964195 17780698358499658543446293)
              ·
                refine ⟨833470235554671494224045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17780698358499658543446293 833470235554671494224045)
                ·
                  refine ⟨312551338333001810334017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833470235554671494224045 312551338333001810334017)
                  ·
                    rfl

theorem cell20_684778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_684778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684778 prefixEnd_684778 := by exact prefixLift 684778
  have htrace : WordTrace (prefixWord ++ tailWord_684778) baseStart_684778 baseEnd_684778 := by
    simpa [prefixWord, tailWord_684778, baseEnd_684778] using wordTrace_append hprefix tailTrace_684778
  have hstable : (prefixWord ++ tailWord_684778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684778).length < 2 ^ (prefixWord ++ tailWord_684778).sum := by decide
  have hdescent : baseEnd_684778 < baseStart_684778 := by decide
  rcases family_descends (prefixWord ++ tailWord_684778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684792 : List Nat := [2, 1, 2, 1, 1, 2, 6, 5]
def baseStart_684792 : Nat := 118140960795 + 684792 * 2 ^ 59
def prefixEnd_684792 : Nat := 4983230072969 + 3 ^ 40 * 684792 * 2
def baseEnd_684792 : Nat := 104185909438159994622431

theorem tailTrace_684792 : CollatzResearch.WordTrace tailWord_684792 prefixEnd_684792 104185909438159994622431 := by
  unfold tailWord_684792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488208067561506003796315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16650944090082008005061753 12488208067561506003796315)
  ·
    refine ⟨18732312101342259005694473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12488208067561506003796315 18732312101342259005694473)
    ·
      refine ⟨14049234076006694254270855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18732312101342259005694473 14049234076006694254270855)
      ·
        refine ⟨21073851114010041381406283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14049234076006694254270855 21073851114010041381406283)
        ·
          refine ⟨31610776671015062072109425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21073851114010041381406283 31610776671015062072109425)
          ·
            refine ⟨23708082503261296554082069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31610776671015062072109425 23708082503261296554082069)
            ·
              refine ⟨1111316367340373275972597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23708082503261296554082069 1111316367340373275972597)
              ·
                refine ⟨104185909438159994622431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111316367340373275972597 104185909438159994622431)
                ·
                  rfl

theorem cell20_684792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_684792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684792 prefixEnd_684792 := by exact prefixLift 684792
  have htrace : WordTrace (prefixWord ++ tailWord_684792) baseStart_684792 baseEnd_684792 := by
    simpa [prefixWord, tailWord_684792, baseEnd_684792] using wordTrace_append hprefix tailTrace_684792
  have hstable : (prefixWord ++ tailWord_684792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684792).length < 2 ^ (prefixWord ++ tailWord_684792).sum := by decide
  have hdescent : baseEnd_684792 < baseStart_684792 := by decide
  rcases family_descends (prefixWord ++ tailWord_684792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684899 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_684899 : Nat := 118140960795 + 684899 * 2 ^ 59
def prefixEnd_684899 : Nat := 4983230072969 + 3 ^ 40 * 684899 * 2
def baseEnd_684899 : Nat := 312606566030063167300189

theorem tailTrace_684899 : CollatzResearch.WordTrace tailWord_684899 prefixEnd_684899 312606566030063167300189 := by
  unfold tailWord_684899
  simp only [CollatzResearch.WordTrace]
  refine ⟨24980318745735369281737751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16653545830490246187825167 24980318745735369281737751)
  ·
    refine ⟨37470478118603053922606627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24980318745735369281737751 37470478118603053922606627)
    ·
      refine ⟨56205717177904580883909941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37470478118603053922606627 56205717177904580883909941)
      ·
        refine ⟨5269285985428554457866557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56205717177904580883909941 5269285985428554457866557)
        ·
          refine ⟨1975982244535707921699959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269285985428554457866557 1975982244535707921699959)
          ·
            refine ⟨2963973366803561882549939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975982244535707921699959 2963973366803561882549939)
            ·
              refine ⟨4445960050205342823824909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963973366803561882549939 4445960050205342823824909)
              ·
                refine ⟨1667235018827003558934341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4445960050205342823824909 1667235018827003558934341)
                ·
                  refine ⟨312606566030063167300189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667235018827003558934341 312606566030063167300189)
                  ·
                    rfl

theorem cell20_684899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_684899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684899 prefixEnd_684899 := by exact prefixLift 684899
  have htrace : WordTrace (prefixWord ++ tailWord_684899) baseStart_684899 baseEnd_684899 := by
    simpa [prefixWord, tailWord_684899, baseEnd_684899] using wordTrace_append hprefix tailTrace_684899
  have hstable : (prefixWord ++ tailWord_684899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684899).length < 2 ^ (prefixWord ++ tailWord_684899).sum := by decide
  have hdescent : baseEnd_684899 < baseStart_684899 := by decide
  rcases family_descends (prefixWord ++ tailWord_684899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684920 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_684920 : Nat := 118140960795 + 684920 * 2 ^ 59
def prefixEnd_684920 : Nat := 4983230072969 + 3 ^ 40 * 684920 * 2
def baseEnd_684920 : Nat := 312616151002280427600103

theorem tailTrace_684920 : CollatzResearch.WordTrace tailWord_684920 prefixEnd_684920 312616151002280427600103 := by
  unfold tailWord_684920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490542339329644934126107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16654056452439526578834809 12490542339329644934126107)
  ·
    refine ⟨18735813508994467401189161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490542339329644934126107 18735813508994467401189161)
    ·
      refine ⟨14051860131745850550891871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18735813508994467401189161 14051860131745850550891871)
      ·
        refine ⟨21077790197618775826337807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14051860131745850550891871 21077790197618775826337807)
        ·
          refine ⟨31616685296428163739506711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21077790197618775826337807 31616685296428163739506711)
          ·
            refine ⟨47425027944642245609260067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31616685296428163739506711 47425027944642245609260067)
            ·
              refine ⟨71137541916963368413890101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47425027944642245609260067 71137541916963368413890101)
              ·
                refine ⟨6669144554715315788802197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71137541916963368413890101 6669144554715315788802197)
                ·
                  refine ⟨312616151002280427600103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6669144554715315788802197 312616151002280427600103)
                  ·
                    rfl

theorem cell20_684920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_684920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684920 prefixEnd_684920 := by exact prefixLift 684920
  have htrace : WordTrace (prefixWord ++ tailWord_684920) baseStart_684920 baseEnd_684920 := by
    simpa [prefixWord, tailWord_684920, baseEnd_684920] using wordTrace_append hprefix tailTrace_684920
  have hstable : (prefixWord ++ tailWord_684920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684920).length < 2 ^ (prefixWord ++ tailWord_684920).sum := by decide
  have hdescent : baseEnd_684920 < baseStart_684920 := by decide
  rcases family_descends (prefixWord ++ tailWord_684920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684933 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 2]
def baseStart_684933 : Nat := 118140960795 + 684933 * 2 ^ 59
def prefixEnd_684933 : Nat := 4983230072969 + 3 ^ 40 * 684933 * 2
def baseEnd_684933 : Nat := 312622084556510160166717

theorem tailTrace_684933 : CollatzResearch.WordTrace tailWord_684933 prefixEnd_684933 312622084556510160166717 := by
  unfold tailWord_684933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24981558827612193088475453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16654372551741462058983635 24981558827612193088475453)
  ·
    refine ⟨9368084560354572408178295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24981558827612193088475453 9368084560354572408178295)
    ·
      refine ⟨14052126840531858612267443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9368084560354572408178295 14052126840531858612267443)
      ·
        refine ⟨21078190260797787918401165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14052126840531858612267443 21078190260797787918401165)
        ·
          refine ⟨7904321347799170469400437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21078190260797787918401165 7904321347799170469400437)
          ·
            refine ⟨741030126356172231506291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7904321347799170469400437 741030126356172231506291)
            ·
              refine ⟨1111545189534258347259437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741030126356172231506291 1111545189534258347259437)
              ·
                refine ⟨416829446075346880222289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1111545189534258347259437 416829446075346880222289)
                ·
                  refine ⟨312622084556510160166717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416829446075346880222289 312622084556510160166717)
                  ·
                    rfl

theorem cell20_684933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_684933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684933 prefixEnd_684933 := by exact prefixLift 684933
  have htrace : WordTrace (prefixWord ++ tailWord_684933) baseStart_684933 baseEnd_684933 := by
    simpa [prefixWord, tailWord_684933, baseEnd_684933] using wordTrace_append hprefix tailTrace_684933
  have hstable : (prefixWord ++ tailWord_684933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684933).length < 2 ^ (prefixWord ++ tailWord_684933).sum := by decide
  have hdescent : baseEnd_684933 < baseStart_684933 := by decide
  rcases family_descends (prefixWord ++ tailWord_684933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684950 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_684950 : Nat := 118140960795 + 684950 * 2 ^ 59
def prefixEnd_684950 : Nat := 4983230072969 + 3 ^ 40 * 684950 * 2
def baseEnd_684950 : Nat := 312629843819733656599981

theorem tailTrace_684950 : CollatzResearch.WordTrace tailWord_684950 prefixEnd_684950 312629843819733656599981 := by
  unfold tailWord_684950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561386179284412811990269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16654785912367069994562869 1561386179284412811990269)
  ·
    refine ⟨585519817231654804496351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1561386179284412811990269 585519817231654804496351)
    ·
      refine ⟨878279725847482206744527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585519817231654804496351 878279725847482206744527)
      ·
        refine ⟨1317419588771223310116791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878279725847482206744527 1317419588771223310116791)
        ·
          refine ⟨1976129383156834965175187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317419588771223310116791 1976129383156834965175187)
          ·
            refine ⟨2964194074735252447762781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976129383156834965175187 2964194074735252447762781)
            ·
              refine ⟨1111572778025719667911043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2964194074735252447762781 1111572778025719667911043)
              ·
                refine ⟨1667359167038579501866565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111572778025719667911043 1667359167038579501866565)
                ·
                  refine ⟨312629843819733656599981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667359167038579501866565 312629843819733656599981)
                  ·
                    rfl

theorem cell20_684950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_684950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684950 prefixEnd_684950 := by exact prefixLift 684950
  have htrace : WordTrace (prefixWord ++ tailWord_684950) baseStart_684950 baseEnd_684950 := by
    simpa [prefixWord, tailWord_684950, baseEnd_684950] using wordTrace_append hprefix tailTrace_684950
  have hstable : (prefixWord ++ tailWord_684950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684950).length < 2 ^ (prefixWord ++ tailWord_684950).sum := by decide
  have hdescent : baseEnd_684950 < baseStart_684950 := by decide
  rcases family_descends (prefixWord ++ tailWord_684950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684951 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_684951 : Nat := 118140960795 + 684951 * 2 ^ 59
def prefixEnd_684951 : Nat := 4983230072969 + 3 ^ 40 * 684951 * 2
def baseEnd_684951 : Nat := 312630300246982097566643

theorem tailTrace_684951 : CollatzResearch.WordTrace tailWord_684951 prefixEnd_684951 312630300246982097566643 := by
  unfold tailWord_684951
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982215341546982162630707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16654810227697988108420471 24982215341546982162630707)
  ·
    refine ⟨37473323012320473243946061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24982215341546982162630707 37473323012320473243946061)
    ·
      refine ⟨14052496129620177466479773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37473323012320473243946061 14052496129620177466479773)
      ·
        refine ⟨5269686048607566549929915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14052496129620177466479773 5269686048607566549929915)
        ·
          refine ⟨7904529072911349824894873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269686048607566549929915 7904529072911349824894873)
          ·
            refine ⟨5928396804683512368671155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7904529072911349824894873 5928396804683512368671155)
            ·
              refine ⟨8892595207025268553006733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928396804683512368671155 8892595207025268553006733)
              ·
                refine ⟨3334723202634475707377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8892595207025268553006733 3334723202634475707377525)
                ·
                  refine ⟨312630300246982097566643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334723202634475707377525 312630300246982097566643)
                  ·
                    rfl

theorem cell20_684951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_684951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684951 prefixEnd_684951 := by exact prefixLift 684951
  have htrace : WordTrace (prefixWord ++ tailWord_684951) baseStart_684951 baseEnd_684951 := by
    simpa [prefixWord, tailWord_684951, baseEnd_684951] using wordTrace_append hprefix tailTrace_684951
  have hstable : (prefixWord ++ tailWord_684951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684951).length < 2 ^ (prefixWord ++ tailWord_684951).sum := by decide
  have hdescent : baseEnd_684951 < baseStart_684951 := by decide
  rcases family_descends (prefixWord ++ tailWord_684951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_684961 : List Nat := [1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_684961 : Nat := 118140960795 + 684961 * 2 ^ 59
def prefixEnd_684961 : Nat := 4983230072969 + 3 ^ 40 * 684961 * 2
def baseEnd_684961 : Nat := 104211621506488835744423

theorem tailTrace_684961 : CollatzResearch.WordTrace tailWord_684961 prefixEnd_684961 104211621506488835744423 := by
  unfold tailWord_684961
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982580071510753870494737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16655053381007169246996491 24982580071510753870494737)
  ·
    refine ⟨18736935053633065402871053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24982580071510753870494737 18736935053633065402871053)
    ·
      refine ⟨7026350645112399526076645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18736935053633065402871053 7026350645112399526076645)
      ·
        refine ⟨1317440745958574911139371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7026350645112399526076645 1317440745958574911139371)
        ·
          refine ⟨1976161118937862366709057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317440745958574911139371 1976161118937862366709057)
          ·
            refine ⟨1482120839203396775031793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976161118937862366709057 1482120839203396775031793)
            ·
              refine ⟨1111590629402547581273845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482120839203396775031793 1111590629402547581273845)
              ·
                refine ⟨104211621506488835744423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111590629402547581273845 104211621506488835744423)
                ·
                  rfl

theorem cell20_684961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_684961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_684961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_684961 prefixEnd_684961 := by exact prefixLift 684961
  have htrace : WordTrace (prefixWord ++ tailWord_684961) baseStart_684961 baseEnd_684961 := by
    simpa [prefixWord, tailWord_684961, baseEnd_684961] using wordTrace_append hprefix tailTrace_684961
  have hstable : (prefixWord ++ tailWord_684961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_684961).length < 2 ^ (prefixWord ++ tailWord_684961).sum := by decide
  have hdescent : baseEnd_684961 < baseStart_684961 := by decide
  rcases family_descends (prefixWord ++ tailWord_684961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685003 : List Nat := [1, 1, 1, 1, 3, 13]
def baseStart_685003 : Nat := 118140960795 + 685003 * 2 ^ 59
def prefixEnd_685003 : Nat := 4983230072969 + 3 ^ 40 * 685003 * 2
def baseEnd_685003 : Nat := 11579779054218556586411

theorem tailTrace_685003 : CollatzResearch.WordTrace tailWord_685003 prefixEnd_685003 11579779054218556586411 := by
  unfold tailWord_685003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24984111937358595043523663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16656074624905730029015775 24984111937358595043523663)
  ·
    refine ⟨37476167906037892565285495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24984111937358595043523663 37476167906037892565285495)
    ·
      refine ⟨56214251859056838847928243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37476167906037892565285495 56214251859056838847928243)
      ·
        refine ⟨84321377788585258271892365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56214251859056838847928243 84321377788585258271892365)
        ·
          refine ⟨31620516670719471851959637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84321377788585258271892365 31620516670719471851959637)
          ·
            refine ⟨11579779054218556586411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31620516670719471851959637 11579779054218556586411)
            ·
              rfl

theorem cell20_685003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_685003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685003 prefixEnd_685003 := by exact prefixLift 685003
  have htrace : WordTrace (prefixWord ++ tailWord_685003) baseStart_685003 baseEnd_685003 := by
    simpa [prefixWord, tailWord_685003, baseEnd_685003] using wordTrace_append hprefix tailTrace_685003
  have hstable : (prefixWord ++ tailWord_685003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685003).length < 2 ^ (prefixWord ++ tailWord_685003).sum := by decide
  have hdescent : baseEnd_685003 < baseStart_685003 := by decide
  rcases family_descends (prefixWord ++ tailWord_685003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685006 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_685006 : Nat := 118140960795 + 685006 * 2 ^ 59
def prefixEnd_685006 : Nat := 4983230072969 + 3 ^ 40 * 685006 * 2
def baseEnd_685006 : Nat := 312655403745646350733085

theorem tailTrace_685006 : CollatzResearch.WordTrace tailWord_685006 prefixEnd_685006 312655403745646350733085 := by
  unfold tailWord_685006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123027669543465819485359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16656147570898484370588581 3123027669543465819485359)
  ·
    refine ⟨4684541504315198729228039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123027669543465819485359 4684541504315198729228039)
    ·
      refine ⟨7026812256472798093842059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684541504315198729228039 7026812256472798093842059)
      ·
        refine ⟨10540218384709197140763089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026812256472798093842059 10540218384709197140763089)
        ·
          refine ⟨7905163788531897855572317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540218384709197140763089 7905163788531897855572317)
          ·
            refine ⟨2964436420699461695839619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7905163788531897855572317 2964436420699461695839619)
            ·
              refine ⟨4446654631049192543759429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964436420699461695839619 4446654631049192543759429)
              ·
                refine ⟨833747743321723601954893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4446654631049192543759429 833747743321723601954893)
                ·
                  refine ⟨312655403745646350733085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833747743321723601954893 312655403745646350733085)
                  ·
                    rfl

theorem cell20_685006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_685006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685006 prefixEnd_685006 := by exact prefixLift 685006
  have htrace : WordTrace (prefixWord ++ tailWord_685006) baseStart_685006 baseEnd_685006 := by
    simpa [prefixWord, tailWord_685006, baseEnd_685006] using wordTrace_append hprefix tailTrace_685006
  have hstable : (prefixWord ++ tailWord_685006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685006).length < 2 ^ (prefixWord ++ tailWord_685006).sum := by decide
  have hdescent : baseEnd_685006 < baseStart_685006 := by decide
  rcases family_descends (prefixWord ++ tailWord_685006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685068 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_685068 : Nat := 118140960795 + 685068 * 2 ^ 59
def prefixEnd_685068 : Nat := 4983230072969 + 3 ^ 40 * 685068 * 2
def baseEnd_685068 : Nat := 312683702235049690666165

theorem tailTrace_685068 : CollatzResearch.WordTrace tailWord_685068 prefixEnd_685068 312683702235049690666165 := by
  unfold tailWord_685068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493241341061555572319929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16657655121415407429759905 12493241341061555572319929)
  ·
    refine ⟨9369931005796166679239947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12493241341061555572319929 9369931005796166679239947)
    ·
      refine ⟨14054896508694250018859921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9369931005796166679239947 14054896508694250018859921)
      ·
        refine ⟨10541172381520687514144941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14054896508694250018859921 10541172381520687514144941)
        ·
          refine ⟨3952939643070257817804353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10541172381520687514144941 3952939643070257817804353)
          ·
            refine ⟨2964704732302693363353265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952939643070257817804353 2964704732302693363353265)
            ·
              refine ⟨2223528549227020022514949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964704732302693363353265 2223528549227020022514949)
              ·
                refine ⟨416911602980066254221553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2223528549227020022514949 416911602980066254221553)
                ·
                  refine ⟨312683702235049690666165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416911602980066254221553 312683702235049690666165)
                  ·
                    rfl

theorem cell20_685068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_685068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685068 prefixEnd_685068 := by exact prefixLift 685068
  have htrace : WordTrace (prefixWord ++ tailWord_685068) baseStart_685068 baseEnd_685068 := by
    simpa [prefixWord, tailWord_685068, baseEnd_685068] using wordTrace_append hprefix tailTrace_685068
  have hstable : (prefixWord ++ tailWord_685068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685068).length < 2 ^ (prefixWord ++ tailWord_685068).sum := by decide
  have hdescent : baseEnd_685068 < baseStart_685068 := by decide
  rcases family_descends (prefixWord ++ tailWord_685068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685074 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_685074 : Nat := 118140960795 + 685074 * 2 ^ 59
def prefixEnd_685074 : Nat := 4983230072969 + 3 ^ 40 * 685074 * 2
def baseEnd_685074 : Nat := 312686440798540336466141

theorem tailTrace_685074 : CollatzResearch.WordTrace tailWord_685074 prefixEnd_685074 312686440798540336466141 := by
  unfold tailWord_685074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246675380025343542339569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16657801013400916112905517 6246675380025343542339569)
  ·
    refine ⟨4685006535019007656754677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6246675380025343542339569 4685006535019007656754677)
    ·
      refine ⟨439219362658031967820751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4685006535019007656754677 439219362658031967820751)
      ·
        refine ⟨658829043987047951731127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439219362658031967820751 658829043987047951731127)
        ·
          refine ⟨988243565980571927596691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658829043987047951731127 988243565980571927596691)
          ·
            refine ⟨1482365348970857891395037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988243565980571927596691 1482365348970857891395037)
            ·
              refine ⟨555887005864071709273139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482365348970857891395037 555887005864071709273139)
              ·
                refine ⟨833830508796107563909709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555887005864071709273139 833830508796107563909709)
                ·
                  refine ⟨312686440798540336466141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833830508796107563909709 312686440798540336466141)
                  ·
                    rfl

theorem cell20_685074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_685074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685074 prefixEnd_685074 := by exact prefixLift 685074
  have htrace : WordTrace (prefixWord ++ tailWord_685074) baseStart_685074 baseEnd_685074 := by
    simpa [prefixWord, tailWord_685074, baseEnd_685074] using wordTrace_append hprefix tailTrace_685074
  have hstable : (prefixWord ++ tailWord_685074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685074).length < 2 ^ (prefixWord ++ tailWord_685074).sum := by decide
  have hdescent : baseEnd_685074 < baseStart_685074 := by decide
  rcases family_descends (prefixWord ++ tailWord_685074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685089 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_685089 : Nat := 118140960795 + 685089 * 2 ^ 59
def prefixEnd_685089 : Nat := 4983230072969 + 3 ^ 40 * 685089 * 2
def baseEnd_685089 : Nat := 312693287207266950966079

theorem tailTrace_685089 : CollatzResearch.WordTrace tailWord_685089 prefixEnd_685089 312693287207266950966079 := by
  unfold tailWord_685089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24987248615047031731154321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16658165743364687820769547 24987248615047031731154321)
  ·
    refine ⟨18740436461285273798365741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24987248615047031731154321 18740436461285273798365741)
    ·
      refine ⟨7027663672981977674387153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18740436461285273798365741 7027663672981977674387153)
      ·
        refine ⟨5270747754736483255790365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7027663672981977674387153 5270747754736483255790365)
        ·
          refine ⟨1976530408026181220921387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5270747754736483255790365 1976530408026181220921387)
          ·
            refine ⟨2964795612039271831382081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976530408026181220921387 2964795612039271831382081)
            ·
              refine ⟨2223596709029453873536561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964795612039271831382081 2223596709029453873536561)
              ·
                refine ⟨1667697531772090405152421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223596709029453873536561 1667697531772090405152421)
                ·
                  refine ⟨312693287207266950966079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667697531772090405152421 312693287207266950966079)
                  ·
                    rfl

theorem cell20_685089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_685089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685089 prefixEnd_685089 := by exact prefixLift 685089
  have htrace : WordTrace (prefixWord ++ tailWord_685089) baseStart_685089 baseEnd_685089 := by
    simpa [prefixWord, tailWord_685089, baseEnd_685089] using wordTrace_append hprefix tailTrace_685089
  have hstable : (prefixWord ++ tailWord_685089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685089).length < 2 ^ (prefixWord ++ tailWord_685089).sum := by decide
  have hdescent : baseEnd_685089 < baseStart_685089 := by decide
  rcases family_descends (prefixWord ++ tailWord_685089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685092 : List Nat := [2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_685092 : Nat := 118140960795 + 685092 * 2 ^ 59
def prefixEnd_685092 : Nat := 4983230072969 + 3 ^ 40 * 685092 * 2
def baseEnd_685092 : Nat := 104231552163004091288689

theorem tailTrace_685092 : CollatzResearch.WordTrace tailWord_685092 prefixEnd_685092 104231552163004091288689 := by
  unfold tailWord_685092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493679017018081621756765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16658238689357442162342353 12493679017018081621756765)
  ·
    refine ⟨4685129631381780608158787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12493679017018081621756765 4685129631381780608158787)
    ·
      refine ⟨7027694447072670912238181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685129631381780608158787 7027694447072670912238181)
      ·
        refine ⟨1317692708826125796044659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7027694447072670912238181 1317692708826125796044659)
        ·
          refine ⟨1976539063239188694066989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317692708826125796044659 1976539063239188694066989)
          ·
            refine ⟨741202148714695760275121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1976539063239188694066989 741202148714695760275121)
            ·
              refine ⟨555901611536021820206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741202148714695760275121 555901611536021820206341)
              ·
                refine ⟨104231552163004091288689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555901611536021820206341 104231552163004091288689)
                ·
                  rfl

theorem cell20_685092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_685092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685092 prefixEnd_685092 := by exact prefixLift 685092
  have htrace : WordTrace (prefixWord ++ tailWord_685092) baseStart_685092 baseEnd_685092 := by
    simpa [prefixWord, tailWord_685092, baseEnd_685092] using wordTrace_append hprefix tailTrace_685092
  have hstable : (prefixWord ++ tailWord_685092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685092).length < 2 ^ (prefixWord ++ tailWord_685092).sum := by decide
  have hdescent : baseEnd_685092 < baseStart_685092 := by decide
  rcases family_descends (prefixWord ++ tailWord_685092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685127 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_685127 : Nat := 118140960795 + 685127 * 2 ^ 59
def prefixEnd_685127 : Nat := 4983230072969 + 3 ^ 40 * 685127 * 2
def baseEnd_685127 : Nat := 312710631442707707699257

theorem tailTrace_685127 : CollatzResearch.WordTrace tailWord_685127 prefixEnd_685127 312710631442707707699257 := by
  unfold tailWord_685127
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988634588909364221037635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16659089725939576147358423 24988634588909364221037635)
  ·
    refine ⟨37482951883364046331556453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24988634588909364221037635 37482951883364046331556453)
    ·
      refine ⟨7028053478130758687166835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37482951883364046331556453 7028053478130758687166835)
      ·
        refine ⟨10542080217196138030750253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7028053478130758687166835 10542080217196138030750253)
        ·
          refine ⟨3953280081448551761531345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10542080217196138030750253 3953280081448551761531345)
          ·
            refine ⟨2964960061086413821148509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953280081448551761531345 2964960061086413821148509)
            ·
              refine ⟨1111860022907405182930691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2964960061086413821148509 1111860022907405182930691)
              ·
                refine ⟨1667790034361107774396037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111860022907405182930691 1667790034361107774396037)
                ·
                  refine ⟨312710631442707707699257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1667790034361107774396037 312710631442707707699257)
                  ·
                    rfl

theorem cell20_685127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_685127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685127 prefixEnd_685127 := by exact prefixLift 685127
  have htrace : WordTrace (prefixWord ++ tailWord_685127) baseStart_685127 baseEnd_685127 := by
    simpa [prefixWord, tailWord_685127, baseEnd_685127] using wordTrace_append hprefix tailTrace_685127
  have hstable : (prefixWord ++ tailWord_685127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685127).length < 2 ^ (prefixWord ++ tailWord_685127).sum := by decide
  have hdescent : baseEnd_685127 < baseStart_685127 := by decide
  rcases family_descends (prefixWord ++ tailWord_685127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685134 : List Nat := [4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_685134 : Nat := 118140960795 + 685134 * 2 ^ 59
def prefixEnd_685134 : Nat := 4983230072969 + 3 ^ 40 * 685134 * 2
def baseEnd_685134 : Nat := 104237942144482264821965

theorem tailTrace_685134 : CollatzResearch.WordTrace tailWord_685134 prefixEnd_685134 104237942144482264821965 := by
  unfold tailWord_685134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123611237485500552067807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16659259933256002944361637 3123611237485500552067807)
  ·
    refine ⟨4685416856228250828101711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3123611237485500552067807 4685416856228250828101711)
    ·
      refine ⟨7028125284342376242152567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685416856228250828101711 7028125284342376242152567)
      ·
        refine ⟨10542187926513564363228851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7028125284342376242152567 10542187926513564363228851)
        ·
          refine ⟨15813281889770346544843277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10542187926513564363228851 15813281889770346544843277)
          ·
            refine ⟨5929980708663879954316229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15813281889770346544843277 5929980708663879954316229)
            ·
              refine ⟨1111871382874477491434293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5929980708663879954316229 1111871382874477491434293)
              ·
                refine ⟨104237942144482264821965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111871382874477491434293 104237942144482264821965)
                ·
                  rfl

theorem cell20_685134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_685134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685134 prefixEnd_685134 := by exact prefixLift 685134
  have htrace : WordTrace (prefixWord ++ tailWord_685134) baseStart_685134 baseEnd_685134 := by
    simpa [prefixWord, tailWord_685134, baseEnd_685134] using wordTrace_append hprefix tailTrace_685134
  have hstable : (prefixWord ++ tailWord_685134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685134).length < 2 ^ (prefixWord ++ tailWord_685134).sum := by decide
  have hdescent : baseEnd_685134 < baseStart_685134 := by decide
  rcases family_descends (prefixWord ++ tailWord_685134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685189 : List Nat := [1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_685189 : Nat := 118140960795 + 685189 * 2 ^ 59
def prefixEnd_685189 : Nat := 4983230072969 + 3 ^ 40 * 685189 * 2
def baseEnd_685189 : Nat := 104246309977370349210779

theorem tailTrace_685189 : CollatzResearch.WordTrace tailWord_685189 prefixEnd_685189 104246309977370349210779 := by
  unfold tailWord_685189
  simp only [CollatzResearch.WordTrace]
  refine ⟨24990895914684748809794621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16660597276456499206529747 24990895914684748809794621)
  ·
    refine ⟨9371585968006780803672983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24990895914684748809794621 9371585968006780803672983)
    ·
      refine ⟨14057378952010171205509475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371585968006780803672983 14057378952010171205509475)
      ·
        refine ⟨21086068428015256808264213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14057378952010171205509475 21086068428015256808264213)
        ·
          refine ⟨988409457563215162887385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21086068428015256808264213 988409457563215162887385)
          ·
            refine ⟨741307093172411372165539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988409457563215162887385 741307093172411372165539)
            ·
              refine ⟨1111960639758617058248309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741307093172411372165539 1111960639758617058248309)
              ·
                refine ⟨104246309977370349210779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1111960639758617058248309 104246309977370349210779)
                ·
                  rfl

theorem cell20_685189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_685189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685189 prefixEnd_685189 := by exact prefixLift 685189
  have htrace : WordTrace (prefixWord ++ tailWord_685189) baseStart_685189 baseEnd_685189 := by
    simpa [prefixWord, tailWord_685189, baseEnd_685189] using wordTrace_append hprefix tailTrace_685189
  have hstable : (prefixWord ++ tailWord_685189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685189).length < 2 ^ (prefixWord ++ tailWord_685189).sum := by decide
  have hdescent : baseEnd_685189 < baseStart_685189 := by decide
  rcases family_descends (prefixWord ++ tailWord_685189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685217 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_685217 : Nat := 118140960795 + 685217 * 2 ^ 59
def prefixEnd_685217 : Nat := 4983230072969 + 3 ^ 40 * 685217 * 2
def baseEnd_685217 : Nat := 312751709895067394698889

theorem tailTrace_685217 : CollatzResearch.WordTrace tailWord_685217 prefixEnd_685217 312751709895067394698889 := by
  unfold tailWord_685217
  simp only [CollatzResearch.WordTrace]
  refine ⟨24991917158583309591813905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16661278105722206394542603 24991917158583309591813905)
  ·
    refine ⟨18743937868937482193860429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24991917158583309591813905 18743937868937482193860429)
    ·
      refine ⟨7028976700851555822697661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18743937868937482193860429 7028976700851555822697661)
      ·
        refine ⟨2635866262819333433511623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7028976700851555822697661 2635866262819333433511623)
        ·
          refine ⟨3953799394229000150267435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635866262819333433511623 3953799394229000150267435)
          ·
            refine ⟨5930699091343500225401153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953799394229000150267435 5930699091343500225401153)
            ·
              refine ⟨4448024318507625169050865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5930699091343500225401153 4448024318507625169050865)
              ·
                refine ⟨3336018238880718876788149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448024318507625169050865 3336018238880718876788149)
                ·
                  refine ⟨312751709895067394698889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3336018238880718876788149 312751709895067394698889)
                  ·
                    rfl

theorem cell20_685217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_685217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685217 prefixEnd_685217 := by exact prefixLift 685217
  have htrace : WordTrace (prefixWord ++ tailWord_685217) baseStart_685217 baseEnd_685217 := by
    simpa [prefixWord, tailWord_685217, baseEnd_685217] using wordTrace_append hprefix tailTrace_685217
  have hstable : (prefixWord ++ tailWord_685217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685217).length < 2 ^ (prefixWord ++ tailWord_685217).sum := by decide
  have hdescent : baseEnd_685217 < baseStart_685217 := by decide
  rcases family_descends (prefixWord ++ tailWord_685217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685220 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_685220 : Nat := 118140960795 + 685220 * 2 ^ 59
def prefixEnd_685220 : Nat := 4983230072969 + 3 ^ 40 * 685220 * 2
def baseEnd_685220 : Nat := 312753079176812717598877

theorem tailTrace_685220 : CollatzResearch.WordTrace tailWord_685220 prefixEnd_685220 312753079176812717598877 := by
  unfold tailWord_685220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496013288786220552086557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16661351051714960736115409 12496013288786220552086557)
  ·
    refine ⟨4686004983294832707032459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12496013288786220552086557 4686004983294832707032459)
    ·
      refine ⟨7029007474942249060548689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686004983294832707032459 7029007474942249060548689)
      ·
        refine ⟨5271755606206686795411517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7029007474942249060548689 5271755606206686795411517)
        ·
          refine ⟨1976908352327507548279319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5271755606206686795411517 1976908352327507548279319)
          ·
            refine ⟨2965362528491261322418979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976908352327507548279319 2965362528491261322418979)
            ·
              refine ⟨4448043792736891983628469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965362528491261322418979 4448043792736891983628469)
              ·
                refine ⟨417004105569083623465169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4448043792736891983628469 417004105569083623465169)
                ·
                  refine ⟨312753079176812717598877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417004105569083623465169 312753079176812717598877)
                  ·
                    rfl

theorem cell20_685220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_685220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685220 prefixEnd_685220 := by exact prefixLift 685220
  have htrace : WordTrace (prefixWord ++ tailWord_685220) baseStart_685220 baseEnd_685220 := by
    simpa [prefixWord, tailWord_685220, baseEnd_685220] using wordTrace_append hprefix tailTrace_685220
  have hstable : (prefixWord ++ tailWord_685220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685220).length < 2 ^ (prefixWord ++ tailWord_685220).sum := by decide
  have hdescent : baseEnd_685220 < baseStart_685220 := by decide
  rcases family_descends (prefixWord ++ tailWord_685220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685234 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_685234 : Nat := 118140960795 + 685234 * 2 ^ 59
def prefixEnd_685234 : Nat := 4983230072969 + 3 ^ 40 * 685234 * 2
def baseEnd_685234 : Nat := 312759469158290891132153

theorem tailTrace_685234 : CollatzResearch.WordTrace tailWord_685234 prefixEnd_685234 312759469158290891132153 := by
  unfold tailWord_685234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248134299880430373795689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16661691466347814330121837 6248134299880430373795689)
  ·
    refine ⟨4686100724910322780346767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6248134299880430373795689 4686100724910322780346767)
    ·
      refine ⟨7029151087365484170520151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686100724910322780346767 7029151087365484170520151)
      ·
        refine ⟨10543726631048226255780227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029151087365484170520151 10543726631048226255780227)
        ·
          refine ⟨15815589946572339383670341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543726631048226255780227 15815589946572339383670341)
          ·
            refine ⟨2965423114982313634438189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15815589946572339383670341 2965423114982313634438189)
            ·
              refine ⟨1112033668118367612914321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2965423114982313634438189 1112033668118367612914321)
              ·
                refine ⟨834025251088775709685741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112033668118367612914321 834025251088775709685741)
                ·
                  refine ⟨312759469158290891132153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834025251088775709685741 312759469158290891132153)
                  ·
                    rfl

theorem cell20_685234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_685234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685234 prefixEnd_685234 := by exact prefixLift 685234
  have htrace : WordTrace (prefixWord ++ tailWord_685234) baseStart_685234 baseEnd_685234 := by
    simpa [prefixWord, tailWord_685234, baseEnd_685234] using wordTrace_append hprefix tailTrace_685234
  have hstable : (prefixWord ++ tailWord_685234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685234).length < 2 ^ (prefixWord ++ tailWord_685234).sum := by decide
  have hdescent : baseEnd_685234 < baseStart_685234 := by decide
  rcases family_descends (prefixWord ++ tailWord_685234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685241 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_685241 : Nat := 118140960795 + 685241 * 2 ^ 59
def prefixEnd_685241 : Nat := 4983230072969 + 3 ^ 40 * 685241 * 2
def baseEnd_685241 : Nat := 312762664149029977898791

theorem tailTrace_685241 : CollatzResearch.WordTrace tailWord_685241 prefixEnd_685241 312762664149029977898791 := by
  unfold tailWord_685241
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992792510496361690687577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16661861673664241127125051 24992792510496361690687577)
  ·
    refine ⟨18744594382872271268015683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24992792510496361690687577 18744594382872271268015683)
    ·
      refine ⟨28116891574308406902023525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18744594382872271268015683 28116891574308406902023525)
      ·
        refine ⟨5271917170182826294129411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28116891574308406902023525 5271917170182826294129411)
        ·
          refine ⟨7907875755274239441194117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271917170182826294129411 7907875755274239441194117)
          ·
            refine ⟨1482726704113919895223897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7907875755274239441194117 1482726704113919895223897)
            ·
              refine ⟨1112045028085439921417923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482726704113919895223897 1112045028085439921417923)
              ·
                refine ⟨1668067542128159882126885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112045028085439921417923 1668067542128159882126885)
                ·
                  refine ⟨312762664149029977898791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668067542128159882126885 312762664149029977898791)
                  ·
                    rfl

theorem cell20_685241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_685241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685241 prefixEnd_685241 := by exact prefixLift 685241
  have htrace : WordTrace (prefixWord ++ tailWord_685241) baseStart_685241 baseEnd_685241 := by
    simpa [prefixWord, tailWord_685241, baseEnd_685241] using wordTrace_append hprefix tailTrace_685241
  have hstable : (prefixWord ++ tailWord_685241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685241).length < 2 ^ (prefixWord ++ tailWord_685241).sum := by decide
  have hdescent : baseEnd_685241 < baseStart_685241 := by decide
  rcases family_descends (prefixWord ++ tailWord_685241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685255 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_685255 : Nat := 118140960795 + 685255 * 2 ^ 59
def prefixEnd_685255 : Nat := 4983230072969 + 3 ^ 40 * 685255 * 2
def baseEnd_685255 : Nat := 312769054130508151432067

theorem tailTrace_685255 : CollatzResearch.WordTrace tailWord_685255 prefixEnd_685255 312769054130508151432067 := by
  unfold tailWord_685255
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993303132445642081697219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16662202088297094721131479 24993303132445642081697219)
  ·
    refine ⟨37489954698668463122545829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24993303132445642081697219 37489954698668463122545829)
    ·
      refine ⟨7029366506000336835477343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37489954698668463122545829 7029366506000336835477343)
      ·
        refine ⟨10544049759000505253216015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029366506000336835477343 10544049759000505253216015)
        ·
          refine ⟨15816074638500757879824023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544049759000505253216015 15816074638500757879824023)
          ·
            refine ⟨23724111957751136819736035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816074638500757879824023 23724111957751136819736035)
            ·
              refine ⟨35586167936626705229604053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23724111957751136819736035 35586167936626705229604053)
              ·
                refine ⟨834050811014688403818845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35586167936626705229604053 834050811014688403818845)
                ·
                  refine ⟨312769054130508151432067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834050811014688403818845 312769054130508151432067)
                  ·
                    rfl

theorem cell20_685255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_685255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685255 prefixEnd_685255 := by exact prefixLift 685255
  have htrace : WordTrace (prefixWord ++ tailWord_685255) baseStart_685255 baseEnd_685255 := by
    simpa [prefixWord, tailWord_685255, baseEnd_685255] using wordTrace_append hprefix tailTrace_685255
  have hstable : (prefixWord ++ tailWord_685255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685255).length < 2 ^ (prefixWord ++ tailWord_685255).sum := by decide
  have hdescent : baseEnd_685255 < baseStart_685255 := by decide
  rcases family_descends (prefixWord ++ tailWord_685255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685348 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_685348 : Nat := 118140960795 + 685348 * 2 ^ 59
def prefixEnd_685348 : Nat := 4983230072969 + 3 ^ 40 * 685348 * 2
def baseEnd_685348 : Nat := 312811501864613161331687

theorem tailTrace_685348 : CollatzResearch.WordTrace tailWord_685348 prefixEnd_685348 312811501864613161331687 := by
  unfold tailWord_685348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12498347560554359482416349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16664463414072479309888465 12498347560554359482416349)
  ·
    refine ⟨4686880335207884805906131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12498347560554359482416349 4686880335207884805906131)
    ·
      refine ⟨7030320502811827208859197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686880335207884805906131 7030320502811827208859197)
      ·
        refine ⟨2636370188554435203322199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7030320502811827208859197 2636370188554435203322199)
        ·
          refine ⟨3954555282831652804983299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636370188554435203322199 3954555282831652804983299)
          ·
            refine ⟨5931832924247479207474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954555282831652804983299 5931832924247479207474949)
            ·
              refine ⟨1112218673296402351401553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5931832924247479207474949 1112218673296402351401553)
              ·
                refine ⟨834164004972301763551165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112218673296402351401553 834164004972301763551165)
                ·
                  refine ⟨312811501864613161331687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834164004972301763551165 312811501864613161331687)
                  ·
                    rfl

theorem cell20_685348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_685348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685348 prefixEnd_685348 := by exact prefixLift 685348
  have htrace : WordTrace (prefixWord ++ tailWord_685348) baseStart_685348 baseEnd_685348 := by
    simpa [prefixWord, tailWord_685348, baseEnd_685348] using wordTrace_append hprefix tailTrace_685348
  have hstable : (prefixWord ++ tailWord_685348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685348).length < 2 ^ (prefixWord ++ tailWord_685348).sum := by decide
  have hdescent : baseEnd_685348 < baseStart_685348 := by decide
  rcases family_descends (prefixWord ++ tailWord_685348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685362 : List Nat := [3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_685362 : Nat := 118140960795 + 685362 * 2 ^ 59
def prefixEnd_685362 : Nat := 4983230072969 + 3 ^ 40 * 685362 * 2
def baseEnd_685362 : Nat := 104272630615363778288321

theorem tailTrace_685362 : CollatzResearch.WordTrace tailWord_685362 prefixEnd_685362 104272630615363778288321 := by
  unfold tailWord_685362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249301435764499838960585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16664803828705332903894893 6249301435764499838960585)
  ·
    refine ⟨4686976076823374879220439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6249301435764499838960585 4686976076823374879220439)
    ·
      refine ⟨7030464115235062318830659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686976076823374879220439 7030464115235062318830659)
      ·
        refine ⟨10545696172852593478245989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030464115235062318830659 10545696172852593478245989)
        ·
          refine ⟨1977318032409861277171123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10545696172852593478245989 1977318032409861277171123)
          ·
            refine ⟨2965977048614791915756685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977318032409861277171123 2965977048614791915756685)
            ·
              refine ⟨1112241393230546968408757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2965977048614791915756685 1112241393230546968408757)
              ·
                refine ⟨104272630615363778288321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1112241393230546968408757 104272630615363778288321)
                ·
                  rfl

theorem cell20_685362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_685362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685362 prefixEnd_685362 := by exact prefixLift 685362
  have htrace : WordTrace (prefixWord ++ tailWord_685362) baseStart_685362 baseEnd_685362 := by
    simpa [prefixWord, tailWord_685362, baseEnd_685362] using wordTrace_append hprefix tailTrace_685362
  have hstable : (prefixWord ++ tailWord_685362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685362).length < 2 ^ (prefixWord ++ tailWord_685362).sum := by decide
  have hdescent : baseEnd_685362 < baseStart_685362 := by decide
  rcases family_descends (prefixWord ++ tailWord_685362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685376 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_685376 : Nat := 118140960795 + 685376 * 2 ^ 59
def prefixEnd_685376 : Nat := 4983230072969 + 3 ^ 40 * 685376 * 2
def baseEnd_685376 : Nat := 312824281827569508398239

theorem tailTrace_685376 : CollatzResearch.WordTrace tailWord_685376 prefixEnd_685376 312824281827569508398239 := by
  unfold tailWord_685376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12498858182503639873425991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16665144243338186497901321 12498858182503639873425991)
  ·
    refine ⟨18748287273755459810138987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12498858182503639873425991 18748287273755459810138987)
    ·
      refine ⟨28122430910633189715208481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18748287273755459810138987 28122430910633189715208481)
      ·
        refine ⟨21091823182974892286406361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28122430910633189715208481 21091823182974892286406361)
        ·
          refine ⟨15818867387231169214804771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21091823182974892286406361 15818867387231169214804771)
          ·
            refine ⟨23728301080846753822207157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15818867387231169214804771 23728301080846753822207157)
            ·
              refine ⟨2224528226329383170831921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23728301080846753822207157 2224528226329383170831921)
              ·
                refine ⟨1668396169747037378123941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224528226329383170831921 1668396169747037378123941)
                ·
                  refine ⟨312824281827569508398239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668396169747037378123941 312824281827569508398239)
                  ·
                    rfl

theorem cell20_685376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_685376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685376 prefixEnd_685376 := by exact prefixLift 685376
  have htrace : WordTrace (prefixWord ++ tailWord_685376) baseStart_685376 baseEnd_685376 := by
    simpa [prefixWord, tailWord_685376, baseEnd_685376] using wordTrace_append hprefix tailTrace_685376
  have hstable : (prefixWord ++ tailWord_685376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685376).length < 2 ^ (prefixWord ++ tailWord_685376).sum := by decide
  have hdescent : baseEnd_685376 < baseStart_685376 := by decide
  rcases family_descends (prefixWord ++ tailWord_685376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685410 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_685410 : Nat := 118140960795 + 685410 * 2 ^ 59
def prefixEnd_685410 : Nat := 4983230072969 + 3 ^ 40 * 685410 * 2
def baseEnd_685410 : Nat := 312839800354016501264767

theorem tailTrace_685410 : CollatzResearch.WordTrace tailWord_685410 prefixEnd_685410 312839800354016501264767 := by
  unfold tailWord_685410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249739111721025888397421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16665970964589402369059789 6249739111721025888397421)
  ·
    refine ⟨2343652166895384708149033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6249739111721025888397421 2343652166895384708149033)
    ·
      refine ⟨1757739125171538531111775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2343652166895384708149033 1757739125171538531111775)
      ·
        refine ⟨2636608687757307796667663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757739125171538531111775 2636608687757307796667663)
        ·
          refine ⟨3954913031635961695001495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636608687757307796667663 3954913031635961695001495)
          ·
            refine ⟨5932369547453942542502243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954913031635961695001495 5932369547453942542502243)
            ·
              refine ⟨8898554321180913813753365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932369547453942542502243 8898554321180913813753365)
              ·
                refine ⟨417119733805355335019689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8898554321180913813753365 417119733805355335019689)
                ·
                  refine ⟨312839800354016501264767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417119733805355335019689 312839800354016501264767)
                  ·
                    rfl

theorem cell20_685410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_685410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685410 prefixEnd_685410 := by exact prefixLift 685410
  have htrace : WordTrace (prefixWord ++ tailWord_685410) baseStart_685410 baseEnd_685410 := by
    simpa [prefixWord, tailWord_685410, baseEnd_685410] using wordTrace_append hprefix tailTrace_685410
  have hstable : (prefixWord ++ tailWord_685410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685410).length < 2 ^ (prefixWord ++ tailWord_685410).sum := by decide
  have hdescent : baseEnd_685410 < baseStart_685410 := by decide
  rcases family_descends (prefixWord ++ tailWord_685410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685424 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_685424 : Nat := 118140960795 + 685424 * 2 ^ 59
def prefixEnd_685424 : Nat := 4983230072969 + 3 ^ 40 * 685424 * 2
def baseEnd_685424 : Nat := 312846190335494674798043

theorem tailTrace_685424 : CollatzResearch.WordTrace tailWord_685424 prefixEnd_685424 312846190335494674798043 := by
  unfold tailWord_685424
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499733534416691972299663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16666311379222255963066217 12499733534416691972299663)
  ·
    refine ⟨18749600301625037958449495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499733534416691972299663 18749600301625037958449495)
    ·
      refine ⟨28124400452437556937674243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18749600301625037958449495 28124400452437556937674243)
      ·
        refine ⟨42186600678656335406511365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28124400452437556937674243 42186600678656335406511365)
        ·
          refine ⟨7909987627248062888720881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42186600678656335406511365 7909987627248062888720881)
          ·
            refine ⟨5932490720436047166540661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7909987627248062888720881 5932490720436047166540661)
            ·
              refine ⟨556171005040879421863187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5932490720436047166540661 556171005040879421863187)
              ·
                refine ⟨834256507561319132794781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556171005040879421863187 834256507561319132794781)
                ·
                  refine ⟨312846190335494674798043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834256507561319132794781 312846190335494674798043)
                  ·
                    rfl

theorem cell20_685424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_685424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685424 prefixEnd_685424 := by exact prefixLift 685424
  have htrace : WordTrace (prefixWord ++ tailWord_685424) baseStart_685424 baseEnd_685424 := by
    simpa [prefixWord, tailWord_685424, baseEnd_685424] using wordTrace_append hprefix tailTrace_685424
  have hstable : (prefixWord ++ tailWord_685424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685424).length < 2 ^ (prefixWord ++ tailWord_685424).sum := by decide
  have hdescent : baseEnd_685424 < baseStart_685424 := by decide
  rcases family_descends (prefixWord ++ tailWord_685424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685448 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_685448 : Nat := 118140960795 + 685448 * 2 ^ 59
def prefixEnd_685448 : Nat := 4983230072969 + 3 ^ 40 * 685448 * 2
def baseEnd_685448 : Nat := 312857144589457257997945

theorem tailTrace_685448 : CollatzResearch.WordTrace tailWord_685448 prefixEnd_685448 312857144589457257997945 := by
  unfold tailWord_685448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500171210373218021736499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16666894947164290695648665 12500171210373218021736499)
  ·
    refine ⟨18750256815559827032604749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12500171210373218021736499 18750256815559827032604749)
    ·
      refine ⟨7031346305834935137226781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18750256815559827032604749 7031346305834935137226781)
      ·
        refine ⟨2636754864688100676460043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7031346305834935137226781 2636754864688100676460043)
        ·
          refine ⟨3955132297032151014690065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636754864688100676460043 3955132297032151014690065)
          ·
            refine ⟨2966349222774113261017549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955132297032151014690065 2966349222774113261017549)
            ·
              refine ⟨1112380958540292472881581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966349222774113261017549 1112380958540292472881581)
              ·
                refine ⟨417142859452609677330593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1112380958540292472881581 417142859452609677330593)
                ·
                  refine ⟨312857144589457257997945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417142859452609677330593 312857144589457257997945)
                  ·
                    rfl

theorem cell20_685448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_685448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685448 prefixEnd_685448 := by exact prefixLift 685448
  have htrace : WordTrace (prefixWord ++ tailWord_685448) baseStart_685448 baseEnd_685448 := by
    simpa [prefixWord, tailWord_685448, baseEnd_685448] using wordTrace_append hprefix tailTrace_685448
  have hstable : (prefixWord ++ tailWord_685448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685448).length < 2 ^ (prefixWord ++ tailWord_685448).sum := by decide
  have hdescent : baseEnd_685448 < baseStart_685448 := by decide
  rcases family_descends (prefixWord ++ tailWord_685448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685469 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_685469 : Nat := 118140960795 + 685469 * 2 ^ 59
def prefixEnd_685469 : Nat := 4983230072969 + 3 ^ 40 * 685469 * 2
def baseEnd_685469 : Nat := 312866729561674518297859

theorem tailTrace_685469 : CollatzResearch.WordTrace tailWord_685469 prefixEnd_685469 312866729561674518297859 := by
  unfold tailWord_685469
  simp only [CollatzResearch.WordTrace]
  refine ⟨25001108353670356629987461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16667405569113571086658307 25001108353670356629987461)
  ·
    refine ⟨4687707816313191868122649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25001108353670356629987461 4687707816313191868122649)
    ·
      refine ⟨3515780862234893901091987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4687707816313191868122649 3515780862234893901091987)
      ·
        refine ⟨5273671293352340851637981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515780862234893901091987 5273671293352340851637981)
        ·
          refine ⟨1977626735007127819364243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5273671293352340851637981 1977626735007127819364243)
          ·
            refine ⟨2966440102510691729046365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977626735007127819364243 2966440102510691729046365)
            ·
              refine ⟨1112415038441509398392387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966440102510691729046365 1112415038441509398392387)
              ·
                refine ⟨1668622557662264097588581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112415038441509398392387 1668622557662264097588581)
                ·
                  refine ⟨312866729561674518297859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668622557662264097588581 312866729561674518297859)
                  ·
                    rfl

theorem cell20_685469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_685469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685469 prefixEnd_685469 := by exact prefixLift 685469
  have htrace : WordTrace (prefixWord ++ tailWord_685469) baseStart_685469 baseEnd_685469 := by
    simpa [prefixWord, tailWord_685469, baseEnd_685469] using wordTrace_append hprefix tailTrace_685469
  have hstable : (prefixWord ++ tailWord_685469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685469).length < 2 ^ (prefixWord ++ tailWord_685469).sum := by decide
  have hdescent : baseEnd_685469 < baseStart_685469 := by decide
  rcases family_descends (prefixWord ++ tailWord_685469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685504 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_685504 : Nat := 118140960795 + 685504 * 2 ^ 59
def prefixEnd_685504 : Nat := 4983230072969 + 3 ^ 40 * 685504 * 2
def baseEnd_685504 : Nat := 312882704515369952131049

theorem tailTrace_685504 : CollatzResearch.WordTrace tailWord_685504 prefixEnd_685504 312882704515369952131049 := by
  unfold tailWord_685504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501192454271778803755783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16668256605695705071674377 12501192454271778803755783)
  ·
    refine ⟨18751788681407668205633675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501192454271778803755783 18751788681407668205633675)
    ·
      refine ⟨28127683022111502308450513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751788681407668205633675 28127683022111502308450513)
      ·
        refine ⟨21095762266583626731337885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28127683022111502308450513 21095762266583626731337885)
        ·
          refine ⟨7910910849968860024251707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21095762266583626731337885 7910910849968860024251707)
          ·
            refine ⟨11866366274953290036377561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910910849968860024251707 11866366274953290036377561)
            ·
              refine ⟨8899774706214967527283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11866366274953290036377561 8899774706214967527283171)
              ·
                refine ⟨13349662059322451290924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8899774706214967527283171 13349662059322451290924757)
                ·
                  refine ⟨312882704515369952131049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13349662059322451290924757 312882704515369952131049)
                  ·
                    rfl

theorem cell20_685504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_685504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685504 prefixEnd_685504 := by exact prefixLift 685504
  have htrace : WordTrace (prefixWord ++ tailWord_685504) baseStart_685504 baseEnd_685504 := by
    simpa [prefixWord, tailWord_685504, baseEnd_685504] using wordTrace_append hprefix tailTrace_685504
  have hstable : (prefixWord ++ tailWord_685504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685504).length < 2 ^ (prefixWord ++ tailWord_685504).sum := by decide
  have hdescent : baseEnd_685504 < baseStart_685504 := by decide
  rcases family_descends (prefixWord ++ tailWord_685504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685552 : List Nat := [2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_685552 : Nat := 118140960795 + 685552 * 2 ^ 59
def prefixEnd_685552 : Nat := 4983230072969 + 3 ^ 40 * 685552 * 2
def baseEnd_685552 : Nat := 104301537674431706176951

theorem tailTrace_685552 : CollatzResearch.WordTrace tailWord_685552 prefixEnd_685552 104301537674431706176951 := by
  unfold tailWord_685552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502067806184830902629455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16669423741579774536839273 12502067806184830902629455)
  ·
    refine ⟨18753101709277246353944183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12502067806184830902629455 18753101709277246353944183)
    ·
      refine ⟨28129652563915869530916275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18753101709277246353944183 28129652563915869530916275)
      ·
        refine ⟨42194478845873804296374413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28129652563915869530916275 42194478845873804296374413)
        ·
          refine ⟨15822929567202676611140405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42194478845873804296374413 15822929567202676611140405)
          ·
            refine ⟨1483399646925250932294413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15822929567202676611140405 1483399646925250932294413)
            ·
              refine ⟨556274867596969099610405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1483399646925250932294413 556274867596969099610405)
              ·
                refine ⟨104301537674431706176951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 556274867596969099610405 104301537674431706176951)
                ·
                  rfl

theorem cell20_685552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_685552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685552 prefixEnd_685552 := by exact prefixLift 685552
  have htrace : WordTrace (prefixWord ++ tailWord_685552) baseStart_685552 baseEnd_685552 := by
    simpa [prefixWord, tailWord_685552, baseEnd_685552] using wordTrace_append hprefix tailTrace_685552
  have hstable : (prefixWord ++ tailWord_685552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685552).length < 2 ^ (prefixWord ++ tailWord_685552).sum := by decide
  have hdescent : baseEnd_685552 < baseStart_685552 := by decide
  rcases family_descends (prefixWord ++ tailWord_685552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685572 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_685572 : Nat := 118140960795 + 685572 * 2 ^ 59
def prefixEnd_685572 : Nat := 4983230072969 + 3 ^ 40 * 685572 * 2
def baseEnd_685572 : Nat := 312913741568263937864105

theorem tailTrace_685572 : CollatzResearch.WordTrace tailWord_685572 prefixEnd_685572 312913741568263937864105 := by
  unfold tailWord_685572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502432536148602610493485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16669910048198136813991313 12502432536148602610493485)
  ·
    refine ⟨4688412201055725978935057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12502432536148602610493485 4688412201055725978935057)
    ·
      refine ⟨3516309150791794484201293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4688412201055725978935057 3516309150791794484201293)
      ·
        refine ⟨1318615931546922931575485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3516309150791794484201293 1318615931546922931575485)
        ·
          refine ⟨494480974330096099340807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318615931546922931575485 494480974330096099340807)
          ·
            refine ⟨741721461495144149011211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494480974330096099340807 741721461495144149011211)
            ·
              refine ⟨1112582192242716223516817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741721461495144149011211 1112582192242716223516817)
              ·
                refine ⟨834436644182037167637613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112582192242716223516817 834436644182037167637613)
                ·
                  refine ⟨312913741568263937864105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834436644182037167637613 312913741568263937864105)
                  ·
                    rfl

theorem cell20_685572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_685572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685572 prefixEnd_685572 := by exact prefixLift 685572
  have htrace : WordTrace (prefixWord ++ tailWord_685572) baseStart_685572 baseEnd_685572 := by
    simpa [prefixWord, tailWord_685572, baseEnd_685572] using wordTrace_append hprefix tailTrace_685572
  have hstable : (prefixWord ++ tailWord_685572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685572).length < 2 ^ (prefixWord ++ tailWord_685572).sum := by decide
  have hdescent : baseEnd_685572 < baseStart_685572 := by decide
  rcases family_descends (prefixWord ++ tailWord_685572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685628 : List Nat := [2, 2, 2, 2, 4, 2, 6]
def baseStart_685628 : Nat := 118140960795 + 685628 * 2 ^ 59
def prefixEnd_685628 : Nat := 4983230072969 + 3 ^ 40 * 685628 * 2
def baseEnd_685628 : Nat := 34771033499352959110801

theorem tailTrace_685628 : CollatzResearch.WordTrace tailWord_685628 prefixEnd_685628 34771033499352959110801 := by
  unfold tailWord_685628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12503453780047163392512769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16671271706729551190017025 12503453780047163392512769)
  ·
    refine ⟨9377590335035372544384577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12503453780047163392512769 9377590335035372544384577)
    ·
      refine ⟨7033192751276529408288433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9377590335035372544384577 7033192751276529408288433)
      ·
        refine ⟨5274894563457397056216325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7033192751276529408288433 5274894563457397056216325)
        ·
          refine ⟨989042730648261948040561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5274894563457397056216325 989042730648261948040561)
          ·
            refine ⟨741782047986196461030421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989042730648261948040561 741782047986196461030421)
            ·
              refine ⟨34771033499352959110801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 741782047986196461030421 34771033499352959110801)
              ·
                rfl

theorem cell20_685628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_685628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685628 prefixEnd_685628 := by exact prefixLift 685628
  have htrace : WordTrace (prefixWord ++ tailWord_685628) baseStart_685628 baseEnd_685628 := by
    simpa [prefixWord, tailWord_685628, baseEnd_685628] using wordTrace_append hprefix tailTrace_685628
  have hstable : (prefixWord ++ tailWord_685628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685628).length < 2 ^ (prefixWord ++ tailWord_685628).sum := by decide
  have hdescent : baseEnd_685628 < baseStart_685628 := by decide
  rcases family_descends (prefixWord ++ tailWord_685628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685645 : List Nat := [1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_685645 : Nat := 118140960795 + 685645 * 2 ^ 59
def prefixEnd_685645 : Nat := 4983230072969 + 3 ^ 40 * 685645 * 2
def baseEnd_685645 : Nat := 104315686919133376143491

theorem tailTrace_685645 : CollatzResearch.WordTrace tailWord_685645 prefixEnd_685645 104315686919133376143491 := by
  unfold tailWord_685645
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007527601032738688394389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671685067355159125596259 25007527601032738688394389)
  ·
    refine ⟨1172227856298409626018487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25007527601032738688394389 1172227856298409626018487)
    ·
      refine ⟨1758341784447614439027731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172227856298409626018487 1758341784447614439027731)
      ·
        refine ⟨2637512676671421658541597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758341784447614439027731 2637512676671421658541597)
        ·
          refine ⟨989067253751783121953099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2637512676671421658541597 989067253751783121953099)
          ·
            refine ⟨1483600880627674682929649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989067253751783121953099 1483600880627674682929649)
            ·
              refine ⟨1112700660470756012197237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483600880627674682929649 1112700660470756012197237)
              ·
                refine ⟨104315686919133376143491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1112700660470756012197237 104315686919133376143491)
                ·
                  rfl

theorem cell20_685645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_685645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685645 prefixEnd_685645 := by exact prefixLift 685645
  have htrace : WordTrace (prefixWord ++ tailWord_685645) baseStart_685645 baseEnd_685645 := by
    simpa [prefixWord, tailWord_685645, baseEnd_685645] using wordTrace_append hprefix tailTrace_685645
  have hstable : (prefixWord ++ tailWord_685645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685645).length < 2 ^ (prefixWord ++ tailWord_685645).sum := by decide
  have hdescent : baseEnd_685645 < baseStart_685645 := by decide
  rcases family_descends (prefixWord ++ tailWord_685645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685649 : List Nat := [1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_685649 : Nat := 118140960795 + 685649 * 2 ^ 59
def prefixEnd_685649 : Nat := 4983230072969 + 3 ^ 40 * 685649 * 2
def baseEnd_685649 : Nat := 104316295488797964099041

theorem tailTrace_685649 : CollatzResearch.WordTrace tailWord_685649 prefixEnd_685649 104316295488797964099041 := by
  unfold tailWord_685649
  simp only [CollatzResearch.WordTrace]
  refine ⟨25007673493018247371540001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16671782328678831581026667 25007673493018247371540001)
  ·
    refine ⟨18755755119763685528655001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25007673493018247371540001 18755755119763685528655001)
    ·
      refine ⟨14066816339822764146491251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18755755119763685528655001 14066816339822764146491251)
      ·
        refine ⟨21100224509734146219736877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14066816339822764146491251 21100224509734146219736877)
        ·
          refine ⟨7912584191150304832401329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21100224509734146219736877 7912584191150304832401329)
          ·
            refine ⟨5934438143362728624300997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7912584191150304832401329 5934438143362728624300997)
            ·
              refine ⟨1112707151880511617056437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5934438143362728624300997 1112707151880511617056437)
              ·
                refine ⟨104316295488797964099041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1112707151880511617056437 104316295488797964099041)
                ·
                  rfl

theorem cell20_685649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_685649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685649 prefixEnd_685649 := by exact prefixLift 685649
  have htrace : WordTrace (prefixWord ++ tailWord_685649) baseStart_685649 baseEnd_685649 := by
    simpa [prefixWord, tailWord_685649, baseEnd_685649] using wordTrace_append hprefix tailTrace_685649
  have hstable : (prefixWord ++ tailWord_685649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685649).length < 2 ^ (prefixWord ++ tailWord_685649).sum := by decide
  have hdescent : baseEnd_685649 < baseStart_685649 := by decide
  rcases family_descends (prefixWord ++ tailWord_685649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685693 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 2]
def baseStart_685693 : Nat := 118140960795 + 685693 * 2 ^ 59
def prefixEnd_685693 : Nat := 4983230072969 + 3 ^ 40 * 685693 * 2
def baseEnd_685693 : Nat := 312968969265325294830277

theorem tailTrace_685693 : CollatzResearch.WordTrace tailWord_685693 prefixEnd_685693 312968969265325294830277 := by
  unfold tailWord_685693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25009278304858842886141733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16672852203239228590761155 25009278304858842886141733)
  ·
    refine ⟨4689239682161033041151575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25009278304858842886141733 4689239682161033041151575)
    ·
      refine ⟨7033859523241549561727363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689239682161033041151575 7033859523241549561727363)
      ·
        refine ⟨10550789284862324342591045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033859523241549561727363 10550789284862324342591045)
        ·
          refine ⟨1978272990911685814235821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10550789284862324342591045 1978272990911685814235821)
          ·
            refine ⟨741852371591882180338433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1978272990911685814235821 741852371591882180338433)
            ·
              refine ⟨556389278693911635253825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741852371591882180338433 556389278693911635253825)
              ·
                refine ⟨417291959020433726440369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556389278693911635253825 417291959020433726440369)
                ·
                  refine ⟨312968969265325294830277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417291959020433726440369 312968969265325294830277)
                  ·
                    rfl

theorem cell20_685693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_685693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685693 prefixEnd_685693 := by exact prefixLift 685693
  have htrace : WordTrace (prefixWord ++ tailWord_685693) baseStart_685693 baseEnd_685693 := by
    simpa [prefixWord, tailWord_685693, baseEnd_685693] using wordTrace_append hprefix tailTrace_685693
  have hstable : (prefixWord ++ tailWord_685693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685693).length < 2 ^ (prefixWord ++ tailWord_685693).sum := by decide
  have hdescent : baseEnd_685693 < baseStart_685693 := by decide
  rcases family_descends (prefixWord ++ tailWord_685693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685756 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_685756 : Nat := 118140960795 + 685756 * 2 ^ 59
def prefixEnd_685756 : Nat := 4983230072969 + 3 ^ 40 * 685756 * 2
def baseEnd_685756 : Nat := 312997724181977075730019

theorem tailTrace_685756 : CollatzResearch.WordTrace tailWord_685756 prefixEnd_685756 312997724181977075730019 := by
  unfold tailWord_685756
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505788051815302322842561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16674384069087069763790081 12505788051815302322842561)
  ·
    refine ⟨9379341038861476742131921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12505788051815302322842561 9379341038861476742131921)
    ·
      refine ⟨7034505779146107556598941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9379341038861476742131921 7034505779146107556598941)
      ·
        refine ⟨2637939667179790333724603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7034505779146107556598941 2637939667179790333724603)
        ·
          refine ⟨3956909500769685500586905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637939667179790333724603 3956909500769685500586905)
          ·
            refine ⟨2967682125577264125440179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956909500769685500586905 2967682125577264125440179)
            ·
              refine ⟨4451523188365896188160269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967682125577264125440179 4451523188365896188160269)
              ·
                refine ⟨1669321195637211070560101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4451523188365896188160269 1669321195637211070560101)
                ·
                  refine ⟨312997724181977075730019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1669321195637211070560101 312997724181977075730019)
                  ·
                    rfl

theorem cell20_685756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_685756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685756 prefixEnd_685756 := by exact prefixLift 685756
  have htrace : WordTrace (prefixWord ++ tailWord_685756) baseStart_685756 baseEnd_685756 := by
    simpa [prefixWord, tailWord_685756, baseEnd_685756] using wordTrace_append hprefix tailTrace_685756
  have hstable : (prefixWord ++ tailWord_685756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685756).length < 2 ^ (prefixWord ++ tailWord_685756).sum := by decide
  have hdescent : baseEnd_685756 < baseStart_685756 := by decide
  rcases family_descends (prefixWord ++ tailWord_685756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685780 : List Nat := [2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_685780 : Nat := 118140960795 + 685780 * 2 ^ 59
def prefixEnd_685780 : Nat := 4983230072969 + 3 ^ 40 * 685780 * 2
def baseEnd_685780 : Nat := 104336226145313219643307

theorem tailTrace_685780 : CollatzResearch.WordTrace tailWord_685780 prefixEnd_685780 104336226145313219643307 := by
  unfold tailWord_685780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506225727771828372279397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16674967637029104496372529 12506225727771828372279397)
  ·
    refine ⟨2344917323957217819802387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12506225727771828372279397 2344917323957217819802387)
    ·
      refine ⟨3517375985935826729703581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344917323957217819802387 3517375985935826729703581)
      ·
        refine ⟨1319015994725935023638843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3517375985935826729703581 1319015994725935023638843)
        ·
          refine ⟨1978523992088902535458265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319015994725935023638843 1978523992088902535458265)
          ·
            refine ⟨1483892994066676901593699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978523992088902535458265 1483892994066676901593699)
            ·
              refine ⟨2225839491100015352390549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483892994066676901593699 2225839491100015352390549)
              ·
                refine ⟨104336226145313219643307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2225839491100015352390549 104336226145313219643307)
                ·
                  rfl

theorem cell20_685780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_685780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685780 prefixEnd_685780 := by exact prefixLift 685780
  have htrace : WordTrace (prefixWord ++ tailWord_685780) baseStart_685780 baseEnd_685780 := by
    simpa [prefixWord, tailWord_685780, baseEnd_685780] using wordTrace_append hprefix tailTrace_685780
  have hstable : (prefixWord ++ tailWord_685780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685780).length < 2 ^ (prefixWord ++ tailWord_685780).sum := by decide
  have hdescent : baseEnd_685780 < baseStart_685780 := by decide
  rcases family_descends (prefixWord ++ tailWord_685780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685891 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_685891 : Nat := 118140960795 + 685891 * 2 ^ 59
def prefixEnd_685891 : Nat := 4983230072969 + 3 ^ 40 * 685891 * 2
def baseEnd_685891 : Nat := 313059341860516606229467

theorem tailTrace_685891 : CollatzResearch.WordTrace tailWord_685891 prefixEnd_685891 313059341860516606229467 := by
  unfold tailWord_685891
  simp only [CollatzResearch.WordTrace]
  refine ⟨25016499958141522701849527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16677666638761015134566351 25016499958141522701849527)
  ·
    refine ⟨37524749937212284052774291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25016499958141522701849527 37524749937212284052774291)
    ·
      refine ⟨56287124905818426079161437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37524749937212284052774291 56287124905818426079161437)
      ·
        refine ⟨21107671839681909779685539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56287124905818426079161437 21107671839681909779685539)
        ·
          refine ⟨31661507759522864669528309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21107671839681909779685539 31661507759522864669528309)
          ·
            refine ⟨2968266352455268562768279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31661507759522864669528309 2968266352455268562768279)
            ·
              refine ⟨4452399528682902844152419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968266352455268562768279 4452399528682902844152419)
              ·
                refine ⟨6678599293024354266228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452399528682902844152419 6678599293024354266228629)
                ·
                  refine ⟨313059341860516606229467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678599293024354266228629 313059341860516606229467)
                  ·
                    rfl

theorem cell20_685891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_685891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685891 prefixEnd_685891 := by exact prefixLift 685891
  have htrace : WordTrace (prefixWord ++ tailWord_685891) baseStart_685891 baseEnd_685891 := by
    simpa [prefixWord, tailWord_685891, baseEnd_685891] using wordTrace_append hprefix tailTrace_685891
  have hstable : (prefixWord ++ tailWord_685891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685891).length < 2 ^ (prefixWord ++ tailWord_685891).sum := by decide
  have hdescent : baseEnd_685891 < baseStart_685891 := by decide
  rcases family_descends (prefixWord ++ tailWord_685891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685936 : List Nat := [2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_685936 : Nat := 118140960795 + 685936 * 2 ^ 59
def prefixEnd_685936 : Nat := 4983230072969 + 3 ^ 40 * 685936 * 2
def baseEnd_685936 : Nat := 104359960362232149909761

theorem tailTrace_685936 : CollatzResearch.WordTrace tailWord_685936 prefixEnd_685936 104359960362232149909761 := by
  unfold tailWord_685936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509070621489247693618831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16678760828652330258158441 12509070621489247693618831)
  ·
    refine ⟨18763605932233871540428247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12509070621489247693618831 18763605932233871540428247)
    ·
      refine ⟨28145408898350807310642371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18763605932233871540428247 28145408898350807310642371)
      ·
        refine ⟨42218113347526210965963557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28145408898350807310642371 42218113347526210965963557)
        ·
          refine ⟨7915896252661164556118167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42218113347526210965963557 7915896252661164556118167)
          ·
            refine ⟨11873844378991746834177251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7915896252661164556118167 11873844378991746834177251)
            ·
              refine ⟨17810766568487620251265877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873844378991746834177251 17810766568487620251265877)
              ·
                refine ⟨104359960362232149909761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17810766568487620251265877 104359960362232149909761)
                ·
                  rfl

theorem cell20_685936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_685936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685936 prefixEnd_685936 := by exact prefixLift 685936
  have htrace : WordTrace (prefixWord ++ tailWord_685936) baseStart_685936 baseEnd_685936 := by
    simpa [prefixWord, tailWord_685936, baseEnd_685936] using wordTrace_append hprefix tailTrace_685936
  have hstable : (prefixWord ++ tailWord_685936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685936).length < 2 ^ (prefixWord ++ tailWord_685936).sum := by decide
  have hdescent : baseEnd_685936 < baseStart_685936 := by decide
  rcases family_descends (prefixWord ++ tailWord_685936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685959 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 2]
def baseStart_685959 : Nat := 118140960795 + 685959 * 2 ^ 59
def prefixEnd_685959 : Nat := 4983230072969 + 3 ^ 40 * 685959 * 2
def baseEnd_685959 : Nat := 313090378913410591962523

theorem tailTrace_685959 : CollatzResearch.WordTrace tailWord_685959 prefixEnd_685959 313090378913410591962523 := by
  unfold tailWord_685959
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018980121895170315324931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16679320081263446876883287 25018980121895170315324931)
  ·
    refine ⟨37528470182842755472987397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25018980121895170315324931 37528470182842755472987397)
    ·
      refine ⟨7036588159283016651185137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37528470182842755472987397 7036588159283016651185137)
      ·
        refine ⟨5277441119462262488388853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7036588159283016651185137 5277441119462262488388853)
        ·
          refine ⟨494760104949587108286455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5277441119462262488388853 494760104949587108286455)
          ·
            refine ⟨742140157424380662429683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494760104949587108286455 742140157424380662429683)
            ·
              refine ⟨1113210236136570993644525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742140157424380662429683 1113210236136570993644525)
              ·
                refine ⟨417453838551214122616697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1113210236136570993644525 417453838551214122616697)
                ·
                  refine ⟨313090378913410591962523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417453838551214122616697 313090378913410591962523)
                  ·
                    rfl

theorem cell20_685959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2].length) (baseStart_685959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685959 prefixEnd_685959 := by exact prefixLift 685959
  have htrace : WordTrace (prefixWord ++ tailWord_685959) baseStart_685959 baseEnd_685959 := by
    simpa [prefixWord, tailWord_685959, baseEnd_685959] using wordTrace_append hprefix tailTrace_685959
  have hstable : (prefixWord ++ tailWord_685959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685959).length < 2 ^ (prefixWord ++ tailWord_685959).sum := by decide
  have hdescent : baseEnd_685959 < baseStart_685959 := by decide
  rcases family_descends (prefixWord ++ tailWord_685959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685970 : List Nat := [3, 2, 3, 2, 1, 3, 6]
def baseStart_685970 : Nat := 118140960795 + 685970 * 2 ^ 59
def prefixEnd_685970 : Nat := 4983230072969 + 3 ^ 40 * 685970 * 2
def baseEnd_685970 : Nat := 34788377734793715843979

theorem tailTrace_685970 : CollatzResearch.WordTrace tailWord_685970 prefixEnd_685970 34788377734793715843979 := by
  unfold tailWord_685970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254845331213829798493841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16679587549903546129316909 6254845331213829798493841)
  ·
    refine ⟨4691133998410372348870381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6254845331213829798493841 4691133998410372348870381)
    ·
      refine ⟨1759175249403889630826393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4691133998410372348870381 1759175249403889630826393)
      ·
        refine ⟨1319381437052917223119795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1759175249403889630826393 1319381437052917223119795)
        ·
          refine ⟨1979072155579375834679693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319381437052917223119795 1979072155579375834679693)
          ·
            refine ⟨742152058342265938004885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1979072155579375834679693 742152058342265938004885)
            ·
              refine ⟨34788377734793715843979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 742152058342265938004885 34788377734793715843979)
              ·
                rfl

theorem cell20_685970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_685970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685970 prefixEnd_685970 := by exact prefixLift 685970
  have htrace : WordTrace (prefixWord ++ tailWord_685970) baseStart_685970 baseEnd_685970 := by
    simpa [prefixWord, tailWord_685970, baseEnd_685970] using wordTrace_append hprefix tailTrace_685970
  have hstable : (prefixWord ++ tailWord_685970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685970).length < 2 ^ (prefixWord ++ tailWord_685970).sum := by decide
  have hdescent : baseEnd_685970 < baseStart_685970 := by decide
  rcases family_descends (prefixWord ++ tailWord_685970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685991 : List Nat := [1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_685991 : Nat := 118140960795 + 685991 * 2 ^ 59
def prefixEnd_685991 : Nat := 4983230072969 + 3 ^ 40 * 685991 * 2
def baseEnd_685991 : Nat := 104368328195120234298575

theorem tailTrace_685991 : CollatzResearch.WordTrace tailWord_685991 prefixEnd_685991 104368328195120234298575 := by
  unfold tailWord_685991
  simp only [CollatzResearch.WordTrace]
  refine ⟨25020147257779239780489827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16680098171852826520326551 25020147257779239780489827)
  ·
    refine ⟨37530220886668859670734741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25020147257779239780489827 37530220886668859670734741)
    ·
      refine ⟨1759229104062602797065691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37530220886668859670734741 1759229104062602797065691)
      ·
        refine ⟨2638843656093904195598537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759229104062602797065691 2638843656093904195598537)
        ·
          refine ⟨1979132742070428146698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638843656093904195598537 1979132742070428146698903)
          ·
            refine ⟨2968699113105642220048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979132742070428146698903 2968699113105642220048355)
            ·
              refine ⟨4453048669658463330072533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968699113105642220048355 4453048669658463330072533)
              ·
                refine ⟨104368328195120234298575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4453048669658463330072533 104368328195120234298575)
                ·
                  rfl

theorem cell20_685991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_685991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_685991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_685991 prefixEnd_685991 := by exact prefixLift 685991
  have htrace : WordTrace (prefixWord ++ tailWord_685991) baseStart_685991 baseEnd_685991 := by
    simpa [prefixWord, tailWord_685991, baseEnd_685991] using wordTrace_append hprefix tailTrace_685991
  have hstable : (prefixWord ++ tailWord_685991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685991).length < 2 ^ (prefixWord ++ tailWord_685991).sum := by decide
  have hdescent : baseEnd_685991 < baseStart_685991 := by decide
  rcases family_descends (prefixWord ++ tailWord_685991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686081 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_686081 : Nat := 118140960795 + 686081 * 2 ^ 59
def prefixEnd_686081 : Nat := 4983230072969 + 3 ^ 40 * 686081 * 2
def baseEnd_686081 : Nat := 313146063037720389895357

theorem tailTrace_686081 : CollatzResearch.WordTrace tailWord_686081 prefixEnd_686081 313146063037720389895357 := by
  unfold tailWord_686081
  simp only [CollatzResearch.WordTrace]
  refine ⟨25023429827453185151266097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16682286551635456767510731 25023429827453185151266097)
  ·
    refine ⟨18767572370589888863449573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25023429827453185151266097 18767572370589888863449573)
    ·
      refine ⟨3518919819485604161896795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18767572370589888863449573 3518919819485604161896795)
      ·
        refine ⟨5278379729228406242845193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518919819485604161896795 5278379729228406242845193)
        ·
          refine ⟨3958784796921304682133895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278379729228406242845193 3958784796921304682133895)
          ·
            refine ⟨5938177195381957023200843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958784796921304682133895 5938177195381957023200843)
            ·
              refine ⟨8907265793072935534801265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938177195381957023200843 8907265793072935534801265)
              ·
                refine ⟨6680449344804701651100949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8907265793072935534801265 6680449344804701651100949)
                ·
                  refine ⟨313146063037720389895357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6680449344804701651100949 313146063037720389895357)
                  ·
                    rfl

theorem cell20_686081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_686081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686081 prefixEnd_686081 := by exact prefixLift 686081
  have htrace : WordTrace (prefixWord ++ tailWord_686081) baseStart_686081 baseEnd_686081 := by
    simpa [prefixWord, tailWord_686081, baseEnd_686081] using wordTrace_append hprefix tailTrace_686081
  have hstable : (prefixWord ++ tailWord_686081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686081).length < 2 ^ (prefixWord ++ tailWord_686081).sum := by decide
  have hdescent : baseEnd_686081 < baseStart_686081 := by decide
  rcases family_descends (prefixWord ++ tailWord_686081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686084 : List Nat := [2, 3, 2, 4, 1, 1, 7]
def baseStart_686084 : Nat := 118140960795 + 686084 * 2 ^ 59
def prefixEnd_686084 : Nat := 4983230072969 + 3 ^ 40 * 686084 * 2
def baseEnd_686084 : Nat := 34794159146607301421705

theorem tailTrace_686084 : CollatzResearch.WordTrace tailWord_686084 prefixEnd_686084 34794159146607301421705 := by
  unfold tailWord_686084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511769623221158331812653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16682359497628211109083537 12511769623221158331812653)
  ·
    refine ⟨4691913608707934374429745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12511769623221158331812653 4691913608707934374429745)
    ·
      refine ⟨3518935206530950780822309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4691913608707934374429745 3518935206530950780822309)
      ·
        refine ⟨659800351224553271404183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3518935206530950780822309 659800351224553271404183)
        ·
          refine ⟨989700526836829907106275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659800351224553271404183 989700526836829907106275)
          ·
            refine ⟨1484550790255244860659413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989700526836829907106275 1484550790255244860659413)
            ·
              refine ⟨34794159146607301421705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1484550790255244860659413 34794159146607301421705)
              ·
                rfl

theorem cell20_686084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_686084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686084 prefixEnd_686084 := by exact prefixLift 686084
  have htrace : WordTrace (prefixWord ++ tailWord_686084) baseStart_686084 baseEnd_686084 := by
    simpa [prefixWord, tailWord_686084, baseEnd_686084] using wordTrace_append hprefix tailTrace_686084
  have hstable : (prefixWord ++ tailWord_686084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686084).length < 2 ^ (prefixWord ++ tailWord_686084).sum := by decide
  have hdescent : baseEnd_686084 < baseStart_686084 := by decide
  rcases family_descends (prefixWord ++ tailWord_686084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686088 : List Nat := [2, 1, 3, 2, 1, 2, 9]
def baseStart_686088 : Nat := 118140960795 + 686088 * 2 ^ 59
def prefixEnd_686088 : Nat := 4983230072969 + 3 ^ 40 * 686088 * 2
def baseEnd_686088 : Nat := 34794362003162164073555

theorem tailTrace_686088 : CollatzResearch.WordTrace tailWord_686088 prefixEnd_686088 34794362003162164073555 := by
  unfold tailWord_686088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511842569213912673385459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16682456758951883564513945 12511842569213912673385459)
  ·
    refine ⟨18767763853820869010078189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12511842569213912673385459 18767763853820869010078189)
    ·
      refine ⟨7037911445182825878779321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18767763853820869010078189 7037911445182825878779321)
      ·
        refine ⟨5278433583887119409084491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7037911445182825878779321 5278433583887119409084491)
        ·
          refine ⟨7917650375830679113626737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278433583887119409084491 7917650375830679113626737)
          ·
            refine ⟨5938237781873009335220053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917650375830679113626737 5938237781873009335220053)
            ·
              refine ⟨34794362003162164073555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5938237781873009335220053 34794362003162164073555)
              ·
                rfl

theorem cell20_686088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 9].length) (baseStart_686088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686088 prefixEnd_686088 := by exact prefixLift 686088
  have htrace : WordTrace (prefixWord ++ tailWord_686088) baseStart_686088 baseEnd_686088 := by
    simpa [prefixWord, tailWord_686088, baseEnd_686088] using wordTrace_append hprefix tailTrace_686088
  have hstable : (prefixWord ++ tailWord_686088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686088).length < 2 ^ (prefixWord ++ tailWord_686088).sum := by decide
  have hdescent : baseEnd_686088 < baseStart_686088 := by decide
  rcases family_descends (prefixWord ++ tailWord_686088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686108 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_686108 : Nat := 118140960795 + 686108 * 2 ^ 59
def prefixEnd_686108 : Nat := 4983230072969 + 3 ^ 40 * 686108 * 2
def baseEnd_686108 : Nat := 313158386573428295995247

theorem tailTrace_686108 : CollatzResearch.WordTrace tailWord_686108 prefixEnd_686108 313158386573428295995247 := by
  unfold tailWord_686108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512207299177684381249489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16682943065570245841665985 12512207299177684381249489)
  ·
    refine ⟨9384155474383263285937117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12512207299177684381249489 9384155474383263285937117)
    ·
      refine ⟨3519058302893723732226419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9384155474383263285937117 3519058302893723732226419)
      ·
        refine ⟨5278587454340585598339629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519058302893723732226419 5278587454340585598339629)
        ·
          refine ⟨1979470295377719599377361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5278587454340585598339629 1979470295377719599377361)
          ·
            refine ⟨1484602721533289699533021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1979470295377719599377361 1484602721533289699533021)
            ·
              refine ⟨556726020574983637324883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1484602721533289699533021 556726020574983637324883)
              ·
                refine ⟨835089030862475455987325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556726020574983637324883 835089030862475455987325)
                ·
                  refine ⟨313158386573428295995247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835089030862475455987325 313158386573428295995247)
                  ·
                    rfl

theorem cell20_686108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_686108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686108 prefixEnd_686108 := by exact prefixLift 686108
  have htrace : WordTrace (prefixWord ++ tailWord_686108) baseStart_686108 baseEnd_686108 := by
    simpa [prefixWord, tailWord_686108, baseEnd_686108] using wordTrace_append hprefix tailTrace_686108
  have hstable : (prefixWord ++ tailWord_686108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686108).length < 2 ^ (prefixWord ++ tailWord_686108).sum := by decide
  have hdescent : baseEnd_686108 < baseStart_686108 := by decide
  rcases family_descends (prefixWord ++ tailWord_686108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686122 : List Nat := [3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_686122 : Nat := 118140960795 + 686122 * 2 ^ 59
def prefixEnd_686122 : Nat := 4983230072969 + 3 ^ 40 * 686122 * 2
def baseEnd_686122 : Nat := 104388258851635489842841

theorem tailTrace_686122 : CollatzResearch.WordTrace tailWord_686122 prefixEnd_686122 104388258851635489842841 := by
  unfold tailWord_686122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256231305076162288377155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16683283480203099435672413 6256231305076162288377155)
  ·
    refine ⟨9384346957614243432565733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256231305076162288377155 9384346957614243432565733)
    ·
      refine ⟨1759565054552670643606075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9384346957614243432565733 1759565054552670643606075)
      ·
        refine ⟨2639347581829005965409113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759565054552670643606075 2639347581829005965409113)
        ·
          refine ⟨1979510686371754474056835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639347581829005965409113 1979510686371754474056835)
          ·
            refine ⟨2969266029557631711085253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979510686371754474056835 2969266029557631711085253)
            ·
              refine ⟨556737380542055945828485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2969266029557631711085253 556737380542055945828485)
              ·
                refine ⟨104388258851635489842841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 556737380542055945828485 104388258851635489842841)
                ·
                  rfl

theorem cell20_686122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_686122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686122 prefixEnd_686122 := by exact prefixLift 686122
  have htrace : WordTrace (prefixWord ++ tailWord_686122) baseStart_686122 baseEnd_686122 := by
    simpa [prefixWord, tailWord_686122, baseEnd_686122] using wordTrace_append hprefix tailTrace_686122
  have hstable : (prefixWord ++ tailWord_686122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686122).length < 2 ^ (prefixWord ++ tailWord_686122).sum := by decide
  have hdescent : baseEnd_686122 < baseStart_686122 := by decide
  rcases family_descends (prefixWord ++ tailWord_686122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686153 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 2]
def baseStart_686153 : Nat := 118140960795 + 686153 * 2 ^ 59
def prefixEnd_686153 : Nat := 4983230072969 + 3 ^ 40 * 686153 * 2
def baseEnd_686153 : Nat := 313178925799608139495063

theorem tailTrace_686153 : CollatzResearch.WordTrace tailWord_686153 prefixEnd_686153 313178925799608139495063 := by
  unfold tailWord_686153
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026055883192341447887113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684037255461560965258075 25026055883192341447887113)
  ·
    refine ⟨18769541912394256085915335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25026055883192341447887113 18769541912394256085915335)
    ·
      refine ⟨28154312868591384128873003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18769541912394256085915335 28154312868591384128873003)
      ·
        refine ⟨42231469302887076193309505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28154312868591384128873003 42231469302887076193309505)
        ·
          refine ⟨31673601977165307144982129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42231469302887076193309505 31673601977165307144982129)
          ·
            refine ⟨23755201482873980358736597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31673601977165307144982129 23755201482873980358736597)
            ·
              refine ⟨556762534754858914657889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23755201482873980358736597 556762534754858914657889)
              ·
                refine ⟨417571901066144185993417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556762534754858914657889 417571901066144185993417)
                ·
                  refine ⟨313178925799608139495063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417571901066144185993417 313178925799608139495063)
                  ·
                    rfl

theorem cell20_686153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_686153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686153 prefixEnd_686153 := by exact prefixLift 686153
  have htrace : WordTrace (prefixWord ++ tailWord_686153) baseStart_686153 baseEnd_686153 := by
    simpa [prefixWord, tailWord_686153, baseEnd_686153] using wordTrace_append hprefix tailTrace_686153
  have hstable : (prefixWord ++ tailWord_686153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686153).length < 2 ^ (prefixWord ++ tailWord_686153).sum := by decide
  have hdescent : baseEnd_686153 < baseStart_686153 := by decide
  rcases family_descends (prefixWord ++ tailWord_686153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686167 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_686167 : Nat := 118140960795 + 686167 * 2 ^ 59
def prefixEnd_686167 : Nat := 4983230072969 + 3 ^ 40 * 686167 * 2
def baseEnd_686167 : Nat := 313185315781086313028339

theorem tailTrace_686167 : CollatzResearch.WordTrace tailWord_686167 prefixEnd_686167 313185315781086313028339 := by
  unfold tailWord_686167
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026566505141621838896755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684377670094414559264503 25026566505141621838896755)
  ·
    refine ⟨37539849757712432758345133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25026566505141621838896755 37539849757712432758345133)
    ·
      refine ⟨14077443659142162284379425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37539849757712432758345133 14077443659142162284379425)
      ·
        refine ⟨10558082744356621713284569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14077443659142162284379425 10558082744356621713284569)
        ·
          refine ⟨7918562058267466284963427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10558082744356621713284569 7918562058267466284963427)
          ·
            refine ⟨11877843087401199427445141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918562058267466284963427 11877843087401199427445141)
            ·
              refine ⟨556773894721931223161491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11877843087401199427445141 556773894721931223161491)
              ·
                refine ⟨835160842082896834742237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556773894721931223161491 835160842082896834742237)
                ·
                  refine ⟨313185315781086313028339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835160842082896834742237 313185315781086313028339)
                  ·
                    rfl

theorem cell20_686167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_686167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686167 prefixEnd_686167 := by exact prefixLift 686167
  have htrace : WordTrace (prefixWord ++ tailWord_686167) baseStart_686167 baseEnd_686167 := by
    simpa [prefixWord, tailWord_686167, baseEnd_686167] using wordTrace_append hprefix tailTrace_686167
  have hstable : (prefixWord ++ tailWord_686167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686167).length < 2 ^ (prefixWord ++ tailWord_686167).sum := by decide
  have hdescent : baseEnd_686167 < baseStart_686167 := by decide
  rcases family_descends (prefixWord ++ tailWord_686167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686205 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_686205 : Nat := 118140960795 + 686205 * 2 ^ 59
def prefixEnd_686205 : Nat := 4983230072969 + 3 ^ 40 * 686205 * 2
def baseEnd_686205 : Nat := 313202660016527069761517

theorem tailTrace_686205 : CollatzResearch.WordTrace tailWord_686205 prefixEnd_686205 313202660016527069761517 := by
  unfold tailWord_686205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027952479003954328780069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16685301652669302885853379 25027952479003954328780069)
  ·
    refine ⟨4692741089813241436646263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25027952479003954328780069 4692741089813241436646263)
    ·
      refine ⟨7039111634719862154969395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4692741089813241436646263 7039111634719862154969395)
      ·
        refine ⟨10558667452079793232454093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039111634719862154969395 10558667452079793232454093)
        ·
          refine ⟨3959500294529922462170285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10558667452079793232454093 3959500294529922462170285)
          ·
            refine ⟨1484812610448720923313857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3959500294529922462170285 1484812610448720923313857)
            ·
              refine ⟨1113609457836540692485393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484812610448720923313857 1113609457836540692485393)
              ·
                refine ⟨835207093377405519364045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113609457836540692485393 835207093377405519364045)
                ·
                  refine ⟨313202660016527069761517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835207093377405519364045 313202660016527069761517)
                  ·
                    rfl

theorem cell20_686205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_686205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686205 prefixEnd_686205 := by exact prefixLift 686205
  have htrace : WordTrace (prefixWord ++ tailWord_686205) baseStart_686205 baseEnd_686205 := by
    simpa [prefixWord, tailWord_686205, baseEnd_686205] using wordTrace_append hprefix tailTrace_686205
  have hstable : (prefixWord ++ tailWord_686205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686205).length < 2 ^ (prefixWord ++ tailWord_686205).sum := by decide
  have hdescent : baseEnd_686205 < baseStart_686205 := by decide
  rcases family_descends (prefixWord ++ tailWord_686205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686257 : List Nat := [1, 2, 2, 5, 2, 1, 7]
def baseStart_686257 : Nat := 118140960795 + 686257 * 2 ^ 59
def prefixEnd_686257 : Nat := 4983230072969 + 3 ^ 40 * 686257 * 2
def baseEnd_686257 : Nat := 34802932692605111114219

theorem tailTrace_686257 : CollatzResearch.WordTrace tailWord_686257 prefixEnd_686257 34802932692605111114219 := by
  unfold tailWord_686257
  simp only [CollatzResearch.WordTrace]
  refine ⟨25029849074815567209673025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16686566049877044806448683 25029849074815567209673025)
  ·
    refine ⟨18772386806111675407254769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25029849074815567209673025 18772386806111675407254769)
    ·
      refine ⟨14079290104583756555441077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18772386806111675407254769 14079290104583756555441077)
      ·
        refine ⟨1319933447304727177072601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14079290104583756555441077 1319933447304727177072601)
        ·
          refine ⟨989950085478545382804451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319933447304727177072601 989950085478545382804451)
          ·
            refine ⟨1484925128217818074206677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989950085478545382804451 1484925128217818074206677)
            ·
              refine ⟨34802932692605111114219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1484925128217818074206677 34802932692605111114219)
              ·
                rfl

theorem cell20_686257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_686257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686257 prefixEnd_686257 := by exact prefixLift 686257
  have htrace : WordTrace (prefixWord ++ tailWord_686257) baseStart_686257 baseEnd_686257 := by
    simpa [prefixWord, tailWord_686257, baseEnd_686257] using wordTrace_append hprefix tailTrace_686257
  have hstable : (prefixWord ++ tailWord_686257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686257).length < 2 ^ (prefixWord ++ tailWord_686257).sum := by decide
  have hdescent : baseEnd_686257 < baseStart_686257 := by decide
  rcases family_descends (prefixWord ++ tailWord_686257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686322 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_686322 : Nat := 118140960795 + 686322 * 2 ^ 59
def prefixEnd_686322 : Nat := 4983230072969 + 3 ^ 40 * 686322 * 2
def baseEnd_686322 : Nat := 313256062004594662861039

theorem tailTrace_686322 : CollatzResearch.WordTrace tailWord_686322 prefixEnd_686322 313256062004594662861039 := by
  unfold tailWord_686322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258054954895020827697305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16688146546386722207192813 6258054954895020827697305)
  ·
    refine ⟨4693541216171265620772979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6258054954895020827697305 4693541216171265620772979)
    ·
      refine ⟨7040311824256898431159469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4693541216171265620772979 7040311824256898431159469)
      ·
        refine ⟨2640116934096336911684801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7040311824256898431159469 2640116934096336911684801)
        ·
          refine ⟨1980087700572252683763601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2640116934096336911684801 1980087700572252683763601)
          ·
            refine ⟨1485065775429189512822701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980087700572252683763601 1485065775429189512822701)
            ·
              refine ⟨556899665785946067308513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485065775429189512822701 556899665785946067308513)
              ·
                refine ⟨417674749339459550481385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556899665785946067308513 417674749339459550481385)
                ·
                  refine ⟨313256062004594662861039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417674749339459550481385 313256062004594662861039)
                  ·
                    rfl

theorem cell20_686322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_686322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686322 prefixEnd_686322 := by exact prefixLift 686322
  have htrace : WordTrace (prefixWord ++ tailWord_686322) baseStart_686322 baseEnd_686322 := by
    simpa [prefixWord, tailWord_686322, baseEnd_686322] using wordTrace_append hprefix tailTrace_686322
  have hstable : (prefixWord ++ tailWord_686322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686322).length < 2 ^ (prefixWord ++ tailWord_686322).sum := by decide
  have hdescent : baseEnd_686322 < baseStart_686322 := by decide
  rcases family_descends (prefixWord ++ tailWord_686322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686323 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_686323 : Nat := 118140960795 + 686323 * 2 ^ 59
def prefixEnd_686323 : Nat := 4983230072969 + 3 ^ 40 * 686323 * 2
def baseEnd_686323 : Nat := 313256518431843103827701

theorem tailTrace_686323 : CollatzResearch.WordTrace tailWord_686323 prefixEnd_686323 313256518431843103827701 := by
  unfold tailWord_686323
  simp only [CollatzResearch.WordTrace]
  refine ⟨25032256292576460481575623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16688170861717640321050415 25032256292576460481575623)
  ·
    refine ⟨37548384438864690722363435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25032256292576460481575623 37548384438864690722363435)
    ·
      refine ⟨56322576658297036083545153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37548384438864690722363435 56322576658297036083545153)
      ·
        refine ⟨42241932493722777062658865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56322576658297036083545153 42241932493722777062658865)
        ·
          refine ⟨31681449370292082796994149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42241932493722777062658865 31681449370292082796994149)
          ·
            refine ⟨5940271756929765524436403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31681449370292082796994149 5940271756929765524436403)
            ·
              refine ⟨8910407635394648286654605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940271756929765524436403 8910407635394648286654605)
              ·
                refine ⟨3341402863272993107495477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8910407635394648286654605 3341402863272993107495477)
                ·
                  refine ⟨313256518431843103827701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3341402863272993107495477 313256518431843103827701)
                  ·
                    rfl

theorem cell20_686323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_686323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686323 prefixEnd_686323 := by exact prefixLift 686323
  have htrace : WordTrace (prefixWord ++ tailWord_686323) baseStart_686323 baseEnd_686323 := by
    simpa [prefixWord, tailWord_686323, baseEnd_686323] using wordTrace_append hprefix tailTrace_686323
  have hstable : (prefixWord ++ tailWord_686323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686323).length < 2 ^ (prefixWord ++ tailWord_686323).sum := by decide
  have hdescent : baseEnd_686323 < baseStart_686323 := by decide
  rcases family_descends (prefixWord ++ tailWord_686323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686326 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_686326 : Nat := 118140960795 + 686326 * 2 ^ 59
def prefixEnd_686326 : Nat := 4983230072969 + 3 ^ 40 * 686326 * 2
def baseEnd_686326 : Nat := 313257887713588426727689

theorem tailTrace_686326 : CollatzResearch.WordTrace tailWord_686326 prefixEnd_686326 313257887713588426727689 := by
  unfold tailWord_686326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564522856972849499620927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16688243807710394662623221 1564522856972849499620927)
  ·
    refine ⟨2346784285459274249431391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1564522856972849499620927 2346784285459274249431391)
    ·
      refine ⟨3520176428188911374147087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346784285459274249431391 3520176428188911374147087)
      ·
        refine ⟨5280264642283367061220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520176428188911374147087 5280264642283367061220631)
        ·
          refine ⟨7920396963425050591830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280264642283367061220631 7920396963425050591830947)
          ·
            refine ⟨11880595445137575887746421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920396963425050591830947 11880595445137575887746421)
            ·
              refine ⟨1113805822981647739476227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11880595445137575887746421 1113805822981647739476227)
              ·
                refine ⟨1670708734472471609214341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113805822981647739476227 1670708734472471609214341)
                ·
                  refine ⟨313257887713588426727689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670708734472471609214341 313257887713588426727689)
                  ·
                    rfl

theorem cell20_686326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_686326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686326 prefixEnd_686326 := by exact prefixLift 686326
  have htrace : WordTrace (prefixWord ++ tailWord_686326) baseStart_686326 baseEnd_686326 := by
    simpa [prefixWord, tailWord_686326, baseEnd_686326] using wordTrace_append hprefix tailTrace_686326
  have hstable : (prefixWord ++ tailWord_686326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686326).length < 2 ^ (prefixWord ++ tailWord_686326).sum := by decide
  have hdescent : baseEnd_686326 < baseStart_686326 := by decide
  rcases family_descends (prefixWord ++ tailWord_686326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686364 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_686364 : Nat := 118140960795 + 686364 * 2 ^ 59
def prefixEnd_686364 : Nat := 4983230072969 + 3 ^ 40 * 686364 * 2
def baseEnd_686364 : Nat := 313275231949029183460867

theorem tailTrace_686364 : CollatzResearch.WordTrace tailWord_686364 prefixEnd_686364 313275231949029183460867 := by
  unfold tailWord_686364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516875842713962241909073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16689167790285282989212097 12516875842713962241909073)
  ·
    refine ⟨9387656882035471681431805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12516875842713962241909073 9387656882035471681431805)
    ·
      refine ⟨3520371330763301880536927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9387656882035471681431805 3520371330763301880536927)
      ·
        refine ⟨5280556996144952820805391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520371330763301880536927 5280556996144952820805391)
        ·
          refine ⟨7920835494217429231208087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280556996144952820805391 7920835494217429231208087)
          ·
            refine ⟨11881253241326143846812131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7920835494217429231208087 11881253241326143846812131)
            ·
              refine ⟨17821879861989215770218197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11881253241326143846812131 17821879861989215770218197)
              ·
                refine ⟨417700309265372244614489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17821879861989215770218197 417700309265372244614489)
                ·
                  refine ⟨313275231949029183460867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417700309265372244614489 313275231949029183460867)
                  ·
                    rfl

theorem cell20_686364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_686364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686364 prefixEnd_686364 := by exact prefixLift 686364
  have htrace : WordTrace (prefixWord ++ tailWord_686364) baseStart_686364 baseEnd_686364 := by
    simpa [prefixWord, tailWord_686364, baseEnd_686364] using wordTrace_append hprefix tailTrace_686364
  have hstable : (prefixWord ++ tailWord_686364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686364).length < 2 ^ (prefixWord ++ tailWord_686364).sum := by decide
  have hdescent : baseEnd_686364 < baseStart_686364 := by decide
  rcases family_descends (prefixWord ++ tailWord_686364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686388 : List Nat := [2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_686388 : Nat := 118140960795 + 686388 * 2 ^ 59
def prefixEnd_686388 : Nat := 4983230072969 + 3 ^ 40 * 686388 * 2
def baseEnd_686388 : Nat := 104428728734330588886923

theorem tailTrace_686388 : CollatzResearch.WordTrace tailWord_686388 prefixEnd_686388 104428728734330588886923 := by
  unfold tailWord_686388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517313518670488291345909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16689751358227317721794545 12517313518670488291345909)
  ·
    refine ⟨1173498142375358277313679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12517313518670488291345909 1173498142375358277313679)
    ·
      refine ⟨1760247213563037415970519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173498142375358277313679 1760247213563037415970519)
      ·
        refine ⟨2640370820344556123955779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760247213563037415970519 2640370820344556123955779)
        ·
          refine ⟨3960556230516834185933669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640370820344556123955779 3960556230516834185933669)
          ·
            refine ⟨742604293221906409862563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3960556230516834185933669 742604293221906409862563)
            ·
              refine ⟨1113906439832859614793845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742604293221906409862563 1113906439832859614793845)
              ·
                refine ⟨104428728734330588886923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1113906439832859614793845 104428728734330588886923)
                ·
                  rfl

theorem cell20_686388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_686388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686388 prefixEnd_686388 := by exact prefixLift 686388
  have htrace : WordTrace (prefixWord ++ tailWord_686388) baseStart_686388 baseEnd_686388 := by
    simpa [prefixWord, tailWord_686388, baseEnd_686388] using wordTrace_append hprefix tailTrace_686388
  have hstable : (prefixWord ++ tailWord_686388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686388).length < 2 ^ (prefixWord ++ tailWord_686388).sum := by decide
  have hdescent : baseEnd_686388 < baseStart_686388 := by decide
  rcases family_descends (prefixWord ++ tailWord_686388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686392 : List Nat := [2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_686392 : Nat := 118140960795 + 686392 * 2 ^ 59
def prefixEnd_686392 : Nat := 4983230072969 + 3 ^ 40 * 686392 * 2
def baseEnd_686392 : Nat := 104429337303995176842473

theorem tailTrace_686392 : CollatzResearch.WordTrace tailWord_686392 prefixEnd_686392 104429337303995176842473 := by
  unfold tailWord_686392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517386464663242632918715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16689848619550990177224953 12517386464663242632918715)
  ·
    refine ⟨18776079696994863949378073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12517386464663242632918715 18776079696994863949378073)
    ·
      refine ⟨14082059772746147962033555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18776079696994863949378073 14082059772746147962033555)
      ·
        refine ⟨21123089659119221943050333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14082059772746147962033555 21123089659119221943050333)
        ·
          refine ⟨7921158622169708228643875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21123089659119221943050333 7921158622169708228643875)
          ·
            refine ⟨11881737933254562342965813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921158622169708228643875 11881737933254562342965813)
            ·
              refine ⟨1113912931242615219653045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11881737933254562342965813 1113912931242615219653045)
              ·
                refine ⟨104429337303995176842473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1113912931242615219653045 104429337303995176842473)
                ·
                  rfl

theorem cell20_686392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_686392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686392 prefixEnd_686392 := by exact prefixLift 686392
  have htrace : WordTrace (prefixWord ++ tailWord_686392) baseStart_686392 baseEnd_686392 := by
    simpa [prefixWord, tailWord_686392, baseEnd_686392] using wordTrace_append hprefix tailTrace_686392
  have hstable : (prefixWord ++ tailWord_686392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686392).length < 2 ^ (prefixWord ++ tailWord_686392).sum := by decide
  have hdescent : baseEnd_686392 < baseStart_686392 := by decide
  rcases family_descends (prefixWord ++ tailWord_686392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686440 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_686440 : Nat := 118140960795 + 686440 * 2 ^ 59
def prefixEnd_686440 : Nat := 4983230072969 + 3 ^ 40 * 686440 * 2
def baseEnd_686440 : Nat := 313309920419910696927223

theorem tailTrace_686440 : CollatzResearch.WordTrace tailWord_686440 prefixEnd_686440 313309920419910696927223 := by
  unfold tailWord_686440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518261816576294731792387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16691015755435059642389849 12518261816576294731792387)
  ·
    refine ⟨18777392724864442097688581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12518261816576294731792387 18777392724864442097688581)
    ·
      refine ⟨3520761135912082893316609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18777392724864442097688581 3520761135912082893316609)
      ·
        refine ⟨2640570851934062169987457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3520761135912082893316609 2640570851934062169987457)
        ·
          refine ⟨1980428138950546627490593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2640570851934062169987457 1980428138950546627490593)
          ·
            refine ⟨1485321104212909970617945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980428138950546627490593 1485321104212909970617945)
            ·
              refine ⟨1113990828159682477963459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485321104212909970617945 1113990828159682477963459)
              ·
                refine ⟨1670986242239523716945189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113990828159682477963459 1670986242239523716945189)
                ·
                  refine ⟨313309920419910696927223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670986242239523716945189 313309920419910696927223)
                  ·
                    rfl

theorem cell20_686440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_686440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686440 prefixEnd_686440 := by exact prefixLift 686440
  have htrace : WordTrace (prefixWord ++ tailWord_686440) baseStart_686440 baseEnd_686440 := by
    simpa [prefixWord, tailWord_686440, baseEnd_686440] using wordTrace_append hprefix tailTrace_686440
  have hstable : (prefixWord ++ tailWord_686440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686440).length < 2 ^ (prefixWord ++ tailWord_686440).sum := by decide
  have hdescent : baseEnd_686440 < baseStart_686440 := by decide
  rcases family_descends (prefixWord ++ tailWord_686440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686461 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_686461 : Nat := 118140960795 + 686461 * 2 ^ 59
def prefixEnd_686461 : Nat := 4983230072969 + 3 ^ 40 * 686461 * 2
def baseEnd_686461 : Nat := 313319505392127957227137

theorem tailTrace_686461 : CollatzResearch.WordTrace tailWord_686461 prefixEnd_686461 313319505392127957227137 := by
  unfold tailWord_686461
  simp only [CollatzResearch.WordTrace]
  refine ⟨25037289566076510050099237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16691526377384340033399491 25037289566076510050099237)
  ·
    refine ⟨4694491793639345634393607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25037289566076510050099237 4694491793639345634393607)
    ·
      refine ⟨7041737690459018451590411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4694491793639345634393607 7041737690459018451590411)
      ·
        refine ⟨10562606535688527677385617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041737690459018451590411 10562606535688527677385617)
        ·
          refine ⟨7921954901766395758039213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10562606535688527677385617 7921954901766395758039213)
          ·
            refine ⟨2970733088162398409264705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7921954901766395758039213 2970733088162398409264705)
            ·
              refine ⟨2228049816121798806948529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970733088162398409264705 2228049816121798806948529)
              ·
                refine ⟨1671037362091349105211397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228049816121798806948529 1671037362091349105211397)
                ·
                  refine ⟨313319505392127957227137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671037362091349105211397 313319505392127957227137)
                  ·
                    rfl

theorem cell20_686461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_686461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686461 prefixEnd_686461 := by exact prefixLift 686461
  have htrace : WordTrace (prefixWord ++ tailWord_686461) baseStart_686461 baseEnd_686461 := by
    simpa [prefixWord, tailWord_686461, baseEnd_686461] using wordTrace_append hprefix tailTrace_686461
  have hstable : (prefixWord ++ tailWord_686461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686461).length < 2 ^ (prefixWord ++ tailWord_686461).sum := by decide
  have hdescent : baseEnd_686461 < baseStart_686461 := by decide
  rcases family_descends (prefixWord ++ tailWord_686461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686468 : List Nat := [2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_686468 : Nat := 118140960795 + 686468 * 2 ^ 59
def prefixEnd_686468 : Nat := 4983230072969 + 3 ^ 40 * 686468 * 2
def baseEnd_686468 : Nat := 104440900127622347997925

theorem tailTrace_686468 : CollatzResearch.WordTrace tailWord_686468 prefixEnd_686468 104440900127622347997925 := by
  unfold tailWord_686468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518772438525575122802029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16691696584700766830402705 12518772438525575122802029)
  ·
    refine ⟨4694539664447090671050761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12518772438525575122802029 4694539664447090671050761)
    ·
      refine ⟨3520904748335318003288071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4694539664447090671050761 3520904748335318003288071)
      ·
        refine ⟨5281357122502977004932107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520904748335318003288071 5281357122502977004932107)
        ·
          refine ⟨7922035683754465507398161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281357122502977004932107 7922035683754465507398161)
          ·
            refine ⟨5941526762815849130548621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7922035683754465507398161 5941526762815849130548621)
            ·
              refine ⟨2228072536055943423955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5941526762815849130548621 2228072536055943423955733)
              ·
                refine ⟨104440900127622347997925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2228072536055943423955733 104440900127622347997925)
                ·
                  rfl

theorem cell20_686468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_686468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686468 prefixEnd_686468 := by exact prefixLift 686468
  have htrace : WordTrace (prefixWord ++ tailWord_686468) baseStart_686468 baseEnd_686468 := by
    simpa [prefixWord, tailWord_686468, baseEnd_686468] using wordTrace_append hprefix tailTrace_686468
  have hstable : (prefixWord ++ tailWord_686468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686468).length < 2 ^ (prefixWord ++ tailWord_686468).sum := by decide
  have hdescent : baseEnd_686468 < baseStart_686468 := by decide
  rcases family_descends (prefixWord ++ tailWord_686468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686475 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_686475 : Nat := 118140960795 + 686475 * 2 ^ 59
def prefixEnd_686475 : Nat := 4983230072969 + 3 ^ 40 * 686475 * 2
def baseEnd_686475 : Nat := 313325895373606130760413

theorem tailTrace_686475 : CollatzResearch.WordTrace tailWord_686475 prefixEnd_686475 313325895373606130760413 := by
  unfold tailWord_686475
  simp only [CollatzResearch.WordTrace]
  refine ⟨25037800188025790441108879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16691866792017193627405919 25037800188025790441108879)
  ·
    refine ⟨37556700282038685661663319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25037800188025790441108879 37556700282038685661663319)
    ·
      refine ⟨56335050423058028492494979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37556700282038685661663319 56335050423058028492494979)
      ·
        refine ⟨84502575634587042738742469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56335050423058028492494979 84502575634587042738742469)
        ·
          refine ⟨15844232931485070513514213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84502575634587042738742469 15844232931485070513514213)
          ·
            refine ⟨2970793674653450721283915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15844232931485070513514213 2970793674653450721283915)
            ·
              refine ⟨4456190511980176081925873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970793674653450721283915 4456190511980176081925873)
              ·
                refine ⟨3342142883985132061444405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456190511980176081925873 3342142883985132061444405)
                ·
                  refine ⟨313325895373606130760413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342142883985132061444405 313325895373606130760413)
                  ·
                    rfl

theorem cell20_686475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_686475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686475 prefixEnd_686475 := by exact prefixLift 686475
  have htrace : WordTrace (prefixWord ++ tailWord_686475) baseStart_686475 baseEnd_686475 := by
    simpa [prefixWord, tailWord_686475, baseEnd_686475] using wordTrace_append hprefix tailTrace_686475
  have hstable : (prefixWord ++ tailWord_686475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686475).length < 2 ^ (prefixWord ++ tailWord_686475).sum := by decide
  have hdescent : baseEnd_686475 < baseStart_686475 := by decide
  rcases family_descends (prefixWord ++ tailWord_686475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686495 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 2]
def baseStart_686495 : Nat := 118140960795 + 686495 * 2 ^ 59
def prefixEnd_686495 : Nat := 4983230072969 + 3 ^ 40 * 686495 * 2
def baseEnd_686495 : Nat := 313335023918574950093665

theorem tailTrace_686495 : CollatzResearch.WordTrace tailWord_686495 prefixEnd_686495 313335023918574950093665 := by
  unfold tailWord_686495
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038529647953333856836939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16692353098635555904557959 25038529647953333856836939)
  ·
    refine ⟨37557794471930000785255409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25038529647953333856836939 37557794471930000785255409)
    ·
      refine ⟨28168345853947500588941557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37557794471930000785255409 28168345853947500588941557)
      ·
        refine ⟨2640782423807578180213271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28168345853947500588941557 2640782423807578180213271)
        ·
          refine ⟨3961173635711367270319907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640782423807578180213271 3961173635711367270319907)
          ·
            refine ⟨5941760453567050905479861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961173635711367270319907 5941760453567050905479861)
            ·
              refine ⟨557040042521911022388737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5941760453567050905479861 557040042521911022388737)
              ·
                refine ⟨417780031891433266791553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557040042521911022388737 417780031891433266791553)
                ·
                  refine ⟨313335023918574950093665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417780031891433266791553 313335023918574950093665)
                  ·
                    rfl

theorem cell20_686495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 2].length) (baseStart_686495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686495 prefixEnd_686495 := by exact prefixLift 686495
  have htrace : WordTrace (prefixWord ++ tailWord_686495) baseStart_686495 baseEnd_686495 := by
    simpa [prefixWord, tailWord_686495, baseEnd_686495] using wordTrace_append hprefix tailTrace_686495
  have hstable : (prefixWord ++ tailWord_686495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686495).length < 2 ^ (prefixWord ++ tailWord_686495).sum := by decide
  have hdescent : baseEnd_686495 < baseStart_686495 := by decide
  rcases family_descends (prefixWord ++ tailWord_686495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686499 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_686499 : Nat := 118140960795 + 686499 * 2 ^ 59
def prefixEnd_686499 : Nat := 4983230072969 + 3 ^ 40 * 686499 * 2
def baseEnd_686499 : Nat := 313336849627568713960315

theorem tailTrace_686499 : CollatzResearch.WordTrace tailWord_686499 prefixEnd_686499 313336849627568713960315 := by
  unfold tailWord_686499
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038675539938842539982551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16692450359959228359988367 25038675539938842539982551)
  ·
    refine ⟨37558013309908263809973827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25038675539938842539982551 37558013309908263809973827)
    ·
      refine ⟨56337019964862395714960741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37558013309908263809973827 56337019964862395714960741)
      ·
        refine ⟨10563191243411699196555139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56337019964862395714960741 10563191243411699196555139)
        ·
          refine ⟨15844786865117548794832709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10563191243411699196555139 15844786865117548794832709)
          ·
            refine ⟨2970897537209540399031133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15844786865117548794832709 2970897537209540399031133)
            ·
              refine ⟨1114086576453577649636675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2970897537209540399031133 1114086576453577649636675)
              ·
                refine ⟨1671129864680366474455013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114086576453577649636675 1671129864680366474455013)
                ·
                  refine ⟨313336849627568713960315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671129864680366474455013 313336849627568713960315)
                  ·
                    rfl

theorem cell20_686499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_686499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686499 prefixEnd_686499 := by exact prefixLift 686499
  have htrace : WordTrace (prefixWord ++ tailWord_686499) baseStart_686499 baseEnd_686499 := by
    simpa [prefixWord, tailWord_686499, baseEnd_686499] using wordTrace_append hprefix tailTrace_686499
  have hstable : (prefixWord ++ tailWord_686499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686499).length < 2 ^ (prefixWord ++ tailWord_686499).sum := by decide
  have hdescent : baseEnd_686499 < baseStart_686499 := by decide
  rcases family_descends (prefixWord ++ tailWord_686499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686520 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_686520 : Nat := 118140960795 + 686520 * 2 ^ 59
def prefixEnd_686520 : Nat := 4983230072969 + 3 ^ 40 * 686520 * 2
def baseEnd_686520 : Nat := 313346434599785974260229

theorem tailTrace_686520 : CollatzResearch.WordTrace tailWord_686520 prefixEnd_686520 313346434599785974260229 := by
  unfold tailWord_686520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519720736431381563248507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16692960981908508750998009 12519720736431381563248507)
  ·
    refine ⟨18779581104647072344872761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519720736431381563248507 18779581104647072344872761)
    ·
      refine ⟨14084685828485304258654571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18779581104647072344872761 14084685828485304258654571)
      ·
        refine ⟨21127028742727956387981857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14084685828485304258654571 21127028742727956387981857)
        ·
          refine ⟨15845271557045967290986393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21127028742727956387981857 15845271557045967290986393)
          ·
            refine ⟨11883953667784475468239795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15845271557045967290986393 11883953667784475468239795)
            ·
              refine ⟨17825930501676713202359693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11883953667784475468239795 17825930501676713202359693)
              ·
                refine ⟨6684723938128767450884885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17825930501676713202359693 6684723938128767450884885)
                ·
                  refine ⟨313346434599785974260229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6684723938128767450884885 313346434599785974260229)
                  ·
                    rfl

theorem cell20_686520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_686520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686520 prefixEnd_686520 := by exact prefixLift 686520
  have htrace : WordTrace (prefixWord ++ tailWord_686520) baseStart_686520 baseEnd_686520 := by
    simpa [prefixWord, tailWord_686520, baseEnd_686520] using wordTrace_append hprefix tailTrace_686520
  have hstable : (prefixWord ++ tailWord_686520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686520).length < 2 ^ (prefixWord ++ tailWord_686520).sum := by decide
  have hdescent : baseEnd_686520 < baseStart_686520 := by decide
  rcases family_descends (prefixWord ++ tailWord_686520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686546 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_686546 : Nat := 118140960795 + 686546 * 2 ^ 59
def prefixEnd_686546 : Nat := 4983230072969 + 3 ^ 40 * 686546 * 2
def baseEnd_686546 : Nat := 313358301708245439393457

theorem tailTrace_686546 : CollatzResearch.WordTrace tailWord_686546 prefixEnd_686546 313358301708245439393457 := by
  unfold tailWord_686546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260097442692142391735873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16693593180512379711295661 6260097442692142391735873)
  ·
    refine ⟨4695073082019106793801905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6260097442692142391735873 4695073082019106793801905)
    ·
      refine ⟨3521304811514330095351429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4695073082019106793801905 3521304811514330095351429)
      ·
        refine ⟨660244652158936892878393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3521304811514330095351429 660244652158936892878393)
        ·
          refine ⟨495183489119202669658795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660244652158936892878393 495183489119202669658795)
          ·
            refine ⟨742775233678804004488193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495183489119202669658795 742775233678804004488193)
            ·
              refine ⟨557081425259103003366145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742775233678804004488193 557081425259103003366145)
              ·
                refine ⟨417811068944327252524609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557081425259103003366145 417811068944327252524609)
                ·
                  refine ⟨313358301708245439393457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417811068944327252524609 313358301708245439393457)
                  ·
                    rfl

theorem cell20_686546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_686546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686546 prefixEnd_686546 := by exact prefixLift 686546
  have htrace : WordTrace (prefixWord ++ tailWord_686546) baseStart_686546 baseEnd_686546 := by
    simpa [prefixWord, tailWord_686546, baseEnd_686546] using wordTrace_append hprefix tailTrace_686546
  have hstable : (prefixWord ++ tailWord_686546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686546).length < 2 ^ (prefixWord ++ tailWord_686546).sum := by decide
  have hdescent : baseEnd_686546 < baseStart_686546 := by decide
  rcases family_descends (prefixWord ++ tailWord_686546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686554 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_686554 : Nat := 118140960795 + 686554 * 2 ^ 59
def prefixEnd_686554 : Nat := 4983230072969 + 3 ^ 40 * 686554 * 2
def baseEnd_686554 : Nat := 313361953126232967126757

theorem tailTrace_686554 : CollatzResearch.WordTrace tailWord_686554 prefixEnd_686554 313361953126232967126757 := by
  unfold tailWord_686554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260170388684896733308679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16693787703159724622156477 6260170388684896733308679)
  ·
    refine ⟨9390255583027345099963019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6260170388684896733308679 9390255583027345099963019)
    ·
      refine ⟨14085383374541017649944529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390255583027345099963019 14085383374541017649944529)
      ·
        refine ⟨10564037530905763237458397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14085383374541017649944529 10564037530905763237458397)
        ·
          refine ⟨3961514074089661214046899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10564037530905763237458397 3961514074089661214046899)
          ·
            refine ⟨5942271111134491821070349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961514074089661214046899 5942271111134491821070349)
            ·
              refine ⟨2228351666675434432901381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5942271111134491821070349 2228351666675434432901381)
              ·
                refine ⟨417815937501643956169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2228351666675434432901381 417815937501643956169009)
                ·
                  refine ⟨313361953126232967126757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417815937501643956169009 313361953126232967126757)
                  ·
                    rfl

theorem cell20_686554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_686554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686554 prefixEnd_686554 := by exact prefixLift 686554
  have htrace : WordTrace (prefixWord ++ tailWord_686554) baseStart_686554 baseEnd_686554 := by
    simpa [prefixWord, tailWord_686554, baseEnd_686554] using wordTrace_append hprefix tailTrace_686554
  have hstable : (prefixWord ++ tailWord_686554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686554).length < 2 ^ (prefixWord ++ tailWord_686554).sum := by decide
  have hdescent : baseEnd_686554 < baseStart_686554 := by decide
  rcases family_descends (prefixWord ++ tailWord_686554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686568 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_686568 : Nat := 118140960795 + 686568 * 2 ^ 59
def prefixEnd_686568 : Nat := 4983230072969 + 3 ^ 40 * 686568 * 2
def baseEnd_686568 : Nat := 313368343107711140660033

theorem tailTrace_686568 : CollatzResearch.WordTrace tailWord_686568 prefixEnd_686568 313368343107711140660033 := by
  unfold tailWord_686568
  simp only [CollatzResearch.WordTrace]
  refine ⟨12520596088344433662122179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16694128117792578216162905 12520596088344433662122179)
  ·
    refine ⟨18780894132516650493183269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12520596088344433662122179 18780894132516650493183269)
    ·
      refine ⟨3521417649846871967471863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18780894132516650493183269 3521417649846871967471863)
      ·
        refine ⟨5282126474770307951207795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521417649846871967471863 5282126474770307951207795)
        ·
          refine ⟨7923189712155461926811693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282126474770307951207795 7923189712155461926811693)
          ·
            refine ⟨2971196142058298222554385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7923189712155461926811693 2971196142058298222554385)
            ·
              refine ⟨2228397106543723666915789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2971196142058298222554385 2228397106543723666915789)
              ·
                refine ⟨835648914953896375093421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2228397106543723666915789 835648914953896375093421)
                ·
                  refine ⟨313368343107711140660033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835648914953896375093421 313368343107711140660033)
                  ·
                    rfl

theorem cell20_686568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_686568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686568 prefixEnd_686568 := by exact prefixLift 686568
  have htrace : WordTrace (prefixWord ++ tailWord_686568) baseStart_686568 baseEnd_686568 := by
    simpa [prefixWord, tailWord_686568, baseEnd_686568] using wordTrace_append hprefix tailTrace_686568
  have hstable : (prefixWord ++ tailWord_686568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686568).length < 2 ^ (prefixWord ++ tailWord_686568).sum := by decide
  have hdescent : baseEnd_686568 < baseStart_686568 := by decide
  rcases family_descends (prefixWord ++ tailWord_686568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686578 : List Nat := [3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_686578 : Nat := 118140960795 + 686578 * 2 ^ 59
def prefixEnd_686578 : Nat := 4983230072969 + 3 ^ 40 * 686578 * 2
def baseEnd_686578 : Nat := 104457635793398516775553

theorem tailTrace_686578 : CollatzResearch.WordTrace tailWord_686578 prefixEnd_686578 104457635793398516775553 := by
  unfold tailWord_686578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260389226663159758027097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16694371271101759354738925 6260389226663159758027097)
  ·
    refine ⟨4695291919997369818520323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6260389226663159758027097 4695291919997369818520323)
    ·
      refine ⟨7042937879996054727780485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695291919997369818520323 7042937879996054727780485)
      ·
        refine ⟨1320550852499260261458841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7042937879996054727780485 1320550852499260261458841)
        ·
          refine ⟨990413139374445196094131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320550852499260261458841 990413139374445196094131)
          ·
            refine ⟨1485619709061667794141197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990413139374445196094131 1485619709061667794141197)
            ·
              refine ⟨557107390898125422802949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485619709061667794141197 557107390898125422802949)
              ·
                refine ⟨104457635793398516775553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557107390898125422802949 104457635793398516775553)
                ·
                  rfl

theorem cell20_686578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_686578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686578 prefixEnd_686578 := by exact prefixLift 686578
  have htrace : WordTrace (prefixWord ++ tailWord_686578) baseStart_686578 baseEnd_686578 := by
    simpa [prefixWord, tailWord_686578, baseEnd_686578] using wordTrace_append hprefix tailTrace_686578
  have hstable : (prefixWord ++ tailWord_686578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686578).length < 2 ^ (prefixWord ++ tailWord_686578).sum := by decide
  have hdescent : baseEnd_686578 < baseStart_686578 := by decide
  rcases family_descends (prefixWord ++ tailWord_686578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686589 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_686589 : Nat := 118140960795 + 686589 * 2 ^ 59
def prefixEnd_686589 : Nat := 4983230072969 + 3 ^ 40 * 686589 * 2
def baseEnd_686589 : Nat := 313377928079928400959947

theorem tailTrace_686589 : CollatzResearch.WordTrace tailWord_686589 prefixEnd_686589 313377928079928400959947 := by
  unfold tailWord_686589
  simp only [CollatzResearch.WordTrace]
  refine ⟨25041958109612787910758821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16694638739741858607172547 25041958109612787910758821)
  ·
    refine ⟨4695367145552397733267279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25041958109612787910758821 4695367145552397733267279)
    ·
      refine ⟨7043050718328596599900919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695367145552397733267279 7043050718328596599900919)
      ·
        refine ⟨10564576077492894899851379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7043050718328596599900919 10564576077492894899851379)
        ·
          refine ⟨15846864116239342349777069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564576077492894899851379 15846864116239342349777069)
          ·
            refine ⟨5942574043589753381166401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15846864116239342349777069 5942574043589753381166401)
            ·
              refine ⟨4456930532692315035874801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5942574043589753381166401 4456930532692315035874801)
              ·
                refine ⟨3342697899519236276906101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4456930532692315035874801 3342697899519236276906101)
                ·
                  refine ⟨313377928079928400959947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342697899519236276906101 313377928079928400959947)
                  ·
                    rfl

theorem cell20_686589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_686589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686589 prefixEnd_686589 := by exact prefixLift 686589
  have htrace : WordTrace (prefixWord ++ tailWord_686589) baseStart_686589 baseEnd_686589 := by
    simpa [prefixWord, tailWord_686589, baseEnd_686589] using wordTrace_append hprefix tailTrace_686589
  have hstable : (prefixWord ++ tailWord_686589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686589).length < 2 ^ (prefixWord ++ tailWord_686589).sum := by decide
  have hdescent : baseEnd_686589 < baseStart_686589 := by decide
  rcases family_descends (prefixWord ++ tailWord_686589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686598 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_686598 : Nat := 118140960795 + 686598 * 2 ^ 59
def prefixEnd_686598 : Nat := 4983230072969 + 3 ^ 40 * 686598 * 2
def baseEnd_686598 : Nat := 313382035925164369659911

theorem tailTrace_686598 : CollatzResearch.WordTrace tailWord_686598 prefixEnd_686598 313382035925164369659911 := by
  unfold tailWord_686598
  simp only [CollatzResearch.WordTrace]
  refine ⟨782571448955630701494889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16694857577720121631890965 782571448955630701494889)
  ·
    refine ⟨586928586716723026121167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 782571448955630701494889 586928586716723026121167)
    ·
      refine ⟨880392880075084539181751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586928586716723026121167 880392880075084539181751)
      ·
        refine ⟨1320589320112626808772627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880392880075084539181751 1320589320112626808772627)
        ·
          refine ⟨1980883980168940213158941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320589320112626808772627 1980883980168940213158941)
          ·
            refine ⟨742831492563352579934603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1980883980168940213158941 742831492563352579934603)
            ·
              refine ⟨1114247238845028869901905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742831492563352579934603 1114247238845028869901905)
              ·
                refine ⟨835685429133771652426429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114247238845028869901905 835685429133771652426429)
                ·
                  refine ⟨313382035925164369659911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835685429133771652426429 313382035925164369659911)
                  ·
                    rfl

theorem cell20_686598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_686598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686598 prefixEnd_686598 := by exact prefixLift 686598
  have htrace : WordTrace (prefixWord ++ tailWord_686598) baseStart_686598 baseEnd_686598 := by
    simpa [prefixWord, tailWord_686598, baseEnd_686598] using wordTrace_append hprefix tailTrace_686598
  have hstable : (prefixWord ++ tailWord_686598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686598).length < 2 ^ (prefixWord ++ tailWord_686598).sum := by decide
  have hdescent : baseEnd_686598 < baseStart_686598 := by decide
  rcases family_descends (prefixWord ++ tailWord_686598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686606 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_686606 : Nat := 118140960795 + 686606 * 2 ^ 59
def prefixEnd_686606 : Nat := 4983230072969 + 3 ^ 40 * 686606 * 2
def baseEnd_686606 : Nat := 313385687343151897393211

theorem tailTrace_686606 : CollatzResearch.WordTrace tailWord_686606 prefixEnd_686606 313385687343151897393211 := by
  unfold tailWord_686606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130322268818899976765959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16695052100367466542751781 3130322268818899976765959)
  ·
    refine ⟨4695483403228349965148939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130322268818899976765959 4695483403228349965148939)
    ·
      refine ⟨7043225104842524947723409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4695483403228349965148939 7043225104842524947723409)
      ·
        refine ⟨5282418828631893710792557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7043225104842524947723409 5282418828631893710792557)
        ·
          refine ⟨1980907060736960141547209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5282418828631893710792557 1980907060736960141547209)
          ·
            refine ⟨1485680295552720106160407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1980907060736960141547209 1485680295552720106160407)
            ·
              refine ⟨2228520443329080159240611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485680295552720106160407 2228520443329080159240611)
              ·
                refine ⟨3342780664993620238860917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228520443329080159240611 3342780664993620238860917)
                ·
                  refine ⟨313385687343151897393211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3342780664993620238860917 313385687343151897393211)
                  ·
                    rfl

theorem cell20_686606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_686606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686606 prefixEnd_686606 := by exact prefixLift 686606
  have htrace : WordTrace (prefixWord ++ tailWord_686606) baseStart_686606 baseEnd_686606 := by
    simpa [prefixWord, tailWord_686606, baseEnd_686606] using wordTrace_append hprefix tailTrace_686606
  have hstable : (prefixWord ++ tailWord_686606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686606).length < 2 ^ (prefixWord ++ tailWord_686606).sum := by decide
  have hdescent : baseEnd_686606 < baseStart_686606 := by decide
  rcases family_descends (prefixWord ++ tailWord_686606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686613 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_686613 : Nat := 118140960795 + 686613 * 2 ^ 59
def prefixEnd_686613 : Nat := 4983230072969 + 3 ^ 40 * 686613 * 2
def baseEnd_686613 : Nat := 313388882333890984159849

theorem tailTrace_686613 : CollatzResearch.WordTrace tailWord_686613 prefixEnd_686613 313388882333890984159849 := by
  unfold tailWord_686613
  simp only [CollatzResearch.WordTrace]
  refine ⟨25042833461525840009632493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16695222307683893339754995 25042833461525840009632493)
  ·
    refine ⟨9391062548072190003612185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25042833461525840009632493 9391062548072190003612185)
    ·
      refine ⟨7043296911054142502709139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9391062548072190003612185 7043296911054142502709139)
      ·
        refine ⟨10564945366581213754063709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7043296911054142502709139 10564945366581213754063709)
        ·
          refine ⟨3961854512467955157773891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10564945366581213754063709 3961854512467955157773891)
          ·
            refine ⟨5942781768701932736660837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961854512467955157773891 5942781768701932736660837)
            ·
              refine ⟨1114271581631612388123907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5942781768701932736660837 1114271581631612388123907)
              ·
                refine ⟨1671407372447418582185861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114271581631612388123907 1671407372447418582185861)
                ·
                  refine ⟨313388882333890984159849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671407372447418582185861 313388882333890984159849)
                  ·
                    rfl

theorem cell20_686613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_686613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686613 prefixEnd_686613 := by exact prefixLift 686613
  have htrace : WordTrace (prefixWord ++ tailWord_686613) baseStart_686613 baseEnd_686613 := by
    simpa [prefixWord, tailWord_686613, baseEnd_686613] using wordTrace_append hprefix tailTrace_686613
  have hstable : (prefixWord ++ tailWord_686613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686613).length < 2 ^ (prefixWord ++ tailWord_686613).sum := by decide
  have hdescent : baseEnd_686613 < baseStart_686613 := by decide
  rcases family_descends (prefixWord ++ tailWord_686613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686654 : List Nat := [4, 2, 1, 4, 1, 2, 6]
def baseStart_686654 : Nat := 118140960795 + 686654 * 2 ^ 59
def prefixEnd_686654 : Nat := 4983230072969 + 3 ^ 40 * 686654 * 2
def baseEnd_686654 : Nat := 34823066205675229310335

theorem tailTrace_686654 : CollatzResearch.WordTrace tailWord_686654 prefixEnd_686654 34823066205675229310335 := by
  unfold tailWord_686654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130541106797163001484377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16696219236251536007916677 3130541106797163001484377)
  ·
    refine ⟨2347905830097872251113283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3130541106797163001484377 2347905830097872251113283)
    ·
      refine ⟨3521858745146808376669925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347905830097872251113283 3521858745146808376669925)
      ·
        refine ⟨660348514715026570625611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3521858745146808376669925 660348514715026570625611)
        ·
          refine ⟨990522772072539855938417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660348514715026570625611 990522772072539855938417)
          ·
            refine ⟨742892079054404891953813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990522772072539855938417 742892079054404891953813)
            ·
              refine ⟨34823066205675229310335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 742892079054404891953813 34823066205675229310335)
              ·
                rfl

theorem cell20_686654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_686654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686654 prefixEnd_686654 := by exact prefixLift 686654
  have htrace : WordTrace (prefixWord ++ tailWord_686654) baseStart_686654 baseEnd_686654 := by
    simpa [prefixWord, tailWord_686654, baseEnd_686654] using wordTrace_append hprefix tailTrace_686654
  have hstable : (prefixWord ++ tailWord_686654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686654).length < 2 ^ (prefixWord ++ tailWord_686654).sum := by decide
  have hdescent : baseEnd_686654 < baseStart_686654 := by decide
  rcases family_descends (prefixWord ++ tailWord_686654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686660 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_686660 : Nat := 118140960795 + 686660 * 2 ^ 59
def prefixEnd_686660 : Nat := 4983230072969 + 3 ^ 40 * 686660 * 2
def baseEnd_686660 : Nat := 313410334414567709592991

theorem tailTrace_686660 : CollatzResearch.WordTrace tailWord_686660 prefixEnd_686660 313410334414567709592991 := by
  unfold tailWord_686660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522273846177783518296717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16696365128237044691062289 12522273846177783518296717)
  ·
    refine ⟨4695852692316668819361269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12522273846177783518296717 4695852692316668819361269)
    ·
      refine ⟨440236189904687701815119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4695852692316668819361269 440236189904687701815119)
      ·
        refine ⟨660354284857031552722679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440236189904687701815119 660354284857031552722679)
        ·
          refine ⟨990531427285547329084019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660354284857031552722679 990531427285547329084019)
          ·
            refine ⟨1485797140928320993626029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990531427285547329084019 1485797140928320993626029)
            ·
              refine ⟨557173927848120372609761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485797140928320993626029 557173927848120372609761)
              ·
                refine ⟨417880445886090279457321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557173927848120372609761 417880445886090279457321)
                ·
                  refine ⟨313410334414567709592991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417880445886090279457321 313410334414567709592991)
                  ·
                    rfl

theorem cell20_686660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_686660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686660 prefixEnd_686660 := by exact prefixLift 686660
  have htrace : WordTrace (prefixWord ++ tailWord_686660) baseStart_686660 baseEnd_686660 := by
    simpa [prefixWord, tailWord_686660, baseEnd_686660] using wordTrace_append hprefix tailTrace_686660
  have hstable : (prefixWord ++ tailWord_686660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686660).length < 2 ^ (prefixWord ++ tailWord_686660).sum := by decide
  have hdescent : baseEnd_686660 < baseStart_686660 := by decide
  rcases family_descends (prefixWord ++ tailWord_686660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686672 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_686672 : Nat := 118140960795 + 686672 * 2 ^ 59
def prefixEnd_686672 : Nat := 4983230072969 + 3 ^ 40 * 686672 * 2
def baseEnd_686672 : Nat := 313415811541549001192941

theorem tailTrace_686672 : CollatzResearch.WordTrace tailWord_686672 prefixEnd_686672 313415811541549001192941 := by
  unfold tailWord_686672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522492684156046543015135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16696656912208062057353513 12522492684156046543015135)
  ·
    refine ⟨18783739026234069814522703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522492684156046543015135 18783739026234069814522703)
    ·
      refine ⟨28175608539351104721784055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18783739026234069814522703 28175608539351104721784055)
      ·
        refine ⟨42263412809026657082676083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28175608539351104721784055 42263412809026657082676083)
        ·
          refine ⟨63395119213539985624014125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42263412809026657082676083 63395119213539985624014125)
          ·
            refine ⟨23773169705077494609005297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63395119213539985624014125 23773169705077494609005297)
            ·
              refine ⟨17829877278808120956753973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23773169705077494609005297 17829877278808120956753973)
              ·
                refine ⟨1671550994888261339695685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17829877278808120956753973 1671550994888261339695685)
                ·
                  refine ⟨313415811541549001192941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671550994888261339695685 313415811541549001192941)
                  ·
                    rfl

theorem cell20_686672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_686672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686672 prefixEnd_686672 := by exact prefixLift 686672
  have htrace : WordTrace (prefixWord ++ tailWord_686672) baseStart_686672 baseEnd_686672 := by
    simpa [prefixWord, tailWord_686672, baseEnd_686672] using wordTrace_append hprefix tailTrace_686672
  have hstable : (prefixWord ++ tailWord_686672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686672).length < 2 ^ (prefixWord ++ tailWord_686672).sum := by decide
  have hdescent : baseEnd_686672 < baseStart_686672 := by decide
  rcases family_descends (prefixWord ++ tailWord_686672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686717 : List Nat := [1, 4, 1, 1, 13]
def baseStart_686717 : Nat := 118140960795 + 686717 * 2 ^ 59
def prefixEnd_686717 : Nat := 4983230072969 + 3 ^ 40 * 686717 * 2
def baseEnd_686717 : Nat := 3869584577379368452997

theorem tailTrace_686717 : CollatzResearch.WordTrace tailWord_686717 prefixEnd_686717 3869584577379368452997 := by
  unfold tailWord_686717
  simp only [CollatzResearch.WordTrace]
  refine ⟨25046626653149065771418405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16697751102099377180945603 25046626653149065771418405)
  ·
    refine ⟨4696242497465449832140951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25046626653149065771418405 4696242497465449832140951)
    ·
      refine ⟨7044363746198174748211427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4696242497465449832140951 7044363746198174748211427)
      ·
        refine ⟨10566545619297262122317141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7044363746198174748211427 10566545619297262122317141)
        ·
          refine ⟨3869584577379368452997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10566545619297262122317141 3869584577379368452997)
          ·
            rfl

theorem cell20_686717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 13].length) (baseStart_686717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686717 prefixEnd_686717 := by exact prefixLift 686717
  have htrace : WordTrace (prefixWord ++ tailWord_686717) baseStart_686717 baseEnd_686717 := by
    simpa [prefixWord, tailWord_686717, baseEnd_686717] using wordTrace_append hprefix tailTrace_686717
  have hstable : (prefixWord ++ tailWord_686717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686717).length < 2 ^ (prefixWord ++ tailWord_686717).sum := by decide
  have hdescent : baseEnd_686717 < baseStart_686717 := by decide
  rcases family_descends (prefixWord ++ tailWord_686717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686720 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_686720 : Nat := 118140960795 + 686720 * 2 ^ 59
def prefixEnd_686720 : Nat := 4983230072969 + 3 ^ 40 * 686720 * 2
def baseEnd_686720 : Nat := 313437720049474167592745

theorem tailTrace_686720 : CollatzResearch.WordTrace tailWord_686720 prefixEnd_686720 313437720049474167592745 := by
  unfold tailWord_686720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12523368036069098641888807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16697824048092131522518409 12523368036069098641888807)
  ·
    refine ⟨18785052054103647962833211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12523368036069098641888807 18785052054103647962833211)
    ·
      refine ⟨28177578081155471944249817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18785052054103647962833211 28177578081155471944249817)
      ·
        refine ⟨21133183560866603958187363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28177578081155471944249817 21133183560866603958187363)
        ·
          refine ⟨31699775341299905937281045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21133183560866603958187363 31699775341299905937281045)
          ·
            refine ⟨1485926969123433090810049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31699775341299905937281045 1485926969123433090810049)
            ·
              refine ⟨1114445226842574818107537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485926969123433090810049 1114445226842574818107537)
              ·
                refine ⟨835833920131931113580653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114445226842574818107537 835833920131931113580653)
                ·
                  refine ⟨313437720049474167592745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835833920131931113580653 313437720049474167592745)
                  ·
                    rfl

theorem cell20_686720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_686720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686720 prefixEnd_686720 := by exact prefixLift 686720
  have htrace : WordTrace (prefixWord ++ tailWord_686720) baseStart_686720 baseEnd_686720 := by
    simpa [prefixWord, tailWord_686720, baseEnd_686720] using wordTrace_append hprefix tailTrace_686720
  have hstable : (prefixWord ++ tailWord_686720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686720).length < 2 ^ (prefixWord ++ tailWord_686720).sum := by decide
  have hdescent : baseEnd_686720 < baseStart_686720 := by decide
  rcases family_descends (prefixWord ++ tailWord_686720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686730 : List Nat := [3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_686730 : Nat := 118140960795 + 686730 * 2 ^ 59
def prefixEnd_686730 : Nat := 4983230072969 + 3 ^ 40 * 686730 * 2
def baseEnd_686730 : Nat := 104480761440652859086457

theorem tailTrace_686730 : CollatzResearch.WordTrace tailWord_686730 prefixEnd_686730 104480761440652859086457 := by
  unfold tailWord_686730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261775200525492247910411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16698067201401312661094429 6261775200525492247910411)
  ·
    refine ⟨9392662800788238371865617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6261775200525492247910411 9392662800788238371865617)
    ·
      refine ⟨7044497100591178778899213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9392662800788238371865617 7044497100591178778899213)
      ·
        refine ⟨2641686412721692042087205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7044497100591178778899213 2641686412721692042087205)
        ·
          refine ⟨495316202385317257891351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2641686412721692042087205 495316202385317257891351)
          ·
            refine ⟨742974303577975886837027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495316202385317257891351 742974303577975886837027)
            ·
              refine ⟨1114461455366963830255541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742974303577975886837027 1114461455366963830255541)
              ·
                refine ⟨104480761440652859086457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1114461455366963830255541 104480761440652859086457)
                ·
                  rfl

theorem cell20_686730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_686730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_686730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_686730 prefixEnd_686730 := by exact prefixLift 686730
  have htrace : WordTrace (prefixWord ++ tailWord_686730) baseStart_686730 baseEnd_686730 := by
    simpa [prefixWord, tailWord_686730, baseEnd_686730] using wordTrace_append hprefix tailTrace_686730
  have hstable : (prefixWord ++ tailWord_686730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686730).length < 2 ^ (prefixWord ++ tailWord_686730).sum := by decide
  have hdescent : baseEnd_686730 < baseStart_686730 := by decide
  rcases family_descends (prefixWord ++ tailWord_686730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
