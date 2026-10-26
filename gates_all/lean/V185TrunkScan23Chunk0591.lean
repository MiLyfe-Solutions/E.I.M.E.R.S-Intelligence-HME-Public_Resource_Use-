import V185TrunkScan23Chunk0590

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3494654 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_3494654 : Nat := 118140960795 + 3494654 * 2 ^ 59
def prefixEnd_3494654 : Nat := 4983230072969 + 3 ^ 40 * 3494654 * 2
def baseEnd_3494654 : Nat := 199381913684163931539265

theorem tailTrace_3494654 : CollatzResearch.WordTrace tailWord_3494654 prefixEnd_3494654 199381913684163931539265 := by
  unfold tailWord_3494654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15932562835184109028937377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84973668454315248154332677 15932562835184109028937377)
  ·
    refine ⟨11949422126388081771703033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15932562835184109028937377 11949422126388081771703033)
    ·
      refine ⟨8962066594791061328777275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11949422126388081771703033 8962066594791061328777275)
      ·
        refine ⟨13443099892186591993165913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962066594791061328777275 13443099892186591993165913)
        ·
          refine ⟨10082324919139943994874435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13443099892186591993165913 10082324919139943994874435)
          ·
            refine ⟨15123487378709915992311653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082324919139943994874435 15123487378709915992311653)
            ·
              refine ⟨2835653883508109248558435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15123487378709915992311653 2835653883508109248558435)
              ·
                refine ⟨4253480825262163872837653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835653883508109248558435 4253480825262163872837653)
                ·
                  refine ⟨199381913684163931539265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4253480825262163872837653 199381913684163931539265)
                  ·
                    rfl

theorem cell23_3494654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_3494654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494654 prefixEnd_3494654 := by exact prefixLift 3494654
  have htrace : WordTrace (prefixWord ++ tailWord_3494654) baseStart_3494654 baseEnd_3494654 := by
    simpa [prefixWord, tailWord_3494654, baseEnd_3494654] using wordTrace_append hprefix tailTrace_3494654
  have hstable : (prefixWord ++ tailWord_3494654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494654).length < 2 ^ (prefixWord ++ tailWord_3494654).sum := by decide
  have hdescent : baseEnd_3494654 < baseStart_3494654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494657 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_3494657 : Nat := 118140960795 + 3494657 * 2 ^ 59
def prefixEnd_3494657 : Nat := 4983230072969 + 3 ^ 40 * 3494657 * 2
def baseEnd_3494657 : Nat := 1794438763599438872115871

theorem tailTrace_3494657 : CollatzResearch.WordTrace tailWord_3494657 prefixEnd_3494657 1794438763599438872115871 := by
  unfold tailWord_3494657
  simp only [CollatzResearch.WordTrace]
  refine ⟨127460612100462003743858225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84973741400308002495905483 127460612100462003743858225)
  ·
    refine ⟨95595459075346502807893669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127460612100462003743858225 95595459075346502807893669)
    ·
      refine ⟨17924148576627469276480063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95595459075346502807893669 17924148576627469276480063)
      ·
        refine ⟨26886222864941203914720095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17924148576627469276480063 26886222864941203914720095)
        ·
          refine ⟨40329334297411805872080143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26886222864941203914720095 40329334297411805872080143)
          ·
            refine ⟨60494001446117708808120215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40329334297411805872080143 60494001446117708808120215)
            ·
              refine ⟨90741002169176563212180323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60494001446117708808120215 90741002169176563212180323)
              ·
                refine ⟨136111503253764844818270485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90741002169176563212180323 136111503253764844818270485)
                ·
                  refine ⟨6380226715020227100856429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136111503253764844818270485 6380226715020227100856429)
                  ·
                    refine ⟨2392585018132585162821161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6380226715020227100856429 2392585018132585162821161)
                    ·
                      refine ⟨1794438763599438872115871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392585018132585162821161 1794438763599438872115871)
                      ·
                        rfl

theorem cell23_3494657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_3494657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494657 prefixEnd_3494657 := by exact prefixLift 3494657
  have htrace : WordTrace (prefixWord ++ tailWord_3494657) baseStart_3494657 baseEnd_3494657 := by
    simpa [prefixWord, tailWord_3494657, baseEnd_3494657] using wordTrace_append hprefix tailTrace_3494657
  have hstable : (prefixWord ++ tailWord_3494657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494657).length < 2 ^ (prefixWord ++ tailWord_3494657).sum := by decide
  have hdescent : baseEnd_3494657 < baseStart_3494657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494684 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3494684 : Nat := 118140960795 + 3494684 * 2 ^ 59
def prefixEnd_3494684 : Nat := 4983230072969 + 3 ^ 40 * 3494684 * 2
def baseEnd_3494684 : Nat := 598150875859036755492749

theorem tailTrace_3494684 : CollatzResearch.WordTrace tailWord_3494684 prefixEnd_3494684 598150875859036755492749 := by
  unfold tailWord_3494684
  simp only [CollatzResearch.WordTrace]
  refine ⟨63730798435682093677545553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84974397914242791570060737 63730798435682093677545553)
  ·
    refine ⟨47798098826761570258159165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63730798435682093677545553 47798098826761570258159165)
    ·
      refine ⟨17924287060035588846809687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47798098826761570258159165 17924287060035588846809687)
      ·
        refine ⟨26886430590053383270214531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17924287060035588846809687 26886430590053383270214531)
        ·
          refine ⟨40329645885080074905321797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26886430590053383270214531 40329645885080074905321797)
          ·
            refine ⟨7561808603452514044747837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40329645885080074905321797 7561808603452514044747837)
            ·
              refine ⟨2835678226294692766780439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7561808603452514044747837 2835678226294692766780439)
              ·
                refine ⟨4253517339442039150170659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2835678226294692766780439 4253517339442039150170659)
                ·
                  refine ⟨6380276009163058725255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253517339442039150170659 6380276009163058725255989)
                  ·
                    refine ⟨598150875859036755492749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6380276009163058725255989 598150875859036755492749)
                    ·
                      rfl

theorem cell23_3494684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3494684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494684 prefixEnd_3494684 := by exact prefixLift 3494684
  have htrace : WordTrace (prefixWord ++ tailWord_3494684) baseStart_3494684 baseEnd_3494684 := by
    simpa [prefixWord, tailWord_3494684, baseEnd_3494684] using wordTrace_append hprefix tailTrace_3494684
  have hstable : (prefixWord ++ tailWord_3494684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494684).length < 2 ^ (prefixWord ++ tailWord_3494684).sum := by decide
  have hdescent : baseEnd_3494684 < baseStart_3494684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494700 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3494700 : Nat := 118140960795 + 3494700 * 2 ^ 59
def prefixEnd_3494700 : Nat := 4983230072969 + 3 ^ 40 * 3494700 * 2
def baseEnd_3494700 : Nat := 1794460843267582203878173

theorem tailTrace_3494700 : CollatzResearch.WordTrace tailWord_3494700 prefixEnd_3494700 1794460843267582203878173 := by
  unfold tailWord_3494700
  simp only [CollatzResearch.WordTrace]
  refine ⟨63731090219653111043836777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84974786959537481391782369 63731090219653111043836777)
  ·
    refine ⟨47798317664739833282877583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63731090219653111043836777 47798317664739833282877583)
    ·
      refine ⟨71697476497109749924316375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47798317664739833282877583 71697476497109749924316375)
      ·
        refine ⟨107546214745664624886474563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71697476497109749924316375 107546214745664624886474563)
        ·
          refine ⟨161319322118496937329711845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107546214745664624886474563 161319322118496937329711845)
          ·
            refine ⟨30247372897218175749320971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161319322118496937329711845 30247372897218175749320971)
            ·
              refine ⟨45371059345827263623981457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30247372897218175749320971 45371059345827263623981457)
              ·
                refine ⟨34028294509370447717986093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45371059345827263623981457 34028294509370447717986093)
                ·
                  refine ⟨12760610441013917894244785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34028294509370447717986093 12760610441013917894244785)
                  ·
                    refine ⟨9570457830760438420683589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12760610441013917894244785 9570457830760438420683589)
                    ·
                      refine ⟨1794460843267582203878173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9570457830760438420683589 1794460843267582203878173)
                      ·
                        rfl

theorem cell23_3494700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3494700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494700 prefixEnd_3494700 := by exact prefixLift 3494700
  have htrace : WordTrace (prefixWord ++ tailWord_3494700) baseStart_3494700 baseEnd_3494700 := by
    simpa [prefixWord, tailWord_3494700, baseEnd_3494700] using wordTrace_append hprefix tailTrace_3494700
  have hstable : (prefixWord ++ tailWord_3494700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494700).length < 2 ^ (prefixWord ++ tailWord_3494700).sum := by decide
  have hdescent : baseEnd_3494700 < baseStart_3494700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494707 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3]
def baseStart_3494707 : Nat := 118140960795 + 3494707 * 2 ^ 59
def prefixEnd_3494707 : Nat := 4983230072969 + 3 ^ 40 * 3494707 * 2
def baseEnd_3494707 : Nat := 1794464437632163676490641

theorem tailTrace_3494707 : CollatzResearch.WordTrace tailWord_3494707 prefixEnd_3494707 1794464437632163676490641 := by
  unfold tailWord_3494707
  simp only [CollatzResearch.WordTrace]
  refine ⟨127462435750280862283178375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84974957166853908188785583 127462435750280862283178375)
  ·
    refine ⟨191193653625421293424767563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127462435750280862283178375 191193653625421293424767563)
    ·
      refine ⟨286790480438131940137151345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191193653625421293424767563 286790480438131940137151345)
      ·
        refine ⟨215092860328598955102863509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286790480438131940137151345 215092860328598955102863509)
        ·
          refine ⟨10082477827903076020446727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215092860328598955102863509 10082477827903076020446727)
          ·
            refine ⟨15123716741854614030670091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10082477827903076020446727 15123716741854614030670091)
            ·
              refine ⟨22685575112781921046005137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15123716741854614030670091 22685575112781921046005137)
              ·
                refine ⟨17014181334586440784503853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22685575112781921046005137 17014181334586440784503853)
                ·
                  refine ⟨6380318000469915294188945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17014181334586440784503853 6380318000469915294188945)
                  ·
                    refine ⟨4785238500352436470641709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6380318000469915294188945 4785238500352436470641709)
                    ·
                      refine ⟨1794464437632163676490641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4785238500352436470641709 1794464437632163676490641)
                      ·
                        rfl

theorem cell23_3494707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 3].length) (baseStart_3494707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494707 prefixEnd_3494707 := by exact prefixLift 3494707
  have htrace : WordTrace (prefixWord ++ tailWord_3494707) baseStart_3494707 baseEnd_3494707 := by
    simpa [prefixWord, tailWord_3494707, baseEnd_3494707] using wordTrace_append hprefix tailTrace_3494707
  have hstable : (prefixWord ++ tailWord_3494707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494707).length < 2 ^ (prefixWord ++ tailWord_3494707).sum := by decide
  have hdescent : baseEnd_3494707 < baseStart_3494707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494738 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_3494738 : Nat := 118140960795 + 3494738 * 2 ^ 59
def prefixEnd_3494738 : Nat := 4983230072969 + 3 ^ 40 * 3494738 * 2
def baseEnd_3494738 : Nat := 1794480355532453055202999

theorem tailTrace_3494738 : CollatzResearch.WordTrace tailWord_3494738 prefixEnd_3494738 1794480355532453055202999 := by
  unfold tailWord_3494738
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865891603292138644389217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84975710942112369718371245 31865891603292138644389217)
  ·
    refine ⟨23899418702469103983291913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31865891603292138644389217 23899418702469103983291913)
    ·
      refine ⟨17924564026851827987468935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23899418702469103983291913 17924564026851827987468935)
      ·
        refine ⟨26886846040277741981203403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17924564026851827987468935 26886846040277741981203403)
        ·
          refine ⟨40330269060416612971805105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26886846040277741981203403 40330269060416612971805105)
          ·
            refine ⟨30247701795312459728853829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40330269060416612971805105 30247701795312459728853829)
            ·
              refine ⟨5671444086621086199160093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30247701795312459728853829 5671444086621086199160093)
              ·
                refine ⟨2126791532482907324685035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5671444086621086199160093 2126791532482907324685035)
                ·
                  refine ⟨3190187298724360987027553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2126791532482907324685035 3190187298724360987027553)
                  ·
                    refine ⟨2392640474043270740270665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3190187298724360987027553 2392640474043270740270665)
                    ·
                      refine ⟨1794480355532453055202999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392640474043270740270665 1794480355532453055202999)
                      ·
                        rfl

theorem cell23_3494738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_3494738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494738 prefixEnd_3494738 := by exact prefixLift 3494738
  have htrace : WordTrace (prefixWord ++ tailWord_3494738) baseStart_3494738 baseEnd_3494738 := by
    simpa [prefixWord, tailWord_3494738, baseEnd_3494738] using wordTrace_append hprefix tailTrace_3494738
  have hstable : (prefixWord ++ tailWord_3494738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494738).length < 2 ^ (prefixWord ++ tailWord_3494738).sum := by decide
  have hdescent : baseEnd_3494738 < baseStart_3494738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494780 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3494780 : Nat := 118140960795 + 3494780 * 2 ^ 59
def prefixEnd_3494780 : Nat := 4983230072969 + 3 ^ 40 * 3494780 * 2
def baseEnd_3494780 : Nat := 1794501921719941890877805

theorem tailTrace_3494780 : CollatzResearch.WordTrace tailWord_3494780 prefixEnd_3494780 1794501921719941890877805 := by
  unfold tailWord_3494780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63732549139508197875292897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84976732186010930500390529 63732549139508197875292897)
  ·
    refine ⟨47799411854631148406469673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63732549139508197875292897 47799411854631148406469673)
    ·
      refine ⟨35849558890973361304852255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47799411854631148406469673 35849558890973361304852255)
      ·
        refine ⟨53774338336460041957278383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35849558890973361304852255 53774338336460041957278383)
        ·
          refine ⟨80661507504690062935917575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53774338336460041957278383 80661507504690062935917575)
          ·
            refine ⟨120992261257035094403876363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80661507504690062935917575 120992261257035094403876363)
            ·
              refine ⟨181488391885552641605814545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120992261257035094403876363 181488391885552641605814545)
              ·
                refine ⟨136116293914164481204360909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181488391885552641605814545 136116293914164481204360909)
                ·
                  refine ⟨51043610217811680451635341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136116293914164481204360909 51043610217811680451635341)
                  ·
                    refine ⟨19141353831679380169363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51043610217811680451635341 19141353831679380169363253)
                    ·
                      refine ⟨1794501921719941890877805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19141353831679380169363253 1794501921719941890877805)
                      ·
                        rfl

theorem cell23_3494780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3494780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494780 prefixEnd_3494780 := by exact prefixLift 3494780
  have htrace : WordTrace (prefixWord ++ tailWord_3494780) baseStart_3494780 baseEnd_3494780 := by
    simpa [prefixWord, tailWord_3494780, baseEnd_3494780] using wordTrace_append hprefix tailTrace_3494780
  have hstable : (prefixWord ++ tailWord_3494780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494780).length < 2 ^ (prefixWord ++ tailWord_3494780).sum := by decide
  have hdescent : baseEnd_3494780 < baseStart_3494780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494868 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 5]
def baseStart_3494868 : Nat := 118140960795 + 3494868 * 2 ^ 59
def prefixEnd_3494868 : Nat := 4983230072969 + 3 ^ 40 * 3494868 * 2
def baseEnd_3494868 : Nat := 199394123113059727397489

theorem tailTrace_3494868 : CollatzResearch.WordTrace tailWord_3494868 prefixEnd_3494868 199394123113059727397489 := by
  unfold tailWord_3494868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63734153951348793389894629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84978871935131724519859505 63734153951348793389894629)
  ·
    refine ⟨11950153865877898760605243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63734153951348793389894629 11950153865877898760605243)
    ·
      refine ⟨17925230798816848140907865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11950153865877898760605243 17925230798816848140907865)
      ·
        refine ⟨13443923099112636105680899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17925230798816848140907865 13443923099112636105680899)
        ·
          refine ⟨20165884648668954158521349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13443923099112636105680899 20165884648668954158521349)
          ·
            refine ⟨3781103371625428904722753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20165884648668954158521349 3781103371625428904722753)
            ·
              refine ⟨2835827528719071678542065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781103371625428904722753 2835827528719071678542065)
              ·
                refine ⟨2126870646539303758906549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835827528719071678542065 2126870646539303758906549)
                ·
                  refine ⟨199394123113059727397489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126870646539303758906549 199394123113059727397489)
                  ·
                    rfl

theorem cell23_3494868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_3494868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494868 prefixEnd_3494868 := by exact prefixLift 3494868
  have htrace : WordTrace (prefixWord ++ tailWord_3494868) baseStart_3494868 baseEnd_3494868 := by
    simpa [prefixWord, tailWord_3494868, baseEnd_3494868] using wordTrace_append hprefix tailTrace_3494868
  have hstable : (prefixWord ++ tailWord_3494868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494868).length < 2 ^ (prefixWord ++ tailWord_3494868).sum := by decide
  have hdescent : baseEnd_3494868 < baseStart_3494868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494898 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3494898 : Nat := 118140960795 + 3494898 * 2 ^ 59
def prefixEnd_3494898 : Nat := 4983230072969 + 3 ^ 40 * 3494898 * 2
def baseEnd_3494898 : Nat := 598187504145724143067421

theorem tailTrace_3494898 : CollatzResearch.WordTrace tailWord_3494898 prefixEnd_3494898 598187504145724143067421 := by
  unfold tailWord_3494898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31867350523147225475845337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84979601395059267935587565 31867350523147225475845337)
  ·
    refine ⟨23900512892360419106884003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31867350523147225475845337 23900512892360419106884003)
    ·
      refine ⟨35850769338540628660326005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23900512892360419106884003 35850769338540628660326005)
      ·
        refine ⟨3361009625488183936905563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35850769338540628660326005 3361009625488183936905563)
        ·
          refine ⟨5041514438232275905358345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361009625488183936905563 5041514438232275905358345)
          ·
            refine ⟨3781135828674206929018759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041514438232275905358345 3781135828674206929018759)
            ·
              refine ⟨5671703743011310393528139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781135828674206929018759 5671703743011310393528139)
              ·
                refine ⟨8507555614516965590292209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671703743011310393528139 8507555614516965590292209)
                ·
                  refine ⟨6380666710887724192719157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507555614516965590292209 6380666710887724192719157)
                  ·
                    refine ⟨598187504145724143067421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6380666710887724192719157 598187504145724143067421)
                    ·
                      rfl

theorem cell23_3494898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3494898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494898 prefixEnd_3494898 := by exact prefixLift 3494898
  have htrace : WordTrace (prefixWord ++ tailWord_3494898) baseStart_3494898 baseEnd_3494898 := by
    simpa [prefixWord, tailWord_3494898, baseEnd_3494898] using wordTrace_append hprefix tailTrace_3494898
  have hstable : (prefixWord ++ tailWord_3494898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494898).length < 2 ^ (prefixWord ++ tailWord_3494898).sum := by decide
  have hdescent : baseEnd_3494898 < baseStart_3494898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494924 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 6]
def baseStart_3494924 : Nat := 118140960795 + 3494924 * 2 ^ 59
def prefixEnd_3494924 : Nat := 4983230072969 + 3 ^ 40 * 3494924 * 2
def baseEnd_3494924 : Nat := 199397318103798814164127

theorem tailTrace_3494924 : CollatzResearch.WordTrace tailWord_3494924 prefixEnd_3494924 199397318103798814164127 := by
  unfold tailWord_3494924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63735175195247354171913913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84980233593663138895885217 63735175195247354171913913)
  ·
    refine ⟨47801381396435515628935435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63735175195247354171913913 47801381396435515628935435)
    ·
      refine ⟨71702072094653273443403153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47801381396435515628935435 71702072094653273443403153)
      ·
        refine ⟨53776554070989955082552365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71702072094653273443403153 53776554070989955082552365)
        ·
          refine ⟨20166207776621233155957137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53776554070989955082552365 20166207776621233155957137)
          ·
            refine ⟨15124655832465924866967853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20166207776621233155957137 15124655832465924866967853)
            ·
              refine ⟨5671745937174721825112945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15124655832465924866967853 5671745937174721825112945)
              ·
                refine ⟨4253809452881041368834709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5671745937174721825112945 4253809452881041368834709)
                ·
                  refine ⟨199397318103798814164127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4253809452881041368834709 199397318103798814164127)
                  ·
                    rfl

theorem cell23_3494924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 6].length) (baseStart_3494924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494924 prefixEnd_3494924 := by exact prefixLift 3494924
  have htrace : WordTrace (prefixWord ++ tailWord_3494924) baseStart_3494924 baseEnd_3494924 := by
    simpa [prefixWord, tailWord_3494924, baseEnd_3494924] using wordTrace_append hprefix tailTrace_3494924
  have hstable : (prefixWord ++ tailWord_3494924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494924).length < 2 ^ (prefixWord ++ tailWord_3494924).sum := by decide
  have hdescent : baseEnd_3494924 < baseStart_3494924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494937 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_3494937 : Nat := 118140960795 + 3494937 * 2 ^ 59
def prefixEnd_3494937 : Nat := 4983230072969 + 3 ^ 40 * 3494937 * 2
def baseEnd_3494937 : Nat := 598194179394232592204861

theorem tailTrace_3494937 : CollatzResearch.WordTrace tailWord_3494937 prefixEnd_3494937 598194179394232592204861 := by
  unfold tailWord_3494937
  simp only [CollatzResearch.WordTrace]
  refine ⟨127470824539447611564051065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84980549692965074376034043 127470824539447611564051065)
  ·
    refine ⟨95603118404585708673038299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127470824539447611564051065 95603118404585708673038299)
    ·
      refine ⟨143404677606878563009557449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95603118404585708673038299 143404677606878563009557449)
      ·
        refine ⟨107553508205158922257168087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143404677606878563009557449 107553508205158922257168087)
        ·
          refine ⟨161330262307738383385752131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107553508205158922257168087 161330262307738383385752131)
          ·
            refine ⟨241995393461607575078628197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161330262307738383385752131 241995393461607575078628197)
            ·
              refine ⟨45374136274051420327242787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241995393461607575078628197 45374136274051420327242787)
              ·
                refine ⟨68061204411077130490864181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45374136274051420327242787 68061204411077130490864181)
                ·
                  refine ⟨6380737913538480983518517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68061204411077130490864181 6380737913538480983518517)
                  ·
                    refine ⟨598194179394232592204861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6380737913538480983518517 598194179394232592204861)
                    ·
                      rfl

theorem cell23_3494937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_3494937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494937 prefixEnd_3494937 := by exact prefixLift 3494937
  have htrace : WordTrace (prefixWord ++ tailWord_3494937) baseStart_3494937 baseEnd_3494937 := by
    simpa [prefixWord, tailWord_3494937, baseEnd_3494937] using wordTrace_append hprefix tailTrace_3494937
  have hstable : (prefixWord ++ tailWord_3494937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494937).length < 2 ^ (prefixWord ++ tailWord_3494937).sum := by decide
  have hdescent : baseEnd_3494937 < baseStart_3494937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494961 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_3494961 : Nat := 118140960795 + 3494961 * 2 ^ 59
def prefixEnd_3494961 : Nat := 4983230072969 + 3 ^ 40 * 3494961 * 2
def baseEnd_3494961 : Nat := 1794594861718405682714473

theorem tailTrace_3494961 : CollatzResearch.WordTrace tailWord_3494961 prefixEnd_3494961 1794594861718405682714473 := by
  unfold tailWord_3494961
  simp only [CollatzResearch.WordTrace]
  refine ⟨127471699891360663662924737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84981133260907109108616491 127471699891360663662924737)
  ·
    refine ⟨95603774918520497747193553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127471699891360663662924737 95603774918520497747193553)
    ·
      refine ⟨71702831188890373310395165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95603774918520497747193553 71702831188890373310395165)
      ·
        refine ⟨26888561695833889991398187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71702831188890373310395165 26888561695833889991398187)
        ·
          refine ⟨40332842543750834987097281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26888561695833889991398187 40332842543750834987097281)
          ·
            refine ⟨30249631907813126240322961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40332842543750834987097281 30249631907813126240322961)
            ·
              refine ⟨22687223930859844680242221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30249631907813126240322961 22687223930859844680242221)
              ·
                refine ⟨8507708974072441755090833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22687223930859844680242221 8507708974072441755090833)
                ·
                  refine ⟨6380781730554331316318125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8507708974072441755090833 6380781730554331316318125)
                  ·
                    refine ⟨2392793148957874243619297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6380781730554331316318125 2392793148957874243619297)
                    ·
                      refine ⟨1794594861718405682714473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392793148957874243619297 1794594861718405682714473)
                      ·
                        rfl

theorem cell23_3494961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_3494961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494961 prefixEnd_3494961 := by exact prefixLift 3494961
  have htrace : WordTrace (prefixWord ++ tailWord_3494961) baseStart_3494961 baseEnd_3494961 := by
    simpa [prefixWord, tailWord_3494961, baseEnd_3494961] using wordTrace_append hprefix tailTrace_3494961
  have hstable : (prefixWord ++ tailWord_3494961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494961).length < 2 ^ (prefixWord ++ tailWord_3494961).sum := by decide
  have hdescent : baseEnd_3494961 < baseStart_3494961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494967 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 6]
def baseStart_3494967 : Nat := 118140960795 + 3494967 * 2 ^ 59
def prefixEnd_3494967 : Nat := 4983230072969 + 3 ^ 40 * 3494967 * 2
def baseEnd_3494967 : Nat := 598199314200777553079815

theorem tailTrace_3494967 : CollatzResearch.WordTrace tailWord_3494967 prefixEnd_3494967 598199314200777553079815 := by
  unfold tailWord_3494967
  simp only [CollatzResearch.WordTrace]
  refine ⟨127471918729338926687643155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84981279152892617791762103 127471918729338926687643155)
  ·
    refine ⟨191207878094008390031464733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127471918729338926687643155 191207878094008390031464733)
    ·
      refine ⟨71702954285253146261799275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191207878094008390031464733 71702954285253146261799275)
      ·
        refine ⟨107554431427879719392698913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71702954285253146261799275 107554431427879719392698913)
        ·
          refine ⟨80665823570909789544524185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107554431427879719392698913 80665823570909789544524185)
          ·
            refine ⟨60499367678182342158393139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80665823570909789544524185 60499367678182342158393139)
            ·
              refine ⟨90749051517273513237589709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60499367678182342158393139 90749051517273513237589709)
              ·
                refine ⟨34030894318977567464096141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90749051517273513237589709 34030894318977567464096141)
                ·
                  refine ⟨12761585369616587799036053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34030894318977567464096141 12761585369616587799036053)
                  ·
                    refine ⟨598199314200777553079815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12761585369616587799036053 598199314200777553079815)
                    ·
                      rfl

theorem cell23_3494967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_3494967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494967 prefixEnd_3494967 := by exact prefixLift 3494967
  have htrace : WordTrace (prefixWord ++ tailWord_3494967) baseStart_3494967 baseEnd_3494967 := by
    simpa [prefixWord, tailWord_3494967, baseEnd_3494967] using wordTrace_append hprefix tailTrace_3494967
  have hstable : (prefixWord ++ tailWord_3494967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494967).length < 2 ^ (prefixWord ++ tailWord_3494967).sum := by decide
  have hdescent : baseEnd_3494967 < baseStart_3494967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494984 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 4, 4]
def baseStart_3494984 : Nat := 118140960795 + 3494984 * 2 ^ 59
def prefixEnd_3494984 : Nat := 4983230072969 + 3 ^ 40 * 3494984 * 2
def baseEnd_3494984 : Nat := 598202223924486364242289

theorem tailTrace_3494984 : CollatzResearch.WordTrace tailWord_3494984 prefixEnd_3494984 598202223924486364242289 := by
  unfold tailWord_3494984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63736269385138669295506003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84981692513518225727341337 63736269385138669295506003)
  ·
    refine ⟨95604404077708003943259005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63736269385138669295506003 95604404077708003943259005)
    ·
      refine ⟨35851651529140501478722127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95604404077708003943259005 35851651529140501478722127)
      ·
        refine ⟨53777477293710752218083191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35851651529140501478722127 53777477293710752218083191)
        ·
          refine ⟨80666215940566128327124787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53777477293710752218083191 80666215940566128327124787)
          ·
            refine ⟨120999323910849192490687181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80666215940566128327124787 120999323910849192490687181)
            ·
              refine ⟨45374746466568447184007693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120999323910849192490687181 45374746466568447184007693)
              ·
                refine ⟨17015529924963167694002885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45374746466568447184007693 17015529924963167694002885)
                ·
                  refine ⟨3190411860930593942625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17015529924963167694002885 3190411860930593942625541)
                  ·
                    refine ⟨598202223924486364242289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3190411860930593942625541 598202223924486364242289)
                    ·
                      rfl

theorem cell23_3494984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_3494984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494984 prefixEnd_3494984 := by exact prefixLift 3494984
  have htrace : WordTrace (prefixWord ++ tailWord_3494984) baseStart_3494984 baseEnd_3494984 := by
    simpa [prefixWord, tailWord_3494984, baseEnd_3494984] using wordTrace_append hprefix tailTrace_3494984
  have hstable : (prefixWord ++ tailWord_3494984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494984).length < 2 ^ (prefixWord ++ tailWord_3494984).sum := by decide
  have hdescent : baseEnd_3494984 < baseStart_3494984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3494987 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_3494987 : Nat := 118140960795 + 3494987 * 2 ^ 59
def prefixEnd_3494987 : Nat := 4983230072969 + 3 ^ 40 * 3494987 * 2
def baseEnd_3494987 : Nat := 1794608212215422580989353

theorem tailTrace_3494987 : CollatzResearch.WordTrace tailWord_3494987 prefixEnd_3494987 1794608212215422580989353 := by
  unfold tailWord_3494987
  simp only [CollatzResearch.WordTrace]
  refine ⟨127472648189266470103371215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84981765459510980068914143 127472648189266470103371215)
  ·
    refine ⟨191208972283899705155056823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127472648189266470103371215 191208972283899705155056823)
    ·
      refine ⟨286813458425849557732585235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191208972283899705155056823 286813458425849557732585235)
      ·
        refine ⟨430220187638774336598877853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286813458425849557732585235 430220187638774336598877853)
        ·
          refine ⟨161332570364540376224579195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430220187638774336598877853 161332570364540376224579195)
          ·
            refine ⟨241998855546810564336868793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161332570364540376224579195 241998855546810564336868793)
            ·
              refine ⟨181499141660107923252651595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241998855546810564336868793 181499141660107923252651595)
              ·
                refine ⟨272248712490161884878977393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181499141660107923252651595 272248712490161884878977393)
                ·
                  refine ⟨204186534367621413659233045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272248712490161884878977393 204186534367621413659233045)
                  ·
                    refine ⟨9571243798482253765276549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204186534367621413659233045 9571243798482253765276549)
                    ·
                      refine ⟨1794608212215422580989353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9571243798482253765276549 1794608212215422580989353)
                      ·
                        rfl

theorem cell23_3494987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_3494987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3494987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3494987 prefixEnd_3494987 := by exact prefixLift 3494987
  have htrace : WordTrace (prefixWord ++ tailWord_3494987) baseStart_3494987 baseEnd_3494987 := by
    simpa [prefixWord, tailWord_3494987, baseEnd_3494987] using wordTrace_append hprefix tailTrace_3494987
  have hstable : (prefixWord ++ tailWord_3494987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3494987).length < 2 ^ (prefixWord ++ tailWord_3494987).sum := by decide
  have hdescent : baseEnd_3494987 < baseStart_3494987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3494987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495004 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3495004 : Nat := 118140960795 + 3495004 * 2 ^ 59
def prefixEnd_3495004 : Nat := 4983230072969 + 3 ^ 40 * 3495004 * 2
def baseEnd_3495004 : Nat := 1794616941386549014476775

theorem tailTrace_3495004 : CollatzResearch.WordTrace tailWord_3495004 prefixEnd_3495004 1794616941386549014476775 := by
  unfold tailWord_3495004
  simp only [CollatzResearch.WordTrace]
  refine ⟨63736634115102441003370033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84982178820136588004493377 63736634115102441003370033)
  ·
    refine ⟨47802475586326830752527525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63736634115102441003370033 47802475586326830752527525)
    ·
      refine ⟨8962964172436280766098911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47802475586326830752527525 8962964172436280766098911)
      ·
        refine ⟨13444446258654421149148367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8962964172436280766098911 13444446258654421149148367)
        ·
          refine ⟨20166669387981631723722551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444446258654421149148367 20166669387981631723722551)
          ·
            refine ⟨30250004081972447585583827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20166669387981631723722551 30250004081972447585583827)
            ·
              refine ⟨45375006122958671378375741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30250004081972447585583827 45375006122958671378375741)
              ·
                refine ⟨17015627296109501766890903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45375006122958671378375741 17015627296109501766890903)
                ·
                  refine ⟨25523440944164252650336355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17015627296109501766890903 25523440944164252650336355)
                  ·
                    refine ⟨38285161416246378975504533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25523440944164252650336355 38285161416246378975504533)
                    ·
                      refine ⟨1794616941386549014476775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38285161416246378975504533 1794616941386549014476775)
                      ·
                        rfl

theorem cell23_3495004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3495004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495004 prefixEnd_3495004 := by exact prefixLift 3495004
  have htrace : WordTrace (prefixWord ++ tailWord_3495004) baseStart_3495004 baseEnd_3495004 := by
    simpa [prefixWord, tailWord_3495004, baseEnd_3495004] using wordTrace_append hprefix tailTrace_3495004
  have hstable : (prefixWord ++ tailWord_3495004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495004).length < 2 ^ (prefixWord ++ tailWord_3495004).sum := by decide
  have hdescent : baseEnd_3495004 < baseStart_3495004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495005 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3495005 : Nat := 118140960795 + 3495005 * 2 ^ 59
def prefixEnd_3495005 : Nat := 4983230072969 + 3 ^ 40 * 3495005 * 2
def baseEnd_3495005 : Nat := 598205818289067836854757

theorem tailTrace_3495005 : CollatzResearch.WordTrace tailWord_3495005 prefixEnd_3495005 598205818289067836854757 := by
  unfold tailWord_3495005
  simp only [CollatzResearch.WordTrace]
  refine ⟨127473304703201259177526469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84982203135467506118350979 127473304703201259177526469)
  ·
    refine ⟨23901244631850236095786213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127473304703201259177526469 23901244631850236095786213)
    ·
      refine ⟨4481483368471919267959915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23901244631850236095786213 4481483368471919267959915)
      ·
        refine ⟨6722225052707878901939873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481483368471919267959915 6722225052707878901939873)
        ·
          refine ⟨5041668789530909176454905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6722225052707878901939873 5041668789530909176454905)
          ·
            refine ⟨3781251592148181882341179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5041668789530909176454905 3781251592148181882341179)
            ·
              refine ⟨5671877388222272823511769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781251592148181882341179 5671877388222272823511769)
              ·
                refine ⟨4253908041166704617633827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5671877388222272823511769 4253908041166704617633827)
                ·
                  refine ⟨6380862061750056926450741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4253908041166704617633827 6380862061750056926450741)
                  ·
                    refine ⟨598205818289067836854757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6380862061750056926450741 598205818289067836854757)
                    ·
                      rfl

theorem cell23_3495005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3495005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495005 prefixEnd_3495005 := by exact prefixLift 3495005
  have htrace : WordTrace (prefixWord ++ tailWord_3495005) baseStart_3495005 baseEnd_3495005 := by
    simpa [prefixWord, tailWord_3495005, baseEnd_3495005] using wordTrace_append hprefix tailTrace_3495005
  have hstable : (prefixWord ++ tailWord_3495005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495005).length < 2 ^ (prefixWord ++ tailWord_3495005).sum := by decide
  have hdescent : baseEnd_3495005 < baseStart_3495005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495021 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3495021 : Nat := 118140960795 + 3495021 * 2 ^ 59
def prefixEnd_3495021 : Nat := 4983230072969 + 3 ^ 40 * 3495021 * 2
def baseEnd_3495021 : Nat := 1794625670557675447964197

theorem tailTrace_3495021 : CollatzResearch.WordTrace tailWord_3495021 prefixEnd_3495021 1794625670557675447964197 := by
  unfold tailWord_3495021
  simp only [CollatzResearch.WordTrace]
  refine ⟨127473888271143293910108917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84982592180762195940072611 127473888271143293910108917)
  ·
    refine ⟨11950677025419683804072711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127473888271143293910108917 11950677025419683804072711)
    ·
      refine ⟨17926015538129525706109067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11950677025419683804072711 17926015538129525706109067)
      ·
        refine ⟨26889023307194288559163601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926015538129525706109067 26889023307194288559163601)
        ·
          refine ⟨20166767480395716419372701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26889023307194288559163601 20166767480395716419372701)
          ·
            refine ⟨7562537805148393657264763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20166767480395716419372701 7562537805148393657264763)
            ·
              refine ⟨11343806707722590485897145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7562537805148393657264763 11343806707722590485897145)
              ·
                refine ⟨8507855030791942864422859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11343806707722590485897145 8507855030791942864422859)
                ·
                  refine ⟨12761782546187914296634289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507855030791942864422859 12761782546187914296634289)
                  ·
                    refine ⟨9571336909640935722475717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12761782546187914296634289 9571336909640935722475717)
                    ·
                      refine ⟨1794625670557675447964197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9571336909640935722475717 1794625670557675447964197)
                      ·
                        rfl

theorem cell23_3495021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3495021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495021 prefixEnd_3495021 := by exact prefixLift 3495021
  have htrace : WordTrace (prefixWord ++ tailWord_3495021) baseStart_3495021 baseEnd_3495021 := by
    simpa [prefixWord, tailWord_3495021, baseEnd_3495021] using wordTrace_append hprefix tailTrace_3495021
  have hstable : (prefixWord ++ tailWord_3495021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495021).length < 2 ^ (prefixWord ++ tailWord_3495021).sum := by decide
  have hdescent : baseEnd_3495021 < baseStart_3495021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495027 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 7]
def baseStart_3495027 : Nat := 118140960795 + 3495027 * 2 ^ 59
def prefixEnd_3495027 : Nat := 4983230072969 + 3 ^ 40 * 3495027 * 2
def baseEnd_3495027 : Nat := 598209583813867474829723

theorem tailTrace_3495027 : CollatzResearch.WordTrace tailWord_3495027 prefixEnd_3495027 598209583813867474829723 := by
  unfold tailWord_3495027
  simp only [CollatzResearch.WordTrace]
  refine ⟨127474107109121556934827335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84982738072747704623218223 127474107109121556934827335)
  ·
    refine ⟨191211160663682335402241003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127474107109121556934827335 191211160663682335402241003)
    ·
      refine ⟨286816740995523503103361505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191211160663682335402241003 286816740995523503103361505)
      ·
        refine ⟨215112555746642627327521129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286816740995523503103361505 215112555746642627327521129)
        ·
          refine ⟨161334416809981970495640847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215112555746642627327521129 161334416809981970495640847)
          ·
            refine ⟨242001625214972955743461271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161334416809981970495640847 242001625214972955743461271)
            ·
              refine ⟨363002437822459433615191907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242001625214972955743461271 363002437822459433615191907)
              ·
                refine ⟨544503656733689150422787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363002437822459433615191907 544503656733689150422787861)
                ·
                  refine ⟨25523608909391678926068181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544503656733689150422787861 25523608909391678926068181)
                  ·
                    refine ⟨598209583813867474829723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25523608909391678926068181 598209583813867474829723)
                    ·
                      rfl

theorem cell23_3495027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_3495027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495027 prefixEnd_3495027 := by exact prefixLift 3495027
  have htrace : WordTrace (prefixWord ++ tailWord_3495027) baseStart_3495027 baseEnd_3495027 := by
    simpa [prefixWord, tailWord_3495027, baseEnd_3495027] using wordTrace_append hprefix tailTrace_3495027
  have hstable : (prefixWord ++ tailWord_3495027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495027).length < 2 ^ (prefixWord ++ tailWord_3495027).sum := by decide
  have hdescent : baseEnd_3495027 < baseStart_3495027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495044 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_3495044 : Nat := 118140960795 + 3495044 * 2 ^ 59
def prefixEnd_3495044 : Nat := 4983230072969 + 3 ^ 40 * 3495044 * 2
def baseEnd_3495044 : Nat := 598212493537576285992197

theorem tailTrace_3495044 : CollatzResearch.WordTrace tailWord_3495044 prefixEnd_3495044 598212493537576285992197 := by
  unfold tailWord_3495044
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737363575029984419098093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84983151433373312558797457 63737363575029984419098093)
  ·
    refine ⟨23901511340636244157161785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63737363575029984419098093 23901511340636244157161785)
    ·
      refine ⟨17926133505477183117871339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23901511340636244157161785 17926133505477183117871339)
      ·
        refine ⟨26889200258215774676807009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926133505477183117871339 26889200258215774676807009)
        ·
          refine ⟨20166900193661831007605257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26889200258215774676807009 20166900193661831007605257)
          ·
            refine ⟨15125175145246373255703943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20166900193661831007605257 15125175145246373255703943)
            ·
              refine ⟨22687762717869559883555915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15125175145246373255703943 22687762717869559883555915)
              ·
                refine ⟨34031644076804339825333873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22687762717869559883555915 34031644076804339825333873)
                ·
                  refine ⟨25523733057603254869000405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34031644076804339825333873 25523733057603254869000405)
                  ·
                    refine ⟨598212493537576285992197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25523733057603254869000405 598212493537576285992197)
                    ·
                      rfl

theorem cell23_3495044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_3495044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495044 prefixEnd_3495044 := by exact prefixLift 3495044
  have htrace : WordTrace (prefixWord ++ tailWord_3495044) baseStart_3495044 baseEnd_3495044 := by
    simpa [prefixWord, tailWord_3495044, baseEnd_3495044] using wordTrace_append hprefix tailTrace_3495044
  have hstable : (prefixWord ++ tailWord_3495044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495044).length < 2 ^ (prefixWord ++ tailWord_3495044).sum := by decide
  have hdescent : baseEnd_3495044 < baseStart_3495044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495048 : List Nat := [2, 1, 3, 4, 3, 1, 1, 8]
def baseStart_3495048 : Nat := 118140960795 + 3495048 * 2 ^ 59
def prefixEnd_3495048 : Nat := 4983230072969 + 3 ^ 40 * 3495048 * 2
def baseEnd_3495048 : Nat := 66468130908716549715799

theorem tailTrace_3495048 : CollatzResearch.WordTrace tailWord_3495048 prefixEnd_3495048 66468130908716549715799 := by
  unfold tailWord_3495048
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737436521022738760670899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84983248694696985014227865 63737436521022738760670899)
  ·
    refine ⟨95606154781534108141006349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63737436521022738760670899 95606154781534108141006349)
    ·
      refine ⟨35852308043075290552877381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95606154781534108141006349 35852308043075290552877381)
      ·
        refine ⟨6722307758076616978664509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35852308043075290552877381 6722307758076616978664509)
        ·
          refine ⟨2520865409278731366999191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6722307758076616978664509 2520865409278731366999191)
          ·
            refine ⟨3781298113918097050498787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520865409278731366999191 3781298113918097050498787)
            ·
              refine ⟨5671947170877145575748181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781298113918097050498787 5671947170877145575748181)
              ·
                refine ⟨66468130908716549715799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5671947170877145575748181 66468130908716549715799)
                ·
                  rfl

theorem cell23_3495048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 8].length) (baseStart_3495048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495048 prefixEnd_3495048 := by exact prefixLift 3495048
  have htrace : WordTrace (prefixWord ++ tailWord_3495048) baseStart_3495048 baseEnd_3495048 := by
    simpa [prefixWord, tailWord_3495048, baseEnd_3495048] using wordTrace_append hprefix tailTrace_3495048
  have hstable : (prefixWord ++ tailWord_3495048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495048).length < 2 ^ (prefixWord ++ tailWord_3495048).sum := by decide
  have hdescent : baseEnd_3495048 < baseStart_3495048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495058 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3495058 : Nat := 118140960795 + 3495058 * 2 ^ 59
def prefixEnd_3495058 : Nat := 4983230072969 + 3 ^ 40 * 3495058 * 2
def baseEnd_3495058 : Nat := 1794644669341891803201527

theorem tailTrace_3495058 : CollatzResearch.WordTrace tailWord_3495058 prefixEnd_3495058 1794644669341891803201527 := by
  unfold tailWord_3495058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31868809443002312307301457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84983491848006166152803885 31868809443002312307301457)
  ·
    refine ⟨23901607082251734230476093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31868809443002312307301457 23901607082251734230476093)
    ·
      refine ⟨8963102655844400336428535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23901607082251734230476093 8963102655844400336428535)
      ·
        refine ⟨13444653983766600504642803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963102655844400336428535 13444653983766600504642803)
        ·
          refine ⟨20166980975649900756964205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444653983766600504642803 20166980975649900756964205)
          ·
            refine ⟨7562617865868712783861577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20166980975649900756964205 7562617865868712783861577)
            ·
              refine ⟨5671963399401534587896183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7562617865868712783861577 5671963399401534587896183)
              ·
                refine ⟨8507945099102301881844275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5671963399401534587896183 8507945099102301881844275)
                ·
                  refine ⟨12761917648653452822766413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8507945099102301881844275 12761917648653452822766413)
                  ·
                    refine ⟨4785719118245044808537405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12761917648653452822766413 4785719118245044808537405)
                    ·
                      refine ⟨1794644669341891803201527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4785719118245044808537405 1794644669341891803201527)
                      ·
                        rfl

theorem cell23_3495058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3495058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495058 prefixEnd_3495058 := by exact prefixLift 3495058
  have htrace : WordTrace (prefixWord ++ tailWord_3495058) baseStart_3495058 baseEnd_3495058 := by
    simpa [prefixWord, tailWord_3495058, baseEnd_3495058] using wordTrace_append hprefix tailTrace_3495058
  have hstable : (prefixWord ++ tailWord_3495058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495058).length < 2 ^ (prefixWord ++ tailWord_3495058).sum := by decide
  have hdescent : baseEnd_3495058 < baseStart_3495058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495068 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3495068 : Nat := 118140960795 + 3495068 * 2 ^ 59
def prefixEnd_3495068 : Nat := 4983230072969 + 3 ^ 40 * 3495068 * 2
def baseEnd_3495068 : Nat := 1794649804148436764076481

theorem tailTrace_3495068 : CollatzResearch.WordTrace tailWord_3495068 prefixEnd_3495068 1794649804148436764076481 := by
  unfold tailWord_3495068
  simp only [CollatzResearch.WordTrace]
  refine ⟨63737801250986510468534929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84983735001315347291379905 63737801250986510468534929)
  ·
    refine ⟨47803350938239882851401197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63737801250986510468534929 47803350938239882851401197)
    ·
      refine ⟨17926256601839956069275449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47803350938239882851401197 17926256601839956069275449)
      ·
        refine ⟨13444692451379967051956587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17926256601839956069275449 13444692451379967051956587)
        ·
          refine ⟨20167038677069950577934881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13444692451379967051956587 20167038677069950577934881)
          ·
            refine ⟨15125279007802462933451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20167038677069950577934881 15125279007802462933451161)
            ·
              refine ⟨11343959255851847200088371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15125279007802462933451161 11343959255851847200088371)
              ·
                refine ⟨17015938883777770800132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11343959255851847200088371 17015938883777770800132557)
                ·
                  refine ⟨6380977081416664050049709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17015938883777770800132557 6380977081416664050049709)
                  ·
                    refine ⟨2392866405531249018768641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6380977081416664050049709 2392866405531249018768641)
                    ·
                      refine ⟨1794649804148436764076481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392866405531249018768641 1794649804148436764076481)
                      ·
                        rfl

theorem cell23_3495068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3495068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495068 prefixEnd_3495068 := by exact prefixLift 3495068
  have htrace : WordTrace (prefixWord ++ tailWord_3495068) baseStart_3495068 baseEnd_3495068 := by
    simpa [prefixWord, tailWord_3495068, baseEnd_3495068] using wordTrace_append hprefix tailTrace_3495068
  have hstable : (prefixWord ++ tailWord_3495068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495068).length < 2 ^ (prefixWord ++ tailWord_3495068).sum := by decide
  have hdescent : baseEnd_3495068 < baseStart_3495068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495084 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_3495084 : Nat := 118140960795 + 3495084 * 2 ^ 59
def prefixEnd_3495084 : Nat := 4983230072969 + 3 ^ 40 * 3495084 * 2
def baseEnd_3495084 : Nat := 1794658019838908701476407

theorem tailTrace_3495084 : CollatzResearch.WordTrace tailWord_3495084 prefixEnd_3495084 1794658019838908701476407 := by
  unfold tailWord_3495084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63738093034957527834826153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84984124046610037113101537 63738093034957527834826153)
  ·
    refine ⟨47803569776218145876119615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63738093034957527834826153 47803569776218145876119615)
    ·
      refine ⟨71705354664327218814179423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47803569776218145876119615 71705354664327218814179423)
      ·
        refine ⟨107558031996490828221269135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71705354664327218814179423 107558031996490828221269135)
        ·
          refine ⟨161337047994736242331903703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107558031996490828221269135 161337047994736242331903703)
          ·
            refine ⟨242005571992104363497855555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161337047994736242331903703 242005571992104363497855555)
            ·
              refine ⟨363008357988156545246783333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242005571992104363497855555 363008357988156545246783333)
              ·
                refine ⟨68064067122779352233771875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363008357988156545246783333 68064067122779352233771875)
                ·
                  refine ⟨102096100684169028350657813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68064067122779352233771875 102096100684169028350657813)
                  ·
                    refine ⟨4785754719570423203937085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102096100684169028350657813 4785754719570423203937085)
                    ·
                      refine ⟨1794658019838908701476407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4785754719570423203937085 1794658019838908701476407)
                      ·
                        rfl

theorem cell23_3495084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_3495084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495084 prefixEnd_3495084 := by exact prefixLift 3495084
  have htrace : WordTrace (prefixWord ++ tailWord_3495084) baseStart_3495084 baseEnd_3495084 := by
    simpa [prefixWord, tailWord_3495084, baseEnd_3495084] using wordTrace_append hprefix tailTrace_3495084
  have hstable : (prefixWord ++ tailWord_3495084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495084).length < 2 ^ (prefixWord ++ tailWord_3495084).sum := by decide
  have hdescent : baseEnd_3495084 < baseStart_3495084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495158 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_3495158 : Nat := 118140960795 + 3495158 * 2 ^ 59
def prefixEnd_3495158 : Nat := 4983230072969 + 3 ^ 40 * 3495158 * 2
def baseEnd_3495158 : Nat := 1794696017407341411951067

theorem tailTrace_3495158 : CollatzResearch.WordTrace tailWord_3495158 prefixEnd_3495158 1794696017407341411951067 := by
  unfold tailWord_3495158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967430316977935394240383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84985923381097977538564085 7967430316977935394240383)
  ·
    refine ⟨11951145475466903091360575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7967430316977935394240383 11951145475466903091360575)
    ·
      refine ⟨17926718213200354637040863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11951145475466903091360575 17926718213200354637040863)
      ·
        refine ⟨26890077319800531955561295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17926718213200354637040863 26890077319800531955561295)
        ·
          refine ⟨40335115979700797933341943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26890077319800531955561295 40335115979700797933341943)
          ·
            refine ⟨60502673969551196900012915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40335115979700797933341943 60502673969551196900012915)
            ·
              refine ⟨90754010954326795350019373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60502673969551196900012915 90754010954326795350019373)
              ·
                refine ⟨34032754107872548256257265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90754010954326795350019373 34032754107872548256257265)
                ·
                  refine ⟨25524565580904411192192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34032754107872548256257265 25524565580904411192192949)
                  ·
                    refine ⟨2392928023209788549268089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25524565580904411192192949 2392928023209788549268089)
                    ·
                      refine ⟨1794696017407341411951067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392928023209788549268089 1794696017407341411951067)
                      ·
                        rfl

theorem cell23_3495158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_3495158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495158 prefixEnd_3495158 := by exact prefixLift 3495158
  have htrace : WordTrace (prefixWord ++ tailWord_3495158) baseStart_3495158 baseEnd_3495158 := by
    simpa [prefixWord, tailWord_3495158, baseEnd_3495158] using wordTrace_append hprefix tailTrace_3495158
  have hstable : (prefixWord ++ tailWord_3495158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495158).length < 2 ^ (prefixWord ++ tailWord_3495158).sum := by decide
  have hdescent : baseEnd_3495158 < baseStart_3495158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495241 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_3495241 : Nat := 118140960795 + 3495241 * 2 ^ 59
def prefixEnd_3495241 : Nat := 4983230072969 + 3 ^ 40 * 3495241 * 2
def baseEnd_3495241 : Nat := 598246212100554862404395

theorem tailTrace_3495241 : CollatzResearch.WordTrace tailWord_3495241 prefixEnd_3495241 598246212100554862404395 := by
  unfold tailWord_3495241
  simp only [CollatzResearch.WordTrace]
  refine ⟨127481912330346271483117577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84987941553564180988745051 127481912330346271483117577)
  ·
    refine ⟨95611434247759703612338183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127481912330346271483117577 95611434247759703612338183)
    ·
      refine ⟨143417151371639555418507275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95611434247759703612338183 143417151371639555418507275)
      ·
        refine ⟨215125727057459333127760913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143417151371639555418507275 215125727057459333127760913)
        ·
          refine ⟨161344295293094499845820685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215125727057459333127760913 161344295293094499845820685)
          ·
            refine ⟨60504110734910437442182757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161344295293094499845820685 60504110734910437442182757)
            ·
              refine ⟨11344520762795707020409267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60504110734910437442182757 11344520762795707020409267)
              ·
                refine ⟨17016781144193560530613901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344520762795707020409267 17016781144193560530613901)
                ·
                  refine ⟨6381292929072585198980213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17016781144193560530613901 6381292929072585198980213)
                  ·
                    refine ⟨598246212100554862404395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6381292929072585198980213 598246212100554862404395)
                    ·
                      rfl

theorem cell23_3495241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_3495241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495241 prefixEnd_3495241 := by exact prefixLift 3495241
  have htrace : WordTrace (prefixWord ++ tailWord_3495241) baseStart_3495241 baseEnd_3495241 := by
    simpa [prefixWord, tailWord_3495241, baseEnd_3495241] using wordTrace_append hprefix tailTrace_3495241
  have hstable : (prefixWord ++ tailWord_3495241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495241).length < 2 ^ (prefixWord ++ tailWord_3495241).sum := by decide
  have hdescent : baseEnd_3495241 < baseStart_3495241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495248 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2]
def baseStart_3495248 : Nat := 118140960795 + 3495248 * 2 ^ 59
def prefixEnd_3495248 : Nat := 4983230072969 + 3 ^ 40 * 3495248 * 2
def baseEnd_3495248 : Nat := 1794742230666246059825653

theorem tailTrace_3495248 : CollatzResearch.WordTrace tailWord_3495248 prefixEnd_3495248 1794742230666246059825653 := by
  unfold tailWord_3495248
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741083820660455839311199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84988111760880607785748265 63741083820660455839311199)
  ·
    refine ⟨95611625730990683758966799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63741083820660455839311199 95611625730990683758966799)
    ·
      refine ⟨143417438596486025638450199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95611625730990683758966799 143417438596486025638450199)
      ·
        refine ⟨215126157894729038457675299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143417438596486025638450199 215126157894729038457675299)
        ·
          refine ⟨322689236842093557686512949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215126157894729038457675299 322689236842093557686512949)
          ·
            refine ⟨30252115953946271033110589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 322689236842093557686512949 30252115953946271033110589)
            ·
              refine ⟨11344543482729851637416471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30252115953946271033110589 11344543482729851637416471)
              ·
                refine ⟨17016815224094777456124707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344543482729851637416471 17016815224094777456124707)
                ·
                  refine ⟨25525222836142166184187061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17016815224094777456124707 25525222836142166184187061)
                  ·
                    refine ⟨2392989640888328079767537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25525222836142166184187061 2392989640888328079767537)
                    ·
                      refine ⟨1794742230666246059825653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2392989640888328079767537 1794742230666246059825653)
                      ·
                        rfl

theorem cell23_3495248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2].length) (baseStart_3495248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495248 prefixEnd_3495248 := by exact prefixLift 3495248
  have htrace : WordTrace (prefixWord ++ tailWord_3495248) baseStart_3495248 baseEnd_3495248 := by
    simpa [prefixWord, tailWord_3495248, baseEnd_3495248] using wordTrace_append hprefix tailTrace_3495248
  have hstable : (prefixWord ++ tailWord_3495248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495248).length < 2 ^ (prefixWord ++ tailWord_3495248).sum := by decide
  have hdescent : baseEnd_3495248 < baseStart_3495248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495272 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3495272 : Nat := 118140960795 + 3495272 * 2 ^ 59
def prefixEnd_3495272 : Nat := 4983230072969 + 3 ^ 40 * 3495272 * 2
def baseEnd_3495272 : Nat := 1794754554201953965925543

theorem tailTrace_3495272 : CollatzResearch.WordTrace tailWord_3495272 prefixEnd_3495272 1794754554201953965925543 := by
  unfold tailWord_3495272
  simp only [CollatzResearch.WordTrace]
  refine ⟨63741521496616981888748035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84988695328822642518330713 63741521496616981888748035)
  ·
    refine ⟨95612282244925472833122053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63741521496616981888748035 95612282244925472833122053)
    ·
      refine ⟨17927302920923526156210385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95612282244925472833122053 17927302920923526156210385)
      ·
        refine ⟨13445477190692644617157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17927302920923526156210385 13445477190692644617157789)
        ·
          refine ⟨5042053946509741731434171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13445477190692644617157789 5042053946509741731434171)
          ·
            refine ⟨7563080919764612597151257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042053946509741731434171 7563080919764612597151257)
            ·
              refine ⟨5672310689823459447863443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563080919764612597151257 5672310689823459447863443)
              ·
                refine ⟨8508466034735189171795165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5672310689823459447863443 8508466034735189171795165)
                ·
                  refine ⟨3190674763025695939423187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8508466034735189171795165 3190674763025695939423187)
                  ·
                    refine ⟨4786012144538543909134781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190674763025695939423187 4786012144538543909134781)
                    ·
                      refine ⟨1794754554201953965925543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786012144538543909134781 1794754554201953965925543)
                      ·
                        rfl

theorem cell23_3495272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3495272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495272 prefixEnd_3495272 := by exact prefixLift 3495272
  have htrace : WordTrace (prefixWord ++ tailWord_3495272) baseStart_3495272 baseEnd_3495272 := by
    simpa [prefixWord, tailWord_3495272, baseEnd_3495272] using wordTrace_append hprefix tailTrace_3495272
  have hstable : (prefixWord ++ tailWord_3495272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495272).length < 2 ^ (prefixWord ++ tailWord_3495272).sum := by decide
  have hdescent : baseEnd_3495272 < baseStart_3495272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495281 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3495281 : Nat := 118140960795 + 3495281 * 2 ^ 59
def prefixEnd_3495281 : Nat := 4983230072969 + 3 ^ 40 * 3495281 * 2
def baseEnd_3495281 : Nat := 1794759175527844430713001

theorem tailTrace_3495281 : CollatzResearch.WordTrace tailWord_3495281 prefixEnd_3495281 1794759175527844430713001 := by
  unfold tailWord_3495281
  simp only [CollatzResearch.WordTrace]
  refine ⟨127483371250201358314573697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84988914166800905543049131 127483371250201358314573697)
  ·
    refine ⟨95612528437651018735930273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127483371250201358314573697 95612528437651018735930273)
    ·
      refine ⟨71709396328238264051947705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95612528437651018735930273 71709396328238264051947705)
      ·
        refine ⟨53782047246178698038960779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71709396328238264051947705 53782047246178698038960779)
        ·
          refine ⟨80673070869268047058441169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53782047246178698038960779 80673070869268047058441169)
          ·
            refine ⟨60504803151951035293830877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80673070869268047058441169 60504803151951035293830877)
            ·
              refine ⟨22689301181981638235186579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60504803151951035293830877 22689301181981638235186579)
              ·
                refine ⟨34033951772972457352779869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689301181981638235186579 34033951772972457352779869)
                ·
                  refine ⟨12762731914864671507292451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34033951772972457352779869 12762731914864671507292451)
                  ·
                    refine ⟨19144097872297007260938677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12762731914864671507292451 19144097872297007260938677)
                    ·
                      refine ⟨1794759175527844430713001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19144097872297007260938677 1794759175527844430713001)
                      ·
                        rfl

theorem cell23_3495281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3495281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495281 prefixEnd_3495281 := by exact prefixLift 3495281
  have htrace : WordTrace (prefixWord ++ tailWord_3495281) baseStart_3495281 baseEnd_3495281 := by
    simpa [prefixWord, tailWord_3495281, baseEnd_3495281] using wordTrace_append hprefix tailTrace_3495281
  have hstable : (prefixWord ++ tailWord_3495281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495281).length < 2 ^ (prefixWord ++ tailWord_3495281).sum := by decide
  have hdescent : baseEnd_3495281 < baseStart_3495281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495291 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_3495291 : Nat := 118140960795 + 3495291 * 2 ^ 59
def prefixEnd_3495291 : Nat := 4983230072969 + 3 ^ 40 * 3495291 * 2
def baseEnd_3495291 : Nat := 1794764310334389391587955

theorem tailTrace_3495291 : CollatzResearch.WordTrace tailWord_3495291 prefixEnd_3495291 1794764310334389391587955 := by
  unfold tailWord_3495291
  simp only [CollatzResearch.WordTrace]
  refine ⟨127483735980165130022437727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84989157320110086681625151 127483735980165130022437727)
  ·
    refine ⟨191225603970247695033656591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127483735980165130022437727 191225603970247695033656591)
    ·
      refine ⟨286838405955371542550484887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191225603970247695033656591 286838405955371542550484887)
      ·
        refine ⟨430257608933057313825727331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286838405955371542550484887 430257608933057313825727331)
        ·
          refine ⟨645386413399585970738590997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430257608933057313825727331 645386413399585970738590997)
          ·
            refine ⟨30252488128105592378371453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 645386413399585970738590997 30252488128105592378371453)
            ·
              refine ⟨11344683048039597141889295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30252488128105592378371453 11344683048039597141889295)
              ·
                refine ⟨17017024572059395712833943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11344683048039597141889295 17017024572059395712833943)
                ·
                  refine ⟨25525536858089093569250915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17017024572059395712833943 25525536858089093569250915)
                  ·
                    refine ⟨38288305287133640353876373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25525536858089093569250915 38288305287133640353876373)
                    ·
                      refine ⟨1794764310334389391587955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38288305287133640353876373 1794764310334389391587955)
                      ·
                        rfl

theorem cell23_3495291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_3495291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495291 prefixEnd_3495291 := by exact prefixLift 3495291
  have htrace : WordTrace (prefixWord ++ tailWord_3495291) baseStart_3495291 baseEnd_3495291 := by
    simpa [prefixWord, tailWord_3495291, baseEnd_3495291] using wordTrace_append hprefix tailTrace_3495291
  have hstable : (prefixWord ++ tailWord_3495291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495291).length < 2 ^ (prefixWord ++ tailWord_3495291).sum := by decide
  have hdescent : baseEnd_3495291 < baseStart_3495291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495331 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 7]
def baseStart_3495331 : Nat := 118140960795 + 3495331 * 2 ^ 59
def prefixEnd_3495331 : Nat := 4983230072969 + 3 ^ 40 * 3495331 * 2
def baseEnd_3495331 : Nat := 598261616520189745029257

theorem tailTrace_3495331 : CollatzResearch.WordTrace tailWord_3495331 prefixEnd_3495331 598261616520189745029257 := by
  unfold tailWord_3495331
  simp only [CollatzResearch.WordTrace]
  refine ⟨127485194900020216853893847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84990129933346811235929231 127485194900020216853893847)
  ·
    refine ⟨191227792350030325280840771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127485194900020216853893847 191227792350030325280840771)
    ·
      refine ⟨286841688525045487921261157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191227792350030325280840771 286841688525045487921261157)
      ·
        refine ⟨53782816598446028985236467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286841688525045487921261157 53782816598446028985236467)
        ·
          refine ⟨80674224897669043477854701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53782816598446028985236467 80674224897669043477854701)
          ·
            refine ⟨30252834336625891304195513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80674224897669043477854701 30252834336625891304195513)
            ·
              refine ⟨22689625752469418478146635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30252834336625891304195513 22689625752469418478146635)
              ·
                refine ⟨34034438628704127717219953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22689625752469418478146635 34034438628704127717219953)
                ·
                  refine ⟨25525828971528095787914965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34034438628704127717219953 25525828971528095787914965)
                  ·
                    refine ⟨598261616520189745029257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25525828971528095787914965 598261616520189745029257)
                    ·
                      rfl

theorem cell23_3495331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_3495331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495331 prefixEnd_3495331 := by exact prefixLift 3495331
  have htrace : WordTrace (prefixWord ++ tailWord_3495331) baseStart_3495331 baseEnd_3495331 := by
    simpa [prefixWord, tailWord_3495331, baseEnd_3495331] using wordTrace_append hprefix tailTrace_3495331
  have hstable : (prefixWord ++ tailWord_3495331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495331).length < 2 ^ (prefixWord ++ tailWord_3495331).sum := by decide
  have hdescent : baseEnd_3495331 < baseStart_3495331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495380 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3495380 : Nat := 118140960795 + 3495380 * 2 ^ 59
def prefixEnd_3495380 : Nat := 4983230072969 + 3 ^ 40 * 3495380 * 2
def baseEnd_3495380 : Nat := 1794810010112639543375047

theorem tailTrace_3495380 : CollatzResearch.WordTrace tailWord_3495380 prefixEnd_3495380 1794810010112639543375047 := by
  unfold tailWord_3495380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63743491038421349111213797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84991321384561798814951729 63743491038421349111213797)
  ·
    refine ⟨11951904569704002958352587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63743491038421349111213797 11951904569704002958352587)
    ·
      refine ⟨17927856854556004437528881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11951904569704002958352587 17927856854556004437528881)
      ·
        refine ⟨13445892640917003328146661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17927856854556004437528881 13445892640917003328146661)
        ·
          refine ⟨2521104870171938124027499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13445892640917003328146661 2521104870171938124027499)
          ·
            refine ⟨3781657305257907186041249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521104870171938124027499 3781657305257907186041249)
            ·
              refine ⟨2836242978943430389530937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3781657305257907186041249 2836242978943430389530937)
              ·
                refine ⟨2127182234207572792148203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836242978943430389530937 2127182234207572792148203)
                ·
                  refine ⟨3190773351311359188222305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127182234207572792148203 3190773351311359188222305)
                  ·
                    refine ⟨2393080013483519391166729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3190773351311359188222305 2393080013483519391166729)
                    ·
                      refine ⟨1794810010112639543375047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393080013483519391166729 1794810010112639543375047)
                      ·
                        rfl

theorem cell23_3495380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3495380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495380 prefixEnd_3495380 := by exact prefixLift 3495380
  have htrace : WordTrace (prefixWord ++ tailWord_3495380) baseStart_3495380 baseEnd_3495380 := by
    simpa [prefixWord, tailWord_3495380, baseEnd_3495380] using wordTrace_append hprefix tailTrace_3495380
  have hstable : (prefixWord ++ tailWord_3495380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495380).length < 2 ^ (prefixWord ++ tailWord_3495380).sum := by decide
  have hdescent : baseEnd_3495380 < baseStart_3495380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495401 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_3495401 : Nat := 118140960795 + 3495401 * 2 ^ 59
def prefixEnd_3495401 : Nat := 4983230072969 + 3 ^ 40 * 3495401 * 2
def baseEnd_3495401 : Nat := 1794820793206383961212449

theorem tailTrace_3495401 : CollatzResearch.WordTrace tailWord_3495401 prefixEnd_3495401 1794820793206383961212449 := by
  unfold tailWord_3495401
  simp only [CollatzResearch.WordTrace]
  refine ⟨127487748009766618808942057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84991832006511079205961371 127487748009766618808942057)
  ·
    refine ⟨95615811007324964106706543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127487748009766618808942057 95615811007324964106706543)
    ·
      refine ⟨143423716510987446160059815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95615811007324964106706543 143423716510987446160059815)
      ·
        refine ⟨215135574766481169240089723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143423716510987446160059815 215135574766481169240089723)
        ·
          refine ⟨322703362149721753860134585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215135574766481169240089723 322703362149721753860134585)
          ·
            refine ⟨242027521612291315395100939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322703362149721753860134585 242027521612291315395100939)
            ·
              refine ⟨363041282418436973092651409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242027521612291315395100939 363041282418436973092651409)
              ·
                refine ⟨272280961813827729819488557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363041282418436973092651409 272280961813827729819488557)
                ·
                  refine ⟨102105360680185398682308209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272280961813827729819488557 102105360680185398682308209)
                  ·
                    refine ⟨76579020510139049011731157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102105360680185398682308209 76579020510139049011731157)
                    ·
                      refine ⟨1794820793206383961212449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76579020510139049011731157 1794820793206383961212449)
                      ·
                        rfl

theorem cell23_3495401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_3495401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495401 prefixEnd_3495401 := by exact prefixLift 3495401
  have htrace : WordTrace (prefixWord ++ tailWord_3495401) baseStart_3495401 baseEnd_3495401 := by
    simpa [prefixWord, tailWord_3495401, baseEnd_3495401] using wordTrace_append hprefix tailTrace_3495401
  have hstable : (prefixWord ++ tailWord_3495401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495401).length < 2 ^ (prefixWord ++ tailWord_3495401).sum := by decide
  have hdescent : baseEnd_3495401 < baseStart_3495401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495408 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 7]
def baseStart_3495408 : Nat := 118140960795 + 3495408 * 2 ^ 59
def prefixEnd_3495408 : Nat := 4983230072969 + 3 ^ 40 * 3495408 * 2
def baseEnd_3495408 : Nat := 199424931952329492647213

theorem tailTrace_3495408 : CollatzResearch.WordTrace tailWord_3495408 prefixEnd_3495408 199424931952329492647213 := by
  unfold tailWord_3495408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63744001660370629502223439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84992002213827506002964585 63744001660370629502223439)
  ·
    refine ⟨95616002490555944253335159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63744001660370629502223439 95616002490555944253335159)
    ·
      refine ⟨143424003735833916380002739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95616002490555944253335159 143424003735833916380002739)
      ·
        refine ⟨215136005603750874570004109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143424003735833916380002739 215136005603750874570004109)
        ·
          refine ⟨80676002101406577963751541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215136005603750874570004109 80676002101406577963751541)
          ·
            refine ⟨7563375197006866684101707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80676002101406577963751541 7563375197006866684101707)
            ·
              refine ⟨11345062795510300026152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563375197006866684101707 11345062795510300026152561)
              ·
                refine ⟨8508797096632725019614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11345062795510300026152561 8508797096632725019614421)
                ·
                  refine ⟨199424931952329492647213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8508797096632725019614421 199424931952329492647213)
                  ·
                    rfl

theorem cell23_3495408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 7].length) (baseStart_3495408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495408 prefixEnd_3495408 := by exact prefixLift 3495408
  have htrace : WordTrace (prefixWord ++ tailWord_3495408) baseStart_3495408 baseEnd_3495408 := by
    simpa [prefixWord, tailWord_3495408, baseEnd_3495408] using wordTrace_append hprefix tailTrace_3495408
  have hstable : (prefixWord ++ tailWord_3495408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495408).length < 2 ^ (prefixWord ++ tailWord_3495408).sum := by decide
  have hdescent : baseEnd_3495408 < baseStart_3495408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495418 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_3495418 : Nat := 118140960795 + 3495418 * 2 ^ 59
def prefixEnd_3495418 : Nat := 4983230072969 + 3 ^ 40 * 3495418 * 2
def baseEnd_3495418 : Nat := 1794829522377510394699871

theorem tailTrace_3495418 : CollatzResearch.WordTrace tailWord_3495418 prefixEnd_3495418 1794829522377510394699871 := by
  unfold tailWord_3495418
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872092012676257678077727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84992245367136687141540605 31872092012676257678077727)
  ·
    refine ⟨47808138019014386517116591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31872092012676257678077727 47808138019014386517116591)
    ·
      refine ⟨71712207028521579775674887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47808138019014386517116591 71712207028521579775674887)
      ·
        refine ⟨107568310542782369663512331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71712207028521579775674887 107568310542782369663512331)
        ·
          refine ⟨161352465814173554495268497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107568310542782369663512331 161352465814173554495268497)
          ·
            refine ⟨121014349360630165871451373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161352465814173554495268497 121014349360630165871451373)
            ·
              refine ⟨45380381010236312201794265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121014349360630165871451373 45380381010236312201794265)
              ·
                refine ⟨34035285757677234151345699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45380381010236312201794265 34035285757677234151345699)
                ·
                  refine ⟨51052928636515851227018549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34035285757677234151345699 51052928636515851227018549)
                  ·
                    refine ⟨4786212059673361052532989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51052928636515851227018549 4786212059673361052532989)
                    ·
                      refine ⟨1794829522377510394699871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786212059673361052532989 1794829522377510394699871)
                      ·
                        rfl

theorem cell23_3495418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_3495418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495418 prefixEnd_3495418 := by exact prefixLift 3495418
  have htrace : WordTrace (prefixWord ++ tailWord_3495418) baseStart_3495418 baseEnd_3495418 := by
    simpa [prefixWord, tailWord_3495418, baseEnd_3495418] using wordTrace_append hprefix tailTrace_3495418
  have hstable : (prefixWord ++ tailWord_3495418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495418).length < 2 ^ (prefixWord ++ tailWord_3495418).sum := by decide
  have hdescent : baseEnd_3495418 < baseStart_3495418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495430 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3495430 : Nat := 118140960795 + 3495430 * 2 ^ 59
def prefixEnd_3495430 : Nat := 4983230072969 + 3 ^ 40 * 3495430 * 2
def baseEnd_3495430 : Nat := 1794835684145364347749817

theorem tailTrace_3495430 : CollatzResearch.WordTrace tailWord_3495430 prefixEnd_3495430 1794835684145364347749817 := by
  unfold tailWord_3495430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984025178958173648804617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84992537151107704507831829 3984025178958173648804617)
  ·
    refine ⟨2988018884218630236603463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3984025178958173648804617 2988018884218630236603463)
    ·
      refine ⟨4482028326327945354905195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988018884218630236603463 4482028326327945354905195)
      ·
        refine ⟨6723042489491918032357793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482028326327945354905195 6723042489491918032357793)
        ·
          refine ⟨5042281867118938524268345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6723042489491918032357793 5042281867118938524268345)
          ·
            refine ⟨3781711400339203893201259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042281867118938524268345 3781711400339203893201259)
            ·
              refine ⟨5672567100508805839801889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781711400339203893201259 5672567100508805839801889)
              ·
                refine ⟨4254425325381604379851417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672567100508805839801889 4254425325381604379851417)
                ·
                  refine ⟨3190818994036203284888563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254425325381604379851417 3190818994036203284888563)
                  ·
                    refine ⟨4786228491054304927332845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3190818994036203284888563 4786228491054304927332845)
                    ·
                      refine ⟨1794835684145364347749817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786228491054304927332845 1794835684145364347749817)
                      ·
                        rfl

theorem cell23_3495430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3495430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495430 prefixEnd_3495430 := by exact prefixLift 3495430
  have htrace : WordTrace (prefixWord ++ tailWord_3495430) baseStart_3495430 baseEnd_3495430 := by
    simpa [prefixWord, tailWord_3495430, baseEnd_3495430] using wordTrace_append hprefix tailTrace_3495430
  have hstable : (prefixWord ++ tailWord_3495430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495430).length < 2 ^ (prefixWord ++ tailWord_3495430).sum := by decide
  have hdescent : baseEnd_3495430 < baseStart_3495430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495436 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_3495436 : Nat := 118140960795 + 3495436 * 2 ^ 59
def prefixEnd_3495436 : Nat := 4983230072969 + 3 ^ 40 * 3495436 * 2
def baseEnd_3495436 : Nat := 1794838765029291324274789

theorem tailTrace_3495436 : CollatzResearch.WordTrace tailWord_3495436 prefixEnd_3495436 1794838765029291324274789 := by
  unfold tailWord_3495436
  simp only [CollatzResearch.WordTrace]
  refine ⟨63744512282319909893233081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84992683043093213190977441 63744512282319909893233081)
  ·
    refine ⟨47808384211739932419924811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63744512282319909893233081 47808384211739932419924811)
    ·
      refine ⟨71712576317609898629887217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47808384211739932419924811 71712576317609898629887217)
      ·
        refine ⟨53784432238207423972415413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71712576317609898629887217 53784432238207423972415413)
        ·
          refine ⟨5042290522331945997413945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53784432238207423972415413 5042290522331945997413945)
          ·
            refine ⟨3781717891748959498060459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042290522331945997413945 3781717891748959498060459)
            ·
              refine ⟨5672576837623439247090689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3781717891748959498060459 5672576837623439247090689)
              ·
                refine ⟨4254432628217579435318017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672576837623439247090689 4254432628217579435318017)
                ·
                  refine ⟨3190824471163184576488513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254432628217579435318017 3190824471163184576488513)
                  ·
                    refine ⟨2393118353372388432366385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3190824471163184576488513 2393118353372388432366385)
                    ·
                      refine ⟨1794838765029291324274789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393118353372388432366385 1794838765029291324274789)
                      ·
                        rfl

theorem cell23_3495436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_3495436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495436 prefixEnd_3495436 := by exact prefixLift 3495436
  have htrace : WordTrace (prefixWord ++ tailWord_3495436) baseStart_3495436 baseEnd_3495436 := by
    simpa [prefixWord, tailWord_3495436, baseEnd_3495436] using wordTrace_append hprefix tailTrace_3495436
  have hstable : (prefixWord ++ tailWord_3495436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495436).length < 2 ^ (prefixWord ++ tailWord_3495436).sum := by decide
  have hdescent : baseEnd_3495436 < baseStart_3495436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495498 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_3495498 : Nat := 118140960795 + 3495498 * 2 ^ 59
def prefixEnd_3495498 : Nat := 4983230072969 + 3 ^ 40 * 3495498 * 2
def baseEnd_3495498 : Nat := 199430066758874453522167

theorem tailTrace_3495498 : CollatzResearch.WordTrace tailWord_3495498 prefixEnd_3495498 199430066758874453522167 := by
  unfold tailWord_3495498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872821472603801093805787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84994190593610136250148765 31872821472603801093805787)
  ·
    refine ⟨47809232208905701640708681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31872821472603801093805787 47809232208905701640708681)
    ·
      refine ⟨35856924156679276230531511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47809232208905701640708681 35856924156679276230531511)
      ·
        refine ⟨53785386235018914345797267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35856924156679276230531511 53785386235018914345797267)
        ·
          refine ⟨80678079352528371518695901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53785386235018914345797267 80678079352528371518695901)
          ·
            refine ⟨30254279757198139319510963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80678079352528371518695901 30254279757198139319510963)
            ·
              refine ⟨45381419635797208979266445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30254279757198139319510963 45381419635797208979266445)
              ·
                refine ⟨17018032363423953367224917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45381419635797208979266445 17018032363423953367224917)
                ·
                  refine ⟨199430066758874453522167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17018032363423953367224917 199430066758874453522167)
                  ·
                    rfl

theorem cell23_3495498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_3495498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495498 prefixEnd_3495498 := by exact prefixLift 3495498
  have htrace : WordTrace (prefixWord ++ tailWord_3495498) baseStart_3495498 baseEnd_3495498 := by
    simpa [prefixWord, tailWord_3495498, baseEnd_3495498] using wordTrace_append hprefix tailTrace_3495498
  have hstable : (prefixWord ++ tailWord_3495498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495498).length < 2 ^ (prefixWord ++ tailWord_3495498).sum := by decide
  have hdescent : baseEnd_3495498 < baseStart_3495498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495552 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2]
def baseStart_3495552 : Nat := 118140960795 + 3495552 * 2 ^ 59
def prefixEnd_3495552 : Nat := 4983230072969 + 3 ^ 40 * 3495552 * 2
def baseEnd_3495552 : Nat := 1794898328785212870424255

theorem tailTrace_3495552 : CollatzResearch.WordTrace tailWord_3495552 prefixEnd_3495552 1794898328785212870424255 := by
  unfold tailWord_3495552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63746627716109785798844455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84995503621479714398459273 63746627716109785798844455)
  ·
    refine ⟨95619941574164678698266683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63746627716109785798844455 95619941574164678698266683)
    ·
      refine ⟨143429912361247018047400025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95619941574164678698266683 143429912361247018047400025)
      ·
        refine ⟨107572434270935263535550019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143429912361247018047400025 107572434270935263535550019)
        ·
          refine ⟨161358651406402895303325029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107572434270935263535550019 161358651406402895303325029)
          ·
            refine ⟨30254747138700542869373443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161358651406402895303325029 30254747138700542869373443)
            ·
              refine ⟨45382120708050814304060165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30254747138700542869373443 45382120708050814304060165)
              ·
                refine ⟨8509147632759527682011281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45382120708050814304060165 8509147632759527682011281)
                ·
                  refine ⟨6381860724569645761508461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8509147632759527682011281 6381860724569645761508461)
                  ·
                    refine ⟨2393197771713617160565673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6381860724569645761508461 2393197771713617160565673)
                    ·
                      refine ⟨1794898328785212870424255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393197771713617160565673 1794898328785212870424255)
                      ·
                        rfl

theorem cell23_3495552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_3495552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495552 prefixEnd_3495552 := by exact prefixLift 3495552
  have htrace : WordTrace (prefixWord ++ tailWord_3495552) baseStart_3495552 baseEnd_3495552 := by
    simpa [prefixWord, tailWord_3495552, baseEnd_3495552] using wordTrace_append hprefix tailTrace_3495552
  have hstable : (prefixWord ++ tailWord_3495552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495552).length < 2 ^ (prefixWord ++ tailWord_3495552).sum := by decide
  have hdescent : baseEnd_3495552 < baseStart_3495552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495575 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 6]
def baseStart_3495575 : Nat := 118140960795 + 3495575 * 2 ^ 59
def prefixEnd_3495575 : Nat := 4983230072969 + 3 ^ 40 * 3495575 * 2
def baseEnd_3495575 : Nat := 598303379613422093478883

theorem tailTrace_3495575 : CollatzResearch.WordTrace tailWord_3495575 prefixEnd_3495575 598303379613422093478883 := by
  unfold tailWord_3495575
  simp only [CollatzResearch.WordTrace]
  refine ⟨127494094311136246525776179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84996062874090831017184119 127494094311136246525776179)
  ·
    refine ⟨191241141466704369788664269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127494094311136246525776179 191241141466704369788664269)
    ·
      refine ⟨71715428050014138670749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191241141466704369788664269 71715428050014138670749101)
      ·
        refine ⟨26893285518755302001530913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71715428050014138670749101 26893285518755302001530913)
        ·
          refine ⟨20169964139066476501148185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26893285518755302001530913 20169964139066476501148185)
          ·
            refine ⟨15127473104299857375861139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20169964139066476501148185 15127473104299857375861139)
            ·
              refine ⟨22691209656449786063791709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15127473104299857375861139 22691209656449786063791709)
              ·
                refine ⟨8509203621168669773921891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22691209656449786063791709 8509203621168669773921891)
                ·
                  refine ⟨12763805431753004660882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8509203621168669773921891 12763805431753004660882837)
                  ·
                    refine ⟨598303379613422093478883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12763805431753004660882837 598303379613422093478883)
                    ·
                      rfl

theorem cell23_3495575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_3495575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495575 prefixEnd_3495575 := by exact prefixLift 3495575
  have htrace : WordTrace (prefixWord ++ tailWord_3495575) baseStart_3495575 baseEnd_3495575 := by
    simpa [prefixWord, tailWord_3495575, baseEnd_3495575] using wordTrace_append hprefix tailTrace_3495575
  have hstable : (prefixWord ++ tailWord_3495575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495575).length < 2 ^ (prefixWord ++ tailWord_3495575).sum := by decide
  have hdescent : baseEnd_3495575 < baseStart_3495575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495586 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3495586 : Nat := 118140960795 + 3495586 * 2 ^ 59
def prefixEnd_3495586 : Nat := 4983230072969 + 3 ^ 40 * 3495586 * 2
def baseEnd_3495586 : Nat := 1794915787127465737399099

theorem tailTrace_3495586 : CollatzResearch.WordTrace tailWord_3495586 prefixEnd_3495586 1794915787127465737399099 := by
  unfold tailWord_3495586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31873623878524098851106653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84996330342730930269617741 31873623878524098851106653)
  ·
    refine ⟨11952608954446537069164995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31873623878524098851106653 11952608954446537069164995)
    ·
      refine ⟨17928913431669805603747493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11952608954446537069164995 17928913431669805603747493)
      ·
        refine ⟨3361671268438088550702655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17928913431669805603747493 3361671268438088550702655)
        ·
          refine ⟨5042506902657132826053983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361671268438088550702655 5042506902657132826053983)
          ·
            refine ⟨7563760353985699239080975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042506902657132826053983 7563760353985699239080975)
            ·
              refine ⟨11345640530978548858621463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563760353985699239080975 11345640530978548858621463)
              ·
                refine ⟨17018460796467823287932195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11345640530978548858621463 17018460796467823287932195)
                ·
                  refine ⟨25527691194701734931898293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17018460796467823287932195 25527691194701734931898293)
                  ·
                    refine ⟨2393221049503287649865465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25527691194701734931898293 2393221049503287649865465)
                    ·
                      refine ⟨1794915787127465737399099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393221049503287649865465 1794915787127465737399099)
                      ·
                        rfl

theorem cell23_3495586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3495586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495586 prefixEnd_3495586 := by exact prefixLift 3495586
  have htrace : WordTrace (prefixWord ++ tailWord_3495586) baseStart_3495586 baseEnd_3495586 := by
    simpa [prefixWord, tailWord_3495586, baseEnd_3495586] using wordTrace_append hprefix tailTrace_3495586
  have hstable : (prefixWord ++ tailWord_3495586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495586).length < 2 ^ (prefixWord ++ tailWord_3495586).sum := by decide
  have hdescent : baseEnd_3495586 < baseStart_3495586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495616 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 1, 2, 2]
def baseStart_3495616 : Nat := 118140960795 + 3495616 * 2 ^ 59
def prefixEnd_3495616 : Nat := 4983230072969 + 3 ^ 40 * 3495616 * 2
def baseEnd_3495616 : Nat := 1794931191547100620023961

theorem tailTrace_3495616 : CollatzResearch.WordTrace tailWord_3495616 prefixEnd_3495616 1794931191547100620023961 := by
  unfold tailWord_3495616
  simp only [CollatzResearch.WordTrace]
  refine ⟨63747794851993855264009351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84997059802658473685345801 63747794851993855264009351)
  ·
    refine ⟨95621692277990782896014027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63747794851993855264009351 95621692277990782896014027)
    ·
      refine ⟨143432538416986174344021041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95621692277990782896014027 143432538416986174344021041)
      ·
        refine ⟨107574403812739630758015781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143432538416986174344021041 107574403812739630758015781)
        ·
          refine ⟨20170200714888680767127959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107574403812739630758015781 20170200714888680767127959)
          ·
            refine ⟨30255301072333021150691939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20170200714888680767127959 30255301072333021150691939)
            ·
              refine ⟨45382951608499531726037909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30255301072333021150691939 45382951608499531726037909)
              ·
                refine ⟨2127325856648415549658027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45382951608499531726037909 2127325856648415549658027)
                ·
                  refine ⟨3190988784972623324487041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127325856648415549658027 3190988784972623324487041)
                  ·
                    refine ⟨2393241588729467493365281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3190988784972623324487041 2393241588729467493365281)
                    ·
                      refine ⟨1794931191547100620023961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393241588729467493365281 1794931191547100620023961)
                      ·
                        rfl

theorem cell23_3495616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_3495616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495616 prefixEnd_3495616 := by exact prefixLift 3495616
  have htrace : WordTrace (prefixWord ++ tailWord_3495616) baseStart_3495616 baseEnd_3495616 := by
    simpa [prefixWord, tailWord_3495616, baseEnd_3495616] using wordTrace_append hprefix tailTrace_3495616
  have hstable : (prefixWord ++ tailWord_3495616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495616).length < 2 ^ (prefixWord ++ tailWord_3495616).sum := by decide
  have hdescent : baseEnd_3495616 < baseStart_3495616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495626 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_3495626 : Nat := 118140960795 + 3495626 * 2 ^ 59
def prefixEnd_3495626 : Nat := 4983230072969 + 3 ^ 40 * 3495626 * 2
def baseEnd_3495626 : Nat := 598312108784548526966305

theorem tailTrace_3495626 : CollatzResearch.WordTrace tailWord_3495626 prefixEnd_3495626 598312108784548526966305 := by
  unfold tailWord_3495626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31873988608487870558970683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84997302955967654823921821 31873988608487870558970683)
  ·
    refine ⟨47810982912731805838456025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31873988608487870558970683 47810982912731805838456025)
    ·
      refine ⟨35858237184548854378842019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47810982912731805838456025 35858237184548854378842019)
      ·
        refine ⟨53787355776823281568263029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35858237184548854378842019 53787355776823281568263029)
        ·
          refine ⟨5042564604077182647024659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53787355776823281568263029 5042564604077182647024659)
          ·
            refine ⟨7563846906115773970536989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042564604077182647024659 7563846906115773970536989)
            ·
              refine ⟨2836442589793415238951371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7563846906115773970536989 2836442589793415238951371)
              ·
                refine ⟨4254663884690122858427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836442589793415238951371 4254663884690122858427057)
                ·
                  refine ⟨3190997913517592143820293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254663884690122858427057 3190997913517592143820293)
                  ·
                    refine ⟨598312108784548526966305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3190997913517592143820293 598312108784548526966305)
                    ·
                      rfl

theorem cell23_3495626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_3495626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495626 prefixEnd_3495626 := by exact prefixLift 3495626
  have htrace : WordTrace (prefixWord ++ tailWord_3495626) baseStart_3495626 baseEnd_3495626 := by
    simpa [prefixWord, tailWord_3495626, baseEnd_3495626] using wordTrace_append hprefix tailTrace_3495626
  have hstable : (prefixWord ++ tailWord_3495626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495626).length < 2 ^ (prefixWord ++ tailWord_3495626).sum := by decide
  have hdescent : baseEnd_3495626 < baseStart_3495626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495629 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3495629 : Nat := 118140960795 + 3495629 * 2 ^ 59
def prefixEnd_3495629 : Nat := 4983230072969 + 3 ^ 40 * 3495629 * 2
def baseEnd_3495629 : Nat := 1794937866795609069161401

theorem tailTrace_3495629 : CollatzResearch.WordTrace tailWord_3495629 prefixEnd_3495629 1794937866795609069161401 := by
  unfold tailWord_3495629
  simp only [CollatzResearch.WordTrace]
  refine ⟨127496063852940613748241941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84997375901960409165494627 127496063852940613748241941)
  ·
    refine ⟨5976377993106591269448841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127496063852940613748241941 5976377993106591269448841)
    ·
      refine ⟨4482283494829943452086631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5976377993106591269448841 4482283494829943452086631)
      ·
        refine ⟨6723425242244915178129947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482283494829943452086631 6723425242244915178129947)
        ·
          refine ⟨10085137863367372767194921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723425242244915178129947 10085137863367372767194921)
          ·
            refine ⟨7563853397525529575396191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10085137863367372767194921 7563853397525529575396191)
            ·
              refine ⟨11345780096288294363094287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7563853397525529575396191 11345780096288294363094287)
              ·
                refine ⟨17018670144432441544641431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11345780096288294363094287 17018670144432441544641431)
                ·
                  refine ⟨25528005216648662316962147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17018670144432441544641431 25528005216648662316962147)
                  ·
                    refine ⟨38292007824972993475443221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25528005216648662316962147 38292007824972993475443221)
                    ·
                      refine ⟨1794937866795609069161401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38292007824972993475443221 1794937866795609069161401)
                      ·
                        rfl

theorem cell23_3495629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3495629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495629 prefixEnd_3495629 := by exact prefixLift 3495629
  have htrace : WordTrace (prefixWord ++ tailWord_3495629) baseStart_3495629 baseEnd_3495629 := by
    simpa [prefixWord, tailWord_3495629, baseEnd_3495629] using wordTrace_append hprefix tailTrace_3495629
  have hstable : (prefixWord ++ tailWord_3495629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495629).length < 2 ^ (prefixWord ++ tailWord_3495629).sum := by decide
  have hdescent : baseEnd_3495629 < baseStart_3495629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495636 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3495636 : Nat := 118140960795 + 3495636 * 2 ^ 59
def prefixEnd_3495636 : Nat := 4983230072969 + 3 ^ 40 * 3495636 * 2
def baseEnd_3495636 : Nat := 1794941461160190541773869

theorem tailTrace_3495636 : CollatzResearch.WordTrace tailWord_3495636 prefixEnd_3495636 1794941461160190541773869 := by
  unfold tailWord_3495636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748159581957626971873381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84997546109276835962497841 63748159581957626971873381)
  ·
    refine ⟨11952779921617055057226259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63748159581957626971873381 11952779921617055057226259)
    ·
      refine ⟨17929169882425582585839389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11952779921617055057226259 17929169882425582585839389)
      ·
        refine ⟨6723438705909593469689771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17929169882425582585839389 6723438705909593469689771)
        ·
          refine ⟨10085158058864390204534657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723438705909593469689771 10085158058864390204534657)
          ·
            refine ⟨7563868544148292653400993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10085158058864390204534657 7563868544148292653400993)
            ·
              refine ⟨5672901408111219490050745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563868544148292653400993 5672901408111219490050745)
              ·
                refine ⟨4254676056083414617538059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5672901408111219490050745 4254676056083414617538059)
                ·
                  refine ⟨6382014084125121926307089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254676056083414617538059 6382014084125121926307089)
                  ·
                    refine ⟨4786510563093841444730317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6382014084125121926307089 4786510563093841444730317)
                    ·
                      refine ⟨1794941461160190541773869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786510563093841444730317 1794941461160190541773869)
                      ·
                        rfl

theorem cell23_3495636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3495636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495636 prefixEnd_3495636 := by exact prefixLift 3495636
  have htrace : WordTrace (prefixWord ++ tailWord_3495636) baseStart_3495636 baseEnd_3495636 := by
    simpa [prefixWord, tailWord_3495636, baseEnd_3495636] using wordTrace_append hprefix tailTrace_3495636
  have hstable : (prefixWord ++ tailWord_3495636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495636).length < 2 ^ (prefixWord ++ tailWord_3495636).sum := by decide
  have hdescent : baseEnd_3495636 < baseStart_3495636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495659 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 1, 3, 2]
def baseStart_3495659 : Nat := 118140960795 + 3495659 * 2 ^ 59
def prefixEnd_3495659 : Nat := 4983230072969 + 3 ^ 40 * 3495659 * 2
def baseEnd_3495659 : Nat := 1794953271215243951786263

theorem tailTrace_3495659 : CollatzResearch.WordTrace tailWord_3495659 prefixEnd_3495659 1794953271215243951786263 := by
  unfold tailWord_3495659
  simp only [CollatzResearch.WordTrace]
  refine ⟨127497158042831928871834031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84998105361887952581222687 127497158042831928871834031)
  ·
    refine ⟨191245737064247893307751047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127497158042831928871834031 191245737064247893307751047)
    ·
      refine ⟨286868605596371839961626571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191245737064247893307751047 286868605596371839961626571)
      ·
        refine ⟨430302908394557759942439857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286868605596371839961626571 430302908394557759942439857)
        ·
          refine ⟨322727181295918319956829893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430302908394557759942439857 322727181295918319956829893)
          ·
            refine ⟨60511346492984684991905605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322727181295918319956829893 60511346492984684991905605)
            ·
              refine ⟨11345877467434628435982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60511346492984684991905605 11345877467434628435982301)
              ·
                refine ⟨4254704050287985663493363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11345877467434628435982301 4254704050287985663493363)
                ·
                  refine ⟨6382056075431978495240045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4254704050287985663493363 6382056075431978495240045)
                  ·
                    refine ⟨2393271028286991935715017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6382056075431978495240045 2393271028286991935715017)
                    ·
                      refine ⟨1794953271215243951786263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393271028286991935715017 1794953271215243951786263)
                      ·
                        rfl

theorem cell23_3495659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 3, 2].length) (baseStart_3495659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495659 prefixEnd_3495659 := by exact prefixLift 3495659
  have htrace : WordTrace (prefixWord ++ tailWord_3495659) baseStart_3495659 baseEnd_3495659 := by
    simpa [prefixWord, tailWord_3495659, baseEnd_3495659] using wordTrace_append hprefix tailTrace_3495659
  have hstable : (prefixWord ++ tailWord_3495659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495659).length < 2 ^ (prefixWord ++ tailWord_3495659).sum := by decide
  have hdescent : baseEnd_3495659 < baseStart_3495659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2]
def baseStart_3495672 : Nat := 118140960795 + 3495672 * 2 ^ 59
def prefixEnd_3495672 : Nat := 4983230072969 + 3 ^ 40 * 3495672 * 2
def baseEnd_3495672 : Nat := 1794959946463752400923703

theorem tailTrace_3495672 : CollatzResearch.WordTrace tailWord_3495672 prefixEnd_3495672 1794959946463752400923703 := by
  unfold tailWord_3495672
  simp only [CollatzResearch.WordTrace]
  refine ⟨63748816095892416046028635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84998421461189888061371513 63748816095892416046028635)
  ·
    refine ⟨95623224143838624069042953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63748816095892416046028635 95623224143838624069042953)
    ·
      refine ⟨71717418107878968051782215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95623224143838624069042953 71717418107878968051782215)
      ·
        refine ⟨107576127161818452077673323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71717418107878968051782215 107576127161818452077673323)
        ·
          refine ⟨161364190742727678116509985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107576127161818452077673323 161364190742727678116509985)
          ·
            refine ⟨121023143057045758587382489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161364190742727678116509985 121023143057045758587382489)
            ·
              refine ⟨90767357292784318940536867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121023143057045758587382489 90767357292784318940536867)
              ·
                refine ⟨136151035939176478410805301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90767357292784318940536867 136151035939176478410805301)
                ·
                  refine ⟨12764159619297794851012997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136151035939176478410805301 12764159619297794851012997)
                  ·
                    refine ⟨2393279928618336534564937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12764159619297794851012997 2393279928618336534564937)
                    ·
                      refine ⟨1794959946463752400923703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393279928618336534564937 1794959946463752400923703)
                      ·
                        rfl

theorem cell23_3495672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_3495672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495672 prefixEnd_3495672 := by exact prefixLift 3495672
  have htrace : WordTrace (prefixWord ++ tailWord_3495672) baseStart_3495672 baseEnd_3495672 := by
    simpa [prefixWord, tailWord_3495672, baseEnd_3495672] using wordTrace_append hprefix tailTrace_3495672
  have hstable : (prefixWord ++ tailWord_3495672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495672).length < 2 ^ (prefixWord ++ tailWord_3495672).sum := by decide
  have hdescent : baseEnd_3495672 < baseStart_3495672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495682 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3495682 : Nat := 118140960795 + 3495682 * 2 ^ 59
def prefixEnd_3495682 : Nat := 4983230072969 + 3 ^ 40 * 3495682 * 2
def baseEnd_3495682 : Nat := 598321693756765787266219

theorem tailTrace_3495682 : CollatzResearch.WordTrace tailWord_3495682 prefixEnd_3495682 598321693756765787266219 := by
  unfold tailWord_3495682
  simp only [CollatzResearch.WordTrace]
  refine ⟨31874499230437150949980325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84998664614499069199947533 31874499230437150949980325)
  ·
    refine ⟨5976468605706965803121311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31874499230437150949980325 5976468605706965803121311)
    ·
      refine ⟨8964702908560448704681967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976468605706965803121311 8964702908560448704681967)
      ·
        refine ⟨13447054362840673057022951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8964702908560448704681967 13447054362840673057022951)
        ·
          refine ⟨20170581544261009585534427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13447054362840673057022951 20170581544261009585534427)
          ·
            refine ⟨30255872316391514378301641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20170581544261009585534427 30255872316391514378301641)
            ·
              refine ⟨22691904237293635783726231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30255872316391514378301641 22691904237293635783726231)
              ·
                refine ⟨34037856355940453675589347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22691904237293635783726231 34037856355940453675589347)
                ·
                  refine ⟨51056784533910680513384021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34037856355940453675589347 51056784533910680513384021)
                  ·
                    refine ⟨598321693756765787266219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51056784533910680513384021 598321693756765787266219)
                    ·
                      rfl

theorem cell23_3495682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3495682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495682 prefixEnd_3495682 := by exact prefixLift 3495682
  have htrace : WordTrace (prefixWord ++ tailWord_3495682) baseStart_3495682 baseEnd_3495682 := by
    simpa [prefixWord, tailWord_3495682, baseEnd_3495682] using wordTrace_append hprefix tailTrace_3495682
  have hstable : (prefixWord ++ tailWord_3495682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495682).length < 2 ^ (prefixWord ++ tailWord_3495682).sum := by decide
  have hdescent : baseEnd_3495682 < baseStart_3495682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495729 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 5]
def baseStart_3495729 : Nat := 118140960795 + 3495729 * 2 ^ 59
def prefixEnd_3495729 : Nat := 4983230072969 + 3 ^ 40 * 3495729 * 2
def baseEnd_3495729 : Nat := 199443246095673186434549

theorem tailTrace_3495729 : CollatzResearch.WordTrace tailWord_3495729 prefixEnd_3495729 199443246095673186434549 := by
  unfold tailWord_3495729
  simp only [CollatzResearch.WordTrace]
  refine ⟨127499711152578330826882241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84999807435052220551254827 127499711152578330826882241)
  ·
    refine ⟨95624783364433748120161681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127499711152578330826882241 95624783364433748120161681)
    ·
      refine ⟨71718587523325311090121261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95624783364433748120161681 71718587523325311090121261)
      ·
        refine ⟨26894470321246991658795473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71718587523325311090121261 26894470321246991658795473)
        ·
          refine ⟨20170852740935243744096605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26894470321246991658795473 20170852740935243744096605)
          ·
            refine ⟨7564069777850716404036227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20170852740935243744096605 7564069777850716404036227)
            ·
              refine ⟨11346104666776074606054341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564069777850716404036227 11346104666776074606054341)
              ·
                refine ⟨2127394625020513988635189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11346104666776074606054341 2127394625020513988635189)
                ·
                  refine ⟨199443246095673186434549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2127394625020513988635189 199443246095673186434549)
                  ·
                    rfl

theorem cell23_3495729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 5].length) (baseStart_3495729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495729 prefixEnd_3495729 := by exact prefixLift 3495729
  have htrace : WordTrace (prefixWord ++ tailWord_3495729) baseStart_3495729 baseEnd_3495729 := by
    simpa [prefixWord, tailWord_3495729, baseEnd_3495729] using wordTrace_append hprefix tailTrace_3495729
  have hstable : (prefixWord ++ tailWord_3495729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495729).length < 2 ^ (prefixWord ++ tailWord_3495729).sum := by decide
  have hdescent : baseEnd_3495729 < baseStart_3495729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495735 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_3495735 : Nat := 118140960795 + 3495735 * 2 ^ 59
def prefixEnd_3495735 : Nat := 4983230072969 + 3 ^ 40 * 3495735 * 2
def baseEnd_3495735 : Nat := 1794992295744985654435913

theorem tailTrace_3495735 : CollatzResearch.WordTrace tailWord_3495735 prefixEnd_3495735 1794992295744985654435913 := by
  unfold tailWord_3495735
  simp only [CollatzResearch.WordTrace]
  refine ⟨127499929990556593851600659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84999953327037729234400439 127499929990556593851600659)
  ·
    refine ⟨191249894985834890777400989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127499929990556593851600659 191249894985834890777400989)
    ·
      refine ⟨71718710619688084041525371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191249894985834890777400989 71718710619688084041525371)
      ·
        refine ⟨107578065929532126062288057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71718710619688084041525371 107578065929532126062288057)
        ·
          refine ⟨80683549447149094546716043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107578065929532126062288057 80683549447149094546716043)
          ·
            refine ⟨121025324170723641820074065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80683549447149094546716043 121025324170723641820074065)
            ·
              refine ⟨90768993128042731365055549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121025324170723641820074065 90768993128042731365055549)
              ·
                refine ⟨34038372423016024261895831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90768993128042731365055549 34038372423016024261895831)
                ·
                  refine ⟨51057558634524036392843747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34038372423016024261895831 51057558634524036392843747)
                  ·
                    refine ⟨76586337951786054589265621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51057558634524036392843747 76586337951786054589265621)
                    ·
                      refine ⟨1794992295744985654435913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76586337951786054589265621 1794992295744985654435913)
                      ·
                        rfl

theorem cell23_3495735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_3495735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495735 prefixEnd_3495735 := by exact prefixLift 3495735
  have htrace : WordTrace (prefixWord ++ tailWord_3495735) baseStart_3495735 baseEnd_3495735 := by
    simpa [prefixWord, tailWord_3495735, baseEnd_3495735] using wordTrace_append hprefix tailTrace_3495735
  have hstable : (prefixWord ++ tailWord_3495735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495735).length < 2 ^ (prefixWord ++ tailWord_3495735).sum := by decide
  have hdescent : baseEnd_3495735 < baseStart_3495735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495789 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3495789 : Nat := 118140960795 + 3495789 * 2 ^ 59
def prefixEnd_3495789 : Nat := 4983230072969 + 3 ^ 40 * 3495789 * 2
def baseEnd_3495789 : Nat := 598340007900109481053555

theorem tailTrace_3495789 : CollatzResearch.WordTrace tailWord_3495789 prefixEnd_3495789 598340007900109481053555 := by
  unfold tailWord_3495789
  simp only [CollatzResearch.WordTrace]
  refine ⟨127501899532360961074066421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85001266354907307382710947 127501899532360961074066421)
  ·
    refine ⟨11953303081158840100693727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127501899532360961074066421 11953303081158840100693727)
    ·
      refine ⟨17929954621738260151040591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11953303081158840100693727 17929954621738260151040591)
      ·
        refine ⟨26894931932607390226560887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17929954621738260151040591 26894931932607390226560887)
        ·
          refine ⟨40342397898911085339841331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26894931932607390226560887 40342397898911085339841331)
          ·
            refine ⟨60513596848366628009761997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40342397898911085339841331 60513596848366628009761997)
            ·
              refine ⟨22692598818137485503660749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60513596848366628009761997 22692598818137485503660749)
              ·
                refine ⟨8509724556801557063872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22692598818137485503660749 8509724556801557063872781)
                ·
                  refine ⟨3191146708800583898952293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8509724556801557063872781 3191146708800583898952293)
                  ·
                    refine ⟨598340007900109481053555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191146708800583898952293 598340007900109481053555)
                    ·
                      rfl

theorem cell23_3495789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3495789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495789 prefixEnd_3495789 := by exact prefixLift 3495789
  have htrace : WordTrace (prefixWord ++ tailWord_3495789) baseStart_3495789 baseEnd_3495789 := by
    simpa [prefixWord, tailWord_3495789, baseEnd_3495789] using wordTrace_append hprefix tailTrace_3495789
  have hstable : (prefixWord ++ tailWord_3495789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495789).length < 2 ^ (prefixWord ++ tailWord_3495789).sum := by decide
  have hdescent : baseEnd_3495789 < baseStart_3495789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495802 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_3495802 : Nat := 118140960795 + 3495802 * 2 ^ 59
def prefixEnd_3495802 : Nat := 4983230072969 + 3 ^ 40 * 3495802 * 2
def baseEnd_3495802 : Nat := 199447410994315210255345

theorem tailTrace_3495802 : CollatzResearch.WordTrace tailWord_3495802 prefixEnd_3495802 199447410994315210255345 := by
  unfold tailWord_3495802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31875593420328466073572415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85001582454209242862859773 31875593420328466073572415)
  ·
    refine ⟨47813390130492699110358623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31875593420328466073572415 47813390130492699110358623)
    ·
      refine ⟨71720085195739048665537935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47813390130492699110358623 71720085195739048665537935)
      ·
        refine ⟨107580127793608572998306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71720085195739048665537935 107580127793608572998306903)
        ·
          refine ⟨161370191690412859497460355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107580127793608572998306903 161370191690412859497460355)
          ·
            refine ⟨242055287535619289246190533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161370191690412859497460355 242055287535619289246190533)
            ·
              refine ⟨45385366412928616733660725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242055287535619289246190533 45385366412928616733660725)
              ·
                refine ⟨4254878101212057818780693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45385366412928616733660725 4254878101212057818780693)
                ·
                  refine ⟨199447410994315210255345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4254878101212057818780693 199447410994315210255345)
                  ·
                    rfl

theorem cell23_3495802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_3495802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495802 prefixEnd_3495802 := by exact prefixLift 3495802
  have htrace : WordTrace (prefixWord ++ tailWord_3495802) baseStart_3495802 baseEnd_3495802 := by
    simpa [prefixWord, tailWord_3495802, baseEnd_3495802] using wordTrace_append hprefix tailTrace_3495802
  have hstable : (prefixWord ++ tailWord_3495802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495802).length < 2 ^ (prefixWord ++ tailWord_3495802).sum := by decide
  have hdescent : baseEnd_3495802 < baseStart_3495802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495830 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3495830 : Nat := 118140960795 + 3495830 * 2 ^ 59
def prefixEnd_3495830 : Nat := 4983230072969 + 3 ^ 40 * 3495830 * 2
def baseEnd_3495830 : Nat := 1795041076407162782747977

theorem tailTrace_3495830 : CollatzResearch.WordTrace tailWord_3495830 prefixEnd_3495830 1795041076407162782747977 := by
  unfold tailWord_3495830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968962182825776567269309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85002263283474950050872629 7968962182825776567269309)
  ·
    refine ⟨2988360818559666212725991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7968962182825776567269309 2988360818559666212725991)
    ·
      refine ⟨4482541227839499319088987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988360818559666212725991 4482541227839499319088987)
      ·
        refine ⟨6723811841759248978633481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482541227839499319088987 6723811841759248978633481)
        ·
          refine ⟨5042858881319436733975111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6723811841759248978633481 5042858881319436733975111)
          ·
            refine ⟨7564288321979155100962667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5042858881319436733975111 7564288321979155100962667)
            ·
              refine ⟨11346432482968732651444001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564288321979155100962667 11346432482968732651444001)
              ·
                refine ⟨8509824362226549488583001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11346432482968732651444001 8509824362226549488583001)
                ·
                  refine ⟨6382368271669912116437251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8509824362226549488583001 6382368271669912116437251)
                  ·
                    refine ⟨9573552407504868174655877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382368271669912116437251 9573552407504868174655877)
                    ·
                      refine ⟨1795041076407162782747977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9573552407504868174655877 1795041076407162782747977)
                      ·
                        rfl

theorem cell23_3495830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3495830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495830 prefixEnd_3495830 := by exact prefixLift 3495830
  have htrace : WordTrace (prefixWord ++ tailWord_3495830) baseStart_3495830 baseEnd_3495830 := by
    simpa [prefixWord, tailWord_3495830, baseEnd_3495830] using wordTrace_append hprefix tailTrace_3495830
  have hstable : (prefixWord ++ tailWord_3495830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495830).length < 2 ^ (prefixWord ++ tailWord_3495830).sum := by decide
  have hdescent : baseEnd_3495830 < baseStart_3495830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495896 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_3495896 : Nat := 118140960795 + 3495896 * 2 ^ 59
def prefixEnd_3495896 : Nat := 4983230072969 + 3 ^ 40 * 3495896 * 2
def baseEnd_3495896 : Nat := 598358322043453174840891

theorem tailTrace_3495896 : CollatzResearch.WordTrace tailWord_3495896 prefixEnd_3495896 598358322043453174840891 := by
  unfold tailWord_3495896
  simp only [CollatzResearch.WordTrace]
  refine ⟨63752901071486659174105771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85003868095315545565474361 63752901071486659174105771)
  ·
    refine ⟨95629351607229988761158657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63752901071486659174105771 95629351607229988761158657)
    ·
      refine ⟨71722013705422491570868993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95629351607229988761158657 71722013705422491570868993)
      ·
        refine ⟨53791510279066868678151745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71722013705422491570868993 53791510279066868678151745)
        ·
          refine ⟨40343632709300151508613809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53791510279066868678151745 40343632709300151508613809)
          ·
            refine ⟨30257724531975113631460357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40343632709300151508613809 30257724531975113631460357)
            ·
              refine ⟨5673323349745333805898817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30257724531975113631460357 5673323349745333805898817)
              ·
                refine ⟨4254992512309000354424113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673323349745333805898817 4254992512309000354424113)
                ·
                  refine ⟨3191244384231750265818085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4254992512309000354424113 3191244384231750265818085)
                  ·
                    refine ⟨598358322043453174840891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191244384231750265818085 598358322043453174840891)
                    ·
                      rfl

theorem cell23_3495896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_3495896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495896 prefixEnd_3495896 := by exact prefixLift 3495896
  have htrace : WordTrace (prefixWord ++ tailWord_3495896) baseStart_3495896 baseEnd_3495896 := by
    simpa [prefixWord, tailWord_3495896, baseEnd_3495896] using wordTrace_append hprefix tailTrace_3495896
  have hstable : (prefixWord ++ tailWord_3495896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495896).length < 2 ^ (prefixWord ++ tailWord_3495896).sum := by decide
  have hdescent : baseEnd_3495896 < baseStart_3495896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495897 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 1, 1, 3]
def baseStart_3495897 : Nat := 118140960795 + 3495897 * 2 ^ 59
def prefixEnd_3495897 : Nat := 4983230072969 + 3 ^ 40 * 3495897 * 2
def baseEnd_3495897 : Nat := 1795075479611014020610169

theorem tailTrace_3495897 : CollatzResearch.WordTrace tailWord_3495897 prefixEnd_3495897 1795075479611014020610169 := by
  unfold tailWord_3495897
  simp only [CollatzResearch.WordTrace]
  refine ⟨127505838615969695518997945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85003892410646463679331963 127505838615969695518997945)
  ·
    refine ⟨95629378961977271639248459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127505838615969695518997945 95629378961977271639248459)
    ·
      refine ⟨143444068442965907458872689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95629378961977271639248459 143444068442965907458872689)
      ·
        refine ⟨107583051332224430594154517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143444068442965907458872689 107583051332224430594154517)
        ·
          refine ⟨5042955531198020184100993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107583051332224430594154517 5042955531198020184100993)
          ·
            refine ⟨3782216648398515138075745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042955531198020184100993 3782216648398515138075745)
            ·
              refine ⟨2836662486298886353556809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782216648398515138075745 2836662486298886353556809)
              ·
                refine ⟨2127496864724164765167607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2836662486298886353556809 2127496864724164765167607)
                ·
                  refine ⟨3191245297086247147751411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2127496864724164765167607 3191245297086247147751411)
                  ·
                    refine ⟨4786867945629370721627117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191245297086247147751411 4786867945629370721627117)
                    ·
                      refine ⟨1795075479611014020610169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786867945629370721627117 1795075479611014020610169)
                      ·
                        rfl

theorem cell23_3495897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_3495897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495897 prefixEnd_3495897 := by exact prefixLift 3495897
  have htrace : WordTrace (prefixWord ++ tailWord_3495897) baseStart_3495897 baseEnd_3495897 := by
    simpa [prefixWord, tailWord_3495897, baseEnd_3495897] using wordTrace_append hprefix tailTrace_3495897
  have hstable : (prefixWord ++ tailWord_3495897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495897).length < 2 ^ (prefixWord ++ tailWord_3495897).sum := by decide
  have hdescent : baseEnd_3495897 < baseStart_3495897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495940 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3495940 : Nat := 118140960795 + 3495940 * 2 ^ 59
def prefixEnd_3495940 : Nat := 4983230072969 + 3 ^ 40 * 3495940 * 2
def baseEnd_3495940 : Nat := 1795097559279157352372471

theorem tailTrace_3495940 : CollatzResearch.WordTrace tailWord_3495940 prefixEnd_3495940 1795097559279157352372471 := by
  unfold tailWord_3495940
  simp only [CollatzResearch.WordTrace]
  refine ⟨63753703477406956931406637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85004937969875942575208849 63753703477406956931406637)
  ·
    refine ⟨23907638804027608849277489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63753703477406956931406637 23907638804027608849277489)
    ·
      refine ⟨17930729103020706636958117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23907638804027608849277489 17930729103020706636958117)
      ·
        refine ⟨3362011706816382494429647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17930729103020706636958117 3362011706816382494429647)
        ·
          refine ⟨5043017560224573741644471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362011706816382494429647 5043017560224573741644471)
          ·
            refine ⟨7564526340336860612466707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043017560224573741644471 7564526340336860612466707)
            ·
              refine ⟨11346789510505290918700061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564526340336860612466707 11346789510505290918700061)
              ·
                refine ⟨4255046066439484094512523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11346789510505290918700061 4255046066439484094512523)
                ·
                  refine ⟨6382569099659226141768785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255046066439484094512523 6382569099659226141768785)
                  ·
                    refine ⟨4786926824744419606326589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6382569099659226141768785 4786926824744419606326589)
                    ·
                      refine ⟨1795097559279157352372471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786926824744419606326589 1795097559279157352372471)
                      ·
                        rfl

theorem cell23_3495940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3495940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495940 prefixEnd_3495940 := by exact prefixLift 3495940
  have htrace : WordTrace (prefixWord ++ tailWord_3495940) baseStart_3495940 baseEnd_3495940 := by
    simpa [prefixWord, tailWord_3495940, baseEnd_3495940] using wordTrace_append hprefix tailTrace_3495940
  have hstable : (prefixWord ++ tailWord_3495940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495940).length < 2 ^ (prefixWord ++ tailWord_3495940).sum := by decide
  have hdescent : baseEnd_3495940 < baseStart_3495940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495952 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_3495952 : Nat := 118140960795 + 3495952 * 2 ^ 59
def prefixEnd_3495952 : Nat := 4983230072969 + 3 ^ 40 * 3495952 * 2
def baseEnd_3495952 : Nat := 598367907015670435140805

theorem tailTrace_3495952 : CollatzResearch.WordTrace tailWord_3495952 prefixEnd_3495952 598367907015670435140805 := by
  unfold tailWord_3495952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63753922315385219956125055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85005229753846959941500073 63753922315385219956125055)
  ·
    refine ⟨95630883473077829934187583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63753922315385219956125055 95630883473077829934187583)
    ·
      refine ⟨143446325209616744901281375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95630883473077829934187583 143446325209616744901281375)
      ·
        refine ⟨215169487814425117351922063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143446325209616744901281375 215169487814425117351922063)
        ·
          refine ⟨322754231721637676027883095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215169487814425117351922063 322754231721637676027883095)
          ·
            refine ⟨484131347582456514041824643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322754231721637676027883095 484131347582456514041824643)
            ·
              refine ⟨726197021373684771062736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484131347582456514041824643 726197021373684771062736965)
              ·
                refine ⟨136161941507565894574263181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726197021373684771062736965 136161941507565894574263181)
                ·
                  refine ⟨51060728065337210465348693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136161941507565894574263181 51060728065337210465348693)
                  ·
                    refine ⟨598367907015670435140805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51060728065337210465348693 598367907015670435140805)
                    ·
                      rfl

theorem cell23_3495952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_3495952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495952 prefixEnd_3495952 := by exact prefixLift 3495952
  have htrace : WordTrace (prefixWord ++ tailWord_3495952) baseStart_3495952 baseEnd_3495952 := by
    simpa [prefixWord, tailWord_3495952, baseEnd_3495952] using wordTrace_append hprefix tailTrace_3495952
  have hstable : (prefixWord ++ tailWord_3495952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495952).length < 2 ^ (prefixWord ++ tailWord_3495952).sum := by decide
  have hdescent : baseEnd_3495952 < baseStart_3495952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495970 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_3495970 : Nat := 118140960795 + 3495970 * 2 ^ 59
def prefixEnd_3495970 : Nat := 4983230072969 + 3 ^ 40 * 3495970 * 2
def baseEnd_3495970 : Nat := 1795112963698792234997333

theorem tailTrace_3495970 : CollatzResearch.WordTrace tailWord_3495970 prefixEnd_3495970 1795112963698792234997333 := by
  unfold tailWord_3495970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31877125286176307246601341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85005667429803485990936909 31877125286176307246601341)
  ·
    refine ⟨11953921982316115217475503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31877125286176307246601341 11953921982316115217475503)
    ·
      refine ⟨17930882973474172826213255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11953921982316115217475503 17930882973474172826213255)
      ·
        refine ⟨26896324460211259239319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930882973474172826213255 26896324460211259239319883)
        ·
          refine ⟨40344486690316888858979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896324460211259239319883 40344486690316888858979825)
          ·
            refine ⟨30258365017737666644234869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40344486690316888858979825 30258365017737666644234869)
            ·
              refine ⟨2836721720412906247897019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30258365017737666644234869 2836721720412906247897019)
              ·
                refine ⟨4255082580619359371845529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836721720412906247897019 4255082580619359371845529)
                ·
                  refine ⟨3191311935464519528884147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255082580619359371845529 3191311935464519528884147)
                  ·
                    refine ⟨4786967903196779293326221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191311935464519528884147 4786967903196779293326221)
                    ·
                      refine ⟨1795112963698792234997333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4786967903196779293326221 1795112963698792234997333)
                      ·
                        rfl

theorem cell23_3495970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_3495970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495970 prefixEnd_3495970 := by exact prefixLift 3495970
  have htrace : WordTrace (prefixWord ++ tailWord_3495970) baseStart_3495970 baseEnd_3495970 := by
    simpa [prefixWord, tailWord_3495970, baseEnd_3495970] using wordTrace_append hprefix tailTrace_3495970
  have hstable : (prefixWord ++ tailWord_3495970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495970).length < 2 ^ (prefixWord ++ tailWord_3495970).sum := by decide
  have hdescent : baseEnd_3495970 < baseStart_3495970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3495989 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3495989 : Nat := 118140960795 + 3495989 * 2 ^ 59
def prefixEnd_3495989 : Nat := 4983230072969 + 3 ^ 40 * 3495989 * 2
def baseEnd_3495989 : Nat := 1795122719831227660659745

theorem tailTrace_3495989 : CollatzResearch.WordTrace tailWord_3495989 prefixEnd_3495989 1795122719831227660659745 := by
  unfold tailWord_3495989
  simp only [CollatzResearch.WordTrace]
  refine ⟨127509194131636395231347021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85006129421090930154231347 127509194131636395231347021)
  ·
    refine ⟨47815947799363648211755133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127509194131636395231347021 47815947799363648211755133)
    ·
      refine ⟨17930980424761368079408175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47815947799363648211755133 17930980424761368079408175)
      ·
        refine ⟨26896470637142052119112263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17930980424761368079408175 26896470637142052119112263)
        ·
          refine ⟨40344705955713078178668395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896470637142052119112263 40344705955713078178668395)
          ·
            refine ⟨60517058933569617268002593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40344705955713078178668395 60517058933569617268002593)
            ·
              refine ⟨45387794200177212951001945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60517058933569617268002593 45387794200177212951001945)
              ·
                refine ⟨34040845650132909713251459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45387794200177212951001945 34040845650132909713251459)
                ·
                  refine ⟨51061268475199364569877189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34040845650132909713251459 51061268475199364569877189)
                  ·
                    refine ⟨9573987839099880856851973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51061268475199364569877189 9573987839099880856851973)
                    ·
                      refine ⟨1795122719831227660659745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9573987839099880856851973 1795122719831227660659745)
                      ·
                        rfl

theorem cell23_3495989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3495989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3495989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3495989 prefixEnd_3495989 := by exact prefixLift 3495989
  have htrace : WordTrace (prefixWord ++ tailWord_3495989) baseStart_3495989 baseEnd_3495989 := by
    simpa [prefixWord, tailWord_3495989, baseEnd_3495989] using wordTrace_append hprefix tailTrace_3495989
  have hstable : (prefixWord ++ tailWord_3495989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3495989).length < 2 ^ (prefixWord ++ tailWord_3495989).sum := by decide
  have hdescent : baseEnd_3495989 < baseStart_3495989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3495989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496039 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3496039 : Nat := 118140960795 + 3496039 * 2 ^ 59
def prefixEnd_3496039 : Nat := 4983230072969 + 3 ^ 40 * 3496039 * 2
def baseEnd_3496039 : Nat := 1795148393863952465034515

theorem tailTrace_3496039 : CollatzResearch.WordTrace tailWord_3496039 prefixEnd_3496039 1795148393863952465034515 := by
  unfold tailWord_3496039
  simp only [CollatzResearch.WordTrace]
  refine ⟨127511017781455253770667171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85007345187636835847111447 127511017781455253770667171)
  ·
    refine ⟨191266526672182880656000757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127511017781455253770667171 191266526672182880656000757)
    ·
      refine ⟨17931236875517145061500071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191266526672182880656000757 17931236875517145061500071)
      ·
        refine ⟨26896855313275717592250107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931236875517145061500071 26896855313275717592250107)
        ·
          refine ⟨40345282969913576388375161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26896855313275717592250107 40345282969913576388375161)
          ·
            refine ⟨30258962227435182291281371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40345282969913576388375161 30258962227435182291281371)
            ·
              refine ⟨45388443341152773436922057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30258962227435182291281371 45388443341152773436922057)
              ·
                refine ⟨34041332505864580077691543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45388443341152773436922057 34041332505864580077691543)
                ·
                  refine ⟨51061998758796870116537315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34041332505864580077691543 51061998758796870116537315)
                  ·
                    refine ⟨76592998138195305174805973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51061998758796870116537315 76592998138195305174805973)
                    ·
                      refine ⟨1795148393863952465034515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76592998138195305174805973 1795148393863952465034515)
                      ·
                        rfl

theorem cell23_3496039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3496039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496039 prefixEnd_3496039 := by exact prefixLift 3496039
  have htrace : WordTrace (prefixWord ++ tailWord_3496039) baseStart_3496039 baseEnd_3496039 := by
    simpa [prefixWord, tailWord_3496039, baseEnd_3496039] using wordTrace_append hprefix tailTrace_3496039
  have hstable : (prefixWord ++ tailWord_3496039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496039).length < 2 ^ (prefixWord ++ tailWord_3496039).sum := by decide
  have hdescent : baseEnd_3496039 < baseStart_3496039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496093 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_3496093 : Nat := 118140960795 + 3496093 * 2 ^ 59
def prefixEnd_3496093 : Nat := 4983230072969 + 3 ^ 40 * 3496093 * 2
def baseEnd_3496093 : Nat := 598392040606431751253089

theorem tailTrace_3496093 : CollatzResearch.WordTrace tailWord_3496093 prefixEnd_3496093 598392040606431751253089 := by
  unfold tailWord_3496093
  simp only [CollatzResearch.WordTrace]
  refine ⟨127512987323259620993132933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85008658215506413995421955 127512987323259620993132933)
  ·
    refine ⟨23908685123111178936212425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127512987323259620993132933 23908685123111178936212425)
    ·
      refine ⟨17931513842333384202159319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23908685123111178936212425 17931513842333384202159319)
      ·
        refine ⟨26897270763500076303238979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931513842333384202159319 26897270763500076303238979)
        ·
          refine ⟨40345906145250114454858469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26897270763500076303238979 40345906145250114454858469)
          ·
            refine ⟨7564857402234396460285963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40345906145250114454858469 7564857402234396460285963)
            ·
              refine ⟨11347286103351594690428945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564857402234396460285963 11347286103351594690428945)
              ·
                refine ⟨8510464577513696017821709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11347286103351594690428945 8510464577513696017821709)
                ·
                  refine ⟨3191424216567636006683141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8510464577513696017821709 3191424216567636006683141)
                  ·
                    refine ⟨598392040606431751253089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191424216567636006683141 598392040606431751253089)
                    ·
                      rfl

theorem cell23_3496093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_3496093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496093 prefixEnd_3496093 := by exact prefixLift 3496093
  have htrace : WordTrace (prefixWord ++ tailWord_3496093) baseStart_3496093 baseEnd_3496093 := by
    simpa [prefixWord, tailWord_3496093, baseEnd_3496093] using wordTrace_append hprefix tailTrace_3496093
  have hstable : (prefixWord ++ tailWord_3496093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496093).length < 2 ^ (prefixWord ++ tailWord_3496093).sum := by decide
  have hdescent : baseEnd_3496093 < baseStart_3496093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496100 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_3496100 : Nat := 118140960795 + 3496100 * 2 ^ 59
def prefixEnd_3496100 : Nat := 4983230072969 + 3 ^ 40 * 3496100 * 2
def baseEnd_3496100 : Nat := 1795179716183876726371735

theorem tailTrace_3496100 : CollatzResearch.WordTrace tailWord_3496100 prefixEnd_3496100 1795179716183876726371735 := by
  unfold tailWord_3496100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63756621317117130594318877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85008828422822840792425169 63756621317117130594318877)
  ·
    refine ⟨23908732993918923972869579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63756621317117130594318877 23908732993918923972869579)
    ·
      refine ⟨35863099490878385959304369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23908732993918923972869579 35863099490878385959304369)
      ·
        refine ⟨26897324618158789469478277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35863099490878385959304369 26897324618158789469478277)
        ·
          refine ⟨5043248365904773025527177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26897324618158789469478277 5043248365904773025527177)
          ·
            refine ⟨3782436274428579769145383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043248365904773025527177 3782436274428579769145383)
            ·
              refine ⟨5673654411642869653718075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782436274428579769145383 5673654411642869653718075)
              ·
                refine ⟨8510481617464304480577113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673654411642869653718075 8510481617464304480577113)
                ·
                  refine ⟨6382861213098228360432835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8510481617464304480577113 6382861213098228360432835)
                  ·
                    refine ⟨9574291819647342540649253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6382861213098228360432835 9574291819647342540649253)
                    ·
                      refine ⟨1795179716183876726371735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9574291819647342540649253 1795179716183876726371735)
                      ·
                        rfl

theorem cell23_3496100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_3496100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496100 prefixEnd_3496100 := by exact prefixLift 3496100
  have htrace : WordTrace (prefixWord ++ tailWord_3496100) baseStart_3496100 baseEnd_3496100 := by
    simpa [prefixWord, tailWord_3496100, baseEnd_3496100] using wordTrace_append hprefix tailTrace_3496100
  have hstable : (prefixWord ++ tailWord_3496100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496100).length < 2 ^ (prefixWord ++ tailWord_3496100).sum := by decide
  have hdescent : baseEnd_3496100 < baseStart_3496100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496133 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_3496133 : Nat := 118140960795 + 3496133 * 2 ^ 59
def prefixEnd_3496133 : Nat := 4983230072969 + 3 ^ 40 * 3496133 * 2
def baseEnd_3496133 : Nat := 1795196661045475097259083

theorem tailTrace_3496133 : CollatzResearch.WordTrace tailWord_3496133 prefixEnd_3496133 1795196661045475097259083 := by
  unfold tailWord_3496133
  simp only [CollatzResearch.WordTrace]
  refine ⟨127514446243114707824589053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85009630828743138549726035 127514446243114707824589053)
  ·
    refine ⟨47817917341168015434220895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127514446243114707824589053 47817917341168015434220895)
    ·
      refine ⟨71726876011752023151331343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47817917341168015434220895 71726876011752023151331343)
      ·
        refine ⟨107590314017628034726997015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71726876011752023151331343 107590314017628034726997015)
        ·
          refine ⟨161385471026442052090495523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107590314017628034726997015 161385471026442052090495523)
          ·
            refine ⟨242078206539663078135743285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161385471026442052090495523 242078206539663078135743285)
            ·
              refine ⟨22694831863093413575225933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242078206539663078135743285 22694831863093413575225933)
              ·
                refine ⟨8510561948660030090709725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22694831863093413575225933 8510561948660030090709725)
                ·
                  refine ⟨3191460730747511284016147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8510561948660030090709725 3191460730747511284016147)
                  ·
                    refine ⟨4787191096121266926024221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191460730747511284016147 4787191096121266926024221)
                    ·
                      refine ⟨1795196661045475097259083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787191096121266926024221 1795196661045475097259083)
                      ·
                        rfl

theorem cell23_3496133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_3496133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496133 prefixEnd_3496133 := by exact prefixLift 3496133
  have htrace : WordTrace (prefixWord ++ tailWord_3496133) baseStart_3496133 baseEnd_3496133 := by
    simpa [prefixWord, tailWord_3496133, baseEnd_3496133] using wordTrace_append hprefix tailTrace_3496133
  have hstable : (prefixWord ++ tailWord_3496133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496133).length < 2 ^ (prefixWord ++ tailWord_3496133).sum := by decide
  have hdescent : baseEnd_3496133 < baseStart_3496133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496186 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_3496186 : Nat := 118140960795 + 3496186 * 2 ^ 59
def prefixEnd_3496186 : Nat := 4983230072969 + 3 ^ 40 * 3496186 * 2
def baseEnd_3496186 : Nat := 1795223875520163389896339

theorem tailTrace_3496186 : CollatzResearch.WordTrace tailWord_3496186 prefixEnd_3496186 1795223875520163389896339 := by
  unfold tailWord_3496186
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879094827980674469067103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85010919541281798584178941 31879094827980674469067103)
  ·
    refine ⟨47818642241971011703600655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879094827980674469067103 47818642241971011703600655)
    ·
      refine ⟨71727963362956517555400983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47818642241971011703600655 71727963362956517555400983)
      ·
        refine ⟨107591945044434776333101475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71727963362956517555400983 107591945044434776333101475)
        ·
          refine ⟨161387917566652164499652213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107591945044434776333101475 161387917566652164499652213)
          ·
            refine ⟨15130117271873640421842395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161387917566652164499652213 15130117271873640421842395)
            ·
              refine ⟨22695175907810460632763593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130117271873640421842395 22695175907810460632763593)
              ·
                refine ⟨17021381930857845474572695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695175907810460632763593 17021381930857845474572695)
                ·
                  refine ⟨25532072896286768211859043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17021381930857845474572695 25532072896286768211859043)
                  ·
                    refine ⟨38298109344430152317788565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25532072896286768211859043 38298109344430152317788565)
                    ·
                      refine ⟨1795223875520163389896339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38298109344430152317788565 1795223875520163389896339)
                      ·
                        rfl

theorem cell23_3496186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_3496186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496186 prefixEnd_3496186 := by exact prefixLift 3496186
  have htrace : WordTrace (prefixWord ++ tailWord_3496186) baseStart_3496186 baseEnd_3496186 := by
    simpa [prefixWord, tailWord_3496186, baseEnd_3496186] using wordTrace_append hprefix tailTrace_3496186
  have hstable : (prefixWord ++ tailWord_3496186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496186).length < 2 ^ (prefixWord ++ tailWord_3496186).sum := by decide
  have hdescent : baseEnd_3496186 < baseStart_3496186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496193 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3496193 : Nat := 118140960795 + 3496193 * 2 ^ 59
def prefixEnd_3496193 : Nat := 4983230072969 + 3 ^ 40 * 3496193 * 2
def baseEnd_3496193 : Nat := 1795227469884744862508807

theorem tailTrace_3496193 : CollatzResearch.WordTrace tailWord_3496193 prefixEnd_3496193 1795227469884744862508807 := by
  unfold tailWord_3496193
  simp only [CollatzResearch.WordTrace]
  refine ⟨127516634622897338071773233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85011089748598225381182155 127516634622897338071773233)
  ·
    refine ⟨95637475967173003553829925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127516634622897338071773233 95637475967173003553829925)
    ·
      refine ⟨17932026743844938166343111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95637475967173003553829925 17932026743844938166343111)
      ·
        refine ⟨26898040115767407249514667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17932026743844938166343111 26898040115767407249514667)
        ·
          refine ⟨40347060173651110874272001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26898040115767407249514667 40347060173651110874272001)
          ·
            refine ⟨30260295130238333155704001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40347060173651110874272001 30260295130238333155704001)
            ·
              refine ⟨22695221347678749866778001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30260295130238333155704001 22695221347678749866778001)
              ·
                refine ⟨17021416010759062400083501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695221347678749866778001 17021416010759062400083501)
                ·
                  refine ⟨6383031004034648400031313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17021416010759062400083501 6383031004034648400031313)
                  ·
                    refine ⟨4787273253025986300023485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383031004034648400031313 4787273253025986300023485)
                    ·
                      refine ⟨1795227469884744862508807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787273253025986300023485 1795227469884744862508807)
                      ·
                        rfl

theorem cell23_3496193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3496193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496193 prefixEnd_3496193 := by exact prefixLift 3496193
  have htrace : WordTrace (prefixWord ++ tailWord_3496193) baseStart_3496193 baseEnd_3496193 := by
    simpa [prefixWord, tailWord_3496193, baseEnd_3496193] using wordTrace_append hprefix tailTrace_3496193
  have hstable : (prefixWord ++ tailWord_3496193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496193).length < 2 ^ (prefixWord ++ tailWord_3496193).sum := by decide
  have hdescent : baseEnd_3496193 < baseStart_3496193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496200 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_3496200 : Nat := 118140960795 + 3496200 * 2 ^ 59
def prefixEnd_3496200 : Nat := 4983230072969 + 3 ^ 40 * 3496200 * 2
def baseEnd_3496200 : Nat := 598410354749775445040425

theorem tailTrace_3496200 : CollatzResearch.WordTrace tailWord_3496200 prefixEnd_3496200 598410354749775445040425 := by
  unfold tailWord_3496200
  simp only [CollatzResearch.WordTrace]
  refine ⟨63758444966935989133639027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85011259955914652178185369 63758444966935989133639027)
  ·
    refine ⟨95637667450403983700458541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63758444966935989133639027 95637667450403983700458541)
    ·
      refine ⟨35864125293901493887671953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95637667450403983700458541 35864125293901493887671953)
      ·
        refine ⟨26898093970426120415753965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35864125293901493887671953 26898093970426120415753965)
        ·
          refine ⟨10086785238909795155907737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26898093970426120415753965 10086785238909795155907737)
          ·
            refine ⟨7565088929182346366930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10086785238909795155907737 7565088929182346366930803)
            ·
              refine ⟨11347633393773519550396205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7565088929182346366930803 11347633393773519550396205)
              ·
                refine ⟨4255362522665069831398577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11347633393773519550396205 4255362522665069831398577)
                ·
                  refine ⟨3191521891998802373548933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255362522665069831398577 3191521891998802373548933)
                  ·
                    refine ⟨598410354749775445040425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3191521891998802373548933 598410354749775445040425)
                    ·
                      rfl

theorem cell23_3496200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_3496200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496200 prefixEnd_3496200 := by exact prefixLift 3496200
  have htrace : WordTrace (prefixWord ++ tailWord_3496200) baseStart_3496200 baseEnd_3496200 := by
    simpa [prefixWord, tailWord_3496200, baseEnd_3496200] using wordTrace_append hprefix tailTrace_3496200
  have hstable : (prefixWord ++ tailWord_3496200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496200).length < 2 ^ (prefixWord ++ tailWord_3496200).sum := by decide
  have hdescent : baseEnd_3496200 < baseStart_3496200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496223 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3496223 : Nat := 118140960795 + 3496223 * 2 ^ 59
def prefixEnd_3496223 : Nat := 4983230072969 + 3 ^ 40 * 3496223 * 2
def baseEnd_3496223 : Nat := 1795242874304379745133669

theorem tailTrace_3496223 : CollatzResearch.WordTrace tailWord_3496223 prefixEnd_3496223 1795242874304379745133669 := by
  unfold tailWord_3496223
  simp only [CollatzResearch.WordTrace]
  refine ⟨127517728812788653195365323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85011819208525768796910215 127517728812788653195365323)
  ·
    refine ⟨191276593219182979793047985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127517728812788653195365323 191276593219182979793047985)
    ·
      refine ⟨143457444914387234844785989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191276593219182979793047985 143457444914387234844785989)
      ·
        refine ⟨26898270921447606533397373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143457444914387234844785989 26898270921447606533397373)
        ·
          refine ⟨10086851595542852450024015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26898270921447606533397373 10086851595542852450024015)
          ·
            refine ⟨15130277393314278675036023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10086851595542852450024015 15130277393314278675036023)
            ·
              refine ⟨22695416089971418012554035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130277393314278675036023 22695416089971418012554035)
              ·
                refine ⟨34043124134957127018831053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695416089971418012554035 34043124134957127018831053)
                ·
                  refine ⟨12766171550608922632061645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34043124134957127018831053 12766171550608922632061645)
                  ·
                    refine ⟨4787314331478345987023117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12766171550608922632061645 4787314331478345987023117)
                    ·
                      refine ⟨1795242874304379745133669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787314331478345987023117 1795242874304379745133669)
                      ·
                        rfl

theorem cell23_3496223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3496223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496223 prefixEnd_3496223 := by exact prefixLift 3496223
  have htrace : WordTrace (prefixWord ++ tailWord_3496223) baseStart_3496223 baseEnd_3496223 := by
    simpa [prefixWord, tailWord_3496223, baseEnd_3496223] using wordTrace_append hprefix tailTrace_3496223
  have hstable : (prefixWord ++ tailWord_3496223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496223).length < 2 ^ (prefixWord ++ tailWord_3496223).sum := by decide
  have hdescent : baseEnd_3496223 < baseStart_3496223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496236 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3496236 : Nat := 118140960795 + 3496236 * 2 ^ 59
def prefixEnd_3496236 : Nat := 4983230072969 + 3 ^ 40 * 3496236 * 2
def baseEnd_3496236 : Nat := 1795249549552888194271109

theorem tailTrace_3496236 : CollatzResearch.WordTrace tailWord_3496236 prefixEnd_3496236 1795249549552888194271109 := by
  unfold tailWord_3496236
  simp only [CollatzResearch.WordTrace]
  refine ⟨63759101480870778207794281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85012135307827704277059041 63759101480870778207794281)
  ·
    refine ⟨47819326110653083655845711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63759101480870778207794281 47819326110653083655845711)
    ·
      refine ⟨71728989165979625483768567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47819326110653083655845711 71728989165979625483768567)
      ·
        refine ⟨107593483748969438225652851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71728989165979625483768567 107593483748969438225652851)
        ·
          refine ⟨161390225623454157338479277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107593483748969438225652851 161390225623454157338479277)
          ·
            refine ⟨60521334608795309001929729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161390225623454157338479277 60521334608795309001929729)
            ·
              refine ⟨45391000956596481751447297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60521334608795309001929729 45391000956596481751447297)
              ·
                refine ⟨34043250717447361313585473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45391000956596481751447297 34043250717447361313585473)
                ·
                  refine ⟨25532438038085520985189105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34043250717447361313585473 25532438038085520985189105)
                  ·
                    refine ⟨19149328528564140738891829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25532438038085520985189105 19149328528564140738891829)
                    ·
                      refine ⟨1795249549552888194271109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19149328528564140738891829 1795249549552888194271109)
                      ·
                        rfl

theorem cell23_3496236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3496236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496236 prefixEnd_3496236 := by exact prefixLift 3496236
  have htrace : WordTrace (prefixWord ++ tailWord_3496236) baseStart_3496236 baseEnd_3496236 := by
    simpa [prefixWord, tailWord_3496236, baseEnd_3496236] using wordTrace_append hprefix tailTrace_3496236
  have hstable : (prefixWord ++ tailWord_3496236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496236).length < 2 ^ (prefixWord ++ tailWord_3496236).sum := by decide
  have hdescent : baseEnd_3496236 < baseStart_3496236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496250 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_3496250 : Nat := 118140960795 + 3496250 * 2 ^ 59
def prefixEnd_3496250 : Nat := 4983230072969 + 3 ^ 40 * 3496250 * 2
def baseEnd_3496250 : Nat := 1795256738282051139496045

theorem tailTrace_3496250 : CollatzResearch.WordTrace tailWord_3496250 prefixEnd_3496250 1795256738282051139496045 := by
  unfold tailWord_3496250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879678395922709201649551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85012475722460557871065469 31879678395922709201649551)
  ·
    refine ⟨47819517593884063802474327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31879678395922709201649551 47819517593884063802474327)
    ·
      refine ⟨71729276390826095703711491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47819517593884063802474327 71729276390826095703711491)
      ·
        refine ⟨107593914586239143555567237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71729276390826095703711491 107593914586239143555567237)
        ·
          refine ⟨20173858984919839416668857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107593914586239143555567237 20173858984919839416668857)
          ·
            refine ⟨15130394238689879562501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20173858984919839416668857 15130394238689879562501643)
            ·
              refine ⟨22695591358034819343752465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130394238689879562501643 22695591358034819343752465)
              ·
                refine ⟨17021693518526114507814349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695591358034819343752465 17021693518526114507814349)
                ·
                  refine ⟨6383135069447292940430381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17021693518526114507814349 6383135069447292940430381)
                  ·
                    refine ⟨2393675651042734852661393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6383135069447292940430381 2393675651042734852661393)
                    ·
                      refine ⟨1795256738282051139496045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393675651042734852661393 1795256738282051139496045)
                      ·
                        rfl

theorem cell23_3496250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_3496250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496250 prefixEnd_3496250 := by exact prefixLift 3496250
  have htrace : WordTrace (prefixWord ++ tailWord_3496250) baseStart_3496250 baseEnd_3496250 := by
    simpa [prefixWord, tailWord_3496250, baseEnd_3496250] using wordTrace_append hprefix tailTrace_3496250
  have hstable : (prefixWord ++ tailWord_3496250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496250).length < 2 ^ (prefixWord ++ tailWord_3496250).sum := by decide
  have hdescent : baseEnd_3496250 < baseStart_3496250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496257 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3496257 : Nat := 118140960795 + 3496257 * 2 ^ 59
def prefixEnd_3496257 : Nat := 4983230072969 + 3 ^ 40 * 3496257 * 2
def baseEnd_3496257 : Nat := 1795260332646632612108513

theorem tailTrace_3496257 : CollatzResearch.WordTrace tailWord_3496257 prefixEnd_3496257 1795260332646632612108513 := by
  unfold tailWord_3496257
  simp only [CollatzResearch.WordTrace]
  refine ⟨127518968894665477002103025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85012645929776984668068683 127518968894665477002103025)
  ·
    refine ⟨95639226670999107751577269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127518968894665477002103025 95639226670999107751577269)
    ·
      refine ⟨8966177500406166351710369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95639226670999107751577269 8966177500406166351710369)
      ·
        refine ⟨6724633125304624763782777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8966177500406166351710369 6724633125304624763782777)
        ·
          refine ⟨5043474843978468572837083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724633125304624763782777 5043474843978468572837083)
          ·
            refine ⟨7565212265967702859255625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043474843978468572837083 7565212265967702859255625)
            ·
              refine ⟨5673909199475777144441719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565212265967702859255625 5673909199475777144441719)
              ·
                refine ⟨8510863799213665716662579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5673909199475777144441719 8510863799213665716662579)
                ·
                  refine ⟨12766295698820498574993869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8510863799213665716662579 12766295698820498574993869)
                  ·
                    refine ⟨4787360887057686965622701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12766295698820498574993869 4787360887057686965622701)
                    ·
                      refine ⟨1795260332646632612108513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787360887057686965622701 1795260332646632612108513)
                      ·
                        rfl

theorem cell23_3496257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3496257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496257 prefixEnd_3496257 := by exact prefixLift 3496257
  have htrace : WordTrace (prefixWord ++ tailWord_3496257) baseStart_3496257 baseEnd_3496257 := by
    simpa [prefixWord, tailWord_3496257, baseEnd_3496257] using wordTrace_append hprefix tailTrace_3496257
  have hstable : (prefixWord ++ tailWord_3496257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496257).length < 2 ^ (prefixWord ++ tailWord_3496257).sum := by decide
  have hdescent : baseEnd_3496257 < baseStart_3496257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496293 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3496293 : Nat := 118140960795 + 3496293 * 2 ^ 59
def prefixEnd_3496293 : Nat := 4983230072969 + 3 ^ 40 * 3496293 * 2
def baseEnd_3496293 : Nat := 1795278817950194471258347

theorem tailTrace_3496293 : CollatzResearch.WordTrace tailWord_3496293 prefixEnd_3496293 1795278817950194471258347 := by
  unfold tailWord_3496293
  simp only [CollatzResearch.WordTrace]
  refine ⟨127520281922535055150413533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85013521281690036766942355 127520281922535055150413533)
  ·
    refine ⟨47820105720950645681405075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127520281922535055150413533 47820105720950645681405075)
    ·
      refine ⟨71730158581425968522107613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47820105720950645681405075 71730158581425968522107613)
      ·
        refine ⟨26898809468034738195790355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71730158581425968522107613 26898809468034738195790355)
        ·
          refine ⟨40348214202052107293685533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26898809468034738195790355 40348214202052107293685533)
          ·
            refine ⟨15130580325769540235132075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40348214202052107293685533 15130580325769540235132075)
            ·
              refine ⟨22695870488654310352698113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130580325769540235132075 22695870488654310352698113)
              ·
                refine ⟨17021902866490732764523585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22695870488654310352698113 17021902866490732764523585)
                ·
                  refine ⟨12766427149868049573392689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17021902866490732764523585 12766427149868049573392689)
                  ·
                    refine ⟨9574820362401037180044517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12766427149868049573392689 9574820362401037180044517)
                    ·
                      refine ⟨1795278817950194471258347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9574820362401037180044517 1795278817950194471258347)
                      ·
                        rfl

theorem cell23_3496293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3496293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496293 prefixEnd_3496293 := by exact prefixLift 3496293
  have htrace : WordTrace (prefixWord ++ tailWord_3496293) baseStart_3496293 baseEnd_3496293 := by
    simpa [prefixWord, tailWord_3496293, baseEnd_3496293] using wordTrace_append hprefix tailTrace_3496293
  have hstable : (prefixWord ++ tailWord_3496293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496293).length < 2 ^ (prefixWord ++ tailWord_3496293).sum := by decide
  have hdescent : baseEnd_3496293 < baseStart_3496293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496360 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3496360 : Nat := 118140960795 + 3496360 * 2 ^ 59
def prefixEnd_3496360 : Nat := 4983230072969 + 3 ^ 40 * 3496360 * 2
def baseEnd_3496360 : Nat := 1795313221154045709120539

theorem tailTrace_3496360 : CollatzResearch.WordTrace tailWord_3496360 prefixEnd_3496360 1795313221154045709120539 := by
  unfold tailWord_3496360
  simp only [CollatzResearch.WordTrace]
  refine ⟨63761362806646162796551267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85015150408861550395401689 63761362806646162796551267)
  ·
    refine ⟨95642044209969244194826901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63761362806646162796551267 95642044209969244194826901)
    ·
      refine ⟨4483220822342308321632511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95642044209969244194826901 4483220822342308321632511)
      ·
        refine ⟨6724831233513462482448767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483220822342308321632511 6724831233513462482448767)
        ·
          refine ⟨10087246850270193723673151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724831233513462482448767 10087246850270193723673151)
          ·
            refine ⟨15130870275405290585509727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087246850270193723673151 15130870275405290585509727)
            ·
              refine ⟨22696305413107935878264591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130870275405290585509727 22696305413107935878264591)
              ·
                refine ⟨34044458119661903817396887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22696305413107935878264591 34044458119661903817396887)
                ·
                  refine ⟨51066687179492855726095331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34044458119661903817396887 51066687179492855726095331)
                  ·
                    refine ⟨76600030769239283589142997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51066687179492855726095331 76600030769239283589142997)
                    ·
                      refine ⟨1795313221154045709120539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76600030769239283589142997 1795313221154045709120539)
                      ·
                        rfl

theorem cell23_3496360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3496360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496360 prefixEnd_3496360 := by exact prefixLift 3496360
  have htrace : WordTrace (prefixWord ++ tailWord_3496360) baseStart_3496360 baseEnd_3496360 := by
    simpa [prefixWord, tailWord_3496360, baseEnd_3496360] using wordTrace_append hprefix tailTrace_3496360
  have hstable : (prefixWord ++ tailWord_3496360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496360).length < 2 ^ (prefixWord ++ tailWord_3496360).sum := by decide
  have hdescent : baseEnd_3496360 < baseStart_3496360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496365 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3496365 : Nat := 118140960795 + 3496365 * 2 ^ 59
def prefixEnd_3496365 : Nat := 4983230072969 + 3 ^ 40 * 3496365 * 2
def baseEnd_3496365 : Nat := 1795315788557318189558017

theorem tailTrace_3496365 : CollatzResearch.WordTrace tailWord_3496365 prefixEnd_3496365 1795315788557318189558017 := by
  unfold tailWord_3496365
  simp only [CollatzResearch.WordTrace]
  refine ⟨127522907978274211447034549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85015271985516140964689699 127522907978274211447034549)
  ·
    refine ⟨11955272622963207323159489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127522907978274211447034549 11955272622963207323159489)
    ·
      refine ⟨8966454467222405492369617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955272622963207323159489 8966454467222405492369617)
      ·
        refine ⟨6724840850416804119277213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8966454467222405492369617 6724840850416804119277213)
        ·
          refine ⟨2521815318906301544728955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6724840850416804119277213 2521815318906301544728955)
          ·
            refine ⟨3782722978359452317093433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521815318906301544728955 3782722978359452317093433)
            ·
              refine ⟨2837042233769589237820075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3782722978359452317093433 2837042233769589237820075)
              ·
                refine ⟨4255563350654383856730113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837042233769589237820075 4255563350654383856730113)
                ·
                  refine ⟨3191672512990787892547585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4255563350654383856730113 3191672512990787892547585)
                  ·
                    refine ⟨2393754384743090919410689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3191672512990787892547585 2393754384743090919410689)
                    ·
                      refine ⟨1795315788557318189558017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393754384743090919410689 1795315788557318189558017)
                      ·
                        rfl

theorem cell23_3496365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3496365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496365 prefixEnd_3496365 := by exact prefixLift 3496365
  have htrace : WordTrace (prefixWord ++ tailWord_3496365) baseStart_3496365 baseEnd_3496365 := by
    simpa [prefixWord, tailWord_3496365, baseEnd_3496365] using wordTrace_append hprefix tailTrace_3496365
  have hstable : (prefixWord ++ tailWord_3496365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496365).length < 2 ^ (prefixWord ++ tailWord_3496365).sum := by decide
  have hdescent : baseEnd_3496365 < baseStart_3496365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496370 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_3496370 : Nat := 118140960795 + 3496370 * 2 ^ 59
def prefixEnd_3496370 : Nat := 4983230072969 + 3 ^ 40 * 3496370 * 2
def baseEnd_3496370 : Nat := 1795318355960590669995493

theorem tailTrace_3496370 : CollatzResearch.WordTrace tailWord_3496370 prefixEnd_3496370 1795318355960590669995493 := by
  unfold tailWord_3496370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31880772585814024325241641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85015393562170731533977709 31880772585814024325241641)
  ·
    refine ⟨23910579439360518243931231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31880772585814024325241641 23910579439360518243931231)
    ·
      refine ⟨35865869159040777365896847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23910579439360518243931231 35865869159040777365896847)
      ·
        refine ⟨53798803738561166048845271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35865869159040777365896847 53798803738561166048845271)
        ·
          refine ⟨80698205607841749073267907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53798803738561166048845271 80698205607841749073267907)
          ·
            refine ⟨121047308411762623609901861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80698205607841749073267907 121047308411762623609901861)
            ·
              refine ⟨22696370327205491926856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121047308411762623609901861 22696370327205491926856599)
              ·
                refine ⟨34044555490808237890284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22696370327205491926856599 34044555490808237890284899)
                ·
                  refine ⟨51066833236212356835427349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34044555490808237890284899 51066833236212356835427349)
                  ·
                    refine ⟨2393757807947454226660657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51066833236212356835427349 2393757807947454226660657)
                    ·
                      refine ⟨1795318355960590669995493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393757807947454226660657 1795318355960590669995493)
                      ·
                        rfl

theorem cell23_3496370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_3496370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496370 prefixEnd_3496370 := by exact prefixLift 3496370
  have htrace : WordTrace (prefixWord ++ tailWord_3496370) baseStart_3496370 baseEnd_3496370 := by
    simpa [prefixWord, tailWord_3496370, baseEnd_3496370] using wordTrace_append hprefix tailTrace_3496370
  have hstable : (prefixWord ++ tailWord_3496370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496370).length < 2 ^ (prefixWord ++ tailWord_3496370).sum := by decide
  have hdescent : baseEnd_3496370 < baseStart_3496370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3]
def baseStart_3496403 : Nat := 118140960795 + 3496403 * 2 ^ 59
def prefixEnd_3496403 : Nat := 4983230072969 + 3 ^ 40 * 3496403 * 2
def baseEnd_3496403 : Nat := 1795335300822189040882841

theorem tailTrace_3496403 : CollatzResearch.WordTrace tailWord_3496403 prefixEnd_3496403 1795335300822189040882841 := by
  unfold tailWord_3496403
  simp only [CollatzResearch.WordTrace]
  refine ⟨127524293952136543936917863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85016195968091029291278575 127524293952136543936917863)
  ·
    refine ⟨191286440928204815905376795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127524293952136543936917863 191286440928204815905376795)
    ·
      refine ⟨286929661392307223858065193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191286440928204815905376795 286929661392307223858065193)
      ·
        refine ⟨215197246044230417893548895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286929661392307223858065193 215197246044230417893548895)
        ·
          refine ⟨322795869066345626840323343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215197246044230417893548895 322795869066345626840323343)
          ·
            refine ⟨484193803599518440260485015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322795869066345626840323343 484193803599518440260485015)
            ·
              refine ⟨726290705399277660390727523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484193803599518440260485015 726290705399277660390727523)
              ·
                refine ⟨1089436058098916490586091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726290705399277660390727523 1089436058098916490586091285)
                ·
                  refine ⟨51067315223386710496223029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089436058098916490586091285 51067315223386710496223029)
                  ·
                    refine ⟨4787560802192504109020909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51067315223386710496223029 4787560802192504109020909)
                    ·
                      refine ⟨1795335300822189040882841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787560802192504109020909 1795335300822189040882841)
                      ·
                        rfl

theorem cell23_3496403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_3496403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496403 prefixEnd_3496403 := by exact prefixLift 3496403
  have htrace : WordTrace (prefixWord ++ tailWord_3496403) baseStart_3496403 baseEnd_3496403 := by
    simpa [prefixWord, tailWord_3496403, baseEnd_3496403] using wordTrace_append hprefix tailTrace_3496403
  have hstable : (prefixWord ++ tailWord_3496403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496403).length < 2 ^ (prefixWord ++ tailWord_3496403).sum := by decide
  have hdescent : baseEnd_3496403 < baseStart_3496403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496410 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 6]
def baseStart_3496410 : Nat := 118140960795 + 3496410 * 2 ^ 59
def prefixEnd_3496410 : Nat := 4983230072969 + 3 ^ 40 * 3496410 * 2
def baseEnd_3496410 : Nat := 199482099465196723721701

theorem tailTrace_3496410 : CollatzResearch.WordTrace tailWord_3496410 prefixEnd_3496410 199482099465196723721701 := by
  unfold tailWord_3496410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31881137315777796033105671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85016366175407456088281789 31881137315777796033105671)
  ·
    refine ⟨47821705973666694049658507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31881137315777796033105671 47821705973666694049658507)
    ·
      refine ⟨71732558960500041074487761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47821705973666694049658507 71732558960500041074487761)
      ·
        refine ⟨53799419220375030805865821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71732558960500041074487761 53799419220375030805865821)
        ·
          refine ⟨20174782207640636552199683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53799419220375030805865821 20174782207640636552199683)
          ·
            refine ⟨30262173311460954828299525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174782207640636552199683 30262173311460954828299525)
            ·
              refine ⟨5674157495898929030306161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30262173311460954828299525 5674157495898929030306161)
              ·
                refine ⟨4255618121924196772729621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674157495898929030306161 4255618121924196772729621)
                ·
                  refine ⟨199482099465196723721701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4255618121924196772729621 199482099465196723721701)
                  ·
                    rfl

theorem cell23_3496410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_3496410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496410 prefixEnd_3496410 := by exact prefixLift 3496410
  have htrace : WordTrace (prefixWord ++ tailWord_3496410) baseStart_3496410 baseEnd_3496410 := by
    simpa [prefixWord, tailWord_3496410, baseEnd_3496410] using wordTrace_append hprefix tailTrace_3496410
  have hstable : (prefixWord ++ tailWord_3496410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496410).length < 2 ^ (prefixWord ++ tailWord_3496410).sum := by decide
  have hdescent : baseEnd_3496410 < baseStart_3496410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496433 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3496433 : Nat := 118140960795 + 3496433 * 2 ^ 59
def prefixEnd_3496433 : Nat := 4983230072969 + 3 ^ 40 * 3496433 * 2
def baseEnd_3496433 : Nat := 1795350705241823923507703

theorem tailTrace_3496433 : CollatzResearch.WordTrace tailWord_3496433 prefixEnd_3496433 1795350705241823923507703 := by
  unfold tailWord_3496433
  simp only [CollatzResearch.WordTrace]
  refine ⟨127525388142027859060509953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85016925428018572707006635 127525388142027859060509953)
  ·
    refine ⟨95644041106520894295382465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127525388142027859060509953 95644041106520894295382465)
    ·
      refine ⟨71733030829890670721536849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95644041106520894295382465 71733030829890670721536849)
      ·
        refine ⟨53799773122418003041152637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71733030829890670721536849 53799773122418003041152637)
        ·
          refine ⟨20174914920906751140432239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53799773122418003041152637 20174914920906751140432239)
          ·
            refine ⟨30262372381360126710648359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20174914920906751140432239 30262372381360126710648359)
            ·
              refine ⟨45393558572040190065972539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30262372381360126710648359 45393558572040190065972539)
              ·
                refine ⟨68090337858060285098958809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45393558572040190065972539 68090337858060285098958809)
                ·
                  refine ⟨51067753393545213824219107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68090337858060285098958809 51067753393545213824219107)
                  ·
                    refine ⟨76601630090317820736328661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51067753393545213824219107 76601630090317820736328661)
                    ·
                      refine ⟨1795350705241823923507703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76601630090317820736328661 1795350705241823923507703)
                      ·
                        rfl

theorem cell23_3496433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3496433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496433 prefixEnd_3496433 := by exact prefixLift 3496433
  have htrace : WordTrace (prefixWord ++ tailWord_3496433) baseStart_3496433 baseEnd_3496433 := by
    simpa [prefixWord, tailWord_3496433, baseEnd_3496433] using wordTrace_append hprefix tailTrace_3496433
  have hstable : (prefixWord ++ tailWord_3496433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496433).length < 2 ^ (prefixWord ++ tailWord_3496433).sum := by decide
  have hdescent : baseEnd_3496433 < baseStart_3496433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496440 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_3496440 : Nat := 118140960795 + 3496440 * 2 ^ 59
def prefixEnd_3496440 : Nat := 4983230072969 + 3 ^ 40 * 3496440 * 2
def baseEnd_3496440 : Nat := 598451433202135132040057

theorem tailTrace_3496440 : CollatzResearch.WordTrace tailWord_3496440 prefixEnd_3496440 598451433202135132040057 := by
  unfold tailWord_3496440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63762821726501249628007387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85017095635334999504009849 63762821726501249628007387)
  ·
    refine ⟨95644232589751874442011081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63762821726501249628007387 95644232589751874442011081)
    ·
      refine ⟨71733174442313905831508311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95644232589751874442011081 71733174442313905831508311)
      ·
        refine ⟨107599761663470858747262467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71733174442313905831508311 107599761663470858747262467)
        ·
          refine ⟨161399642495206288120893701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107599761663470858747262467 161399642495206288120893701)
          ·
            refine ⟨30262432967851179022667569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161399642495206288120893701 30262432967851179022667569)
            ·
              refine ⟨22696824725888384267000677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30262432967851179022667569 22696824725888384267000677)
              ·
                refine ⟨4255654636104072050062627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22696824725888384267000677 4255654636104072050062627)
                ·
                  refine ⟨6383481954156108075093941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255654636104072050062627 6383481954156108075093941)
                  ·
                    refine ⟨598451433202135132040057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6383481954156108075093941 598451433202135132040057)
                    ·
                      rfl

theorem cell23_3496440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_3496440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496440 prefixEnd_3496440 := by exact prefixLift 3496440
  have htrace : WordTrace (prefixWord ++ tailWord_3496440) baseStart_3496440 baseEnd_3496440 := by
    simpa [prefixWord, tailWord_3496440, baseEnd_3496440] using wordTrace_append hprefix tailTrace_3496440
  have hstable : (prefixWord ++ tailWord_3496440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496440).length < 2 ^ (prefixWord ++ tailWord_3496440).sum := by decide
  have hdescent : baseEnd_3496440 < baseStart_3496440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496461 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3496461 : Nat := 118140960795 + 3496461 * 2 ^ 59
def prefixEnd_3496461 : Nat := 4983230072969 + 3 ^ 40 * 3496461 * 2
def baseEnd_3496461 : Nat := 199485009188905534884175

theorem tailTrace_3496461 : CollatzResearch.WordTrace tailWord_3496461 prefixEnd_3496461 199485009188905534884175 := by
  unfold tailWord_3496461
  simp only [CollatzResearch.WordTrace]
  refine ⟨127526409385926419842529237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85017606257284279895019491 127526409385926419842529237)
  ·
    refine ⟨2988900219982650465059279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127526409385926419842529237 2988900219982650465059279)
    ·
      refine ⟨4483350329973975697588919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988900219982650465059279 4483350329973975697588919)
      ·
        refine ⟨6725025494960963546383379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483350329973975697588919 6725025494960963546383379)
        ·
          refine ⟨10087538242441445319575069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725025494960963546383379 10087538242441445319575069)
          ·
            refine ⟨3782826840915541994840651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10087538242441445319575069 3782826840915541994840651)
            ·
              refine ⟨5674240261373312992260977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782826840915541994840651 5674240261373312992260977)
              ·
                refine ⟨4255680196029984744195733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674240261373312992260977 4255680196029984744195733)
                ·
                  refine ⟨199485009188905534884175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4255680196029984744195733 199485009188905534884175)
                  ·
                    rfl

theorem cell23_3496461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3496461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496461 prefixEnd_3496461 := by exact prefixLift 3496461
  have htrace : WordTrace (prefixWord ++ tailWord_3496461) baseStart_3496461 baseEnd_3496461 := by
    simpa [prefixWord, tailWord_3496461, baseEnd_3496461] using wordTrace_append hprefix tailTrace_3496461
  have hstable : (prefixWord ++ tailWord_3496461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496461).length < 2 ^ (prefixWord ++ tailWord_3496461).sum := by decide
  have hdescent : baseEnd_3496461 < baseStart_3496461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496471 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3496471 : Nat := 118140960795 + 3496471 * 2 ^ 59
def prefixEnd_3496471 : Nat := 4983230072969 + 3 ^ 40 * 3496471 * 2
def baseEnd_3496471 : Nat := 1795370217506694774832529

theorem tailTrace_3496471 : CollatzResearch.WordTrace tailWord_3496471 prefixEnd_3496471 1795370217506694774832529 := by
  unfold tailWord_3496471
  simp only [CollatzResearch.WordTrace]
  refine ⟨127526774115890191550393267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85017849410593461033595511 127526774115890191550393267)
  ·
    refine ⟨191290161173835287325589901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127526774115890191550393267 191290161173835287325589901)
    ·
      refine ⟨71733810440188232747096213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191290161173835287325589901 71733810440188232747096213)
      ·
        refine ⟨3362522364383823410020135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71733810440188232747096213 3362522364383823410020135)
        ·
          refine ⟨5043783546575735115030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362522364383823410020135 5043783546575735115030203)
          ·
            refine ⟨7565675319863602672545305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043783546575735115030203 7565675319863602672545305)
            ·
              refine ⟨5674256489897702004408979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7565675319863602672545305 5674256489897702004408979)
              ·
                refine ⟨8511384734846553006613469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674256489897702004408979 8511384734846553006613469)
                ·
                  refine ⟨3191769275567457377480051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8511384734846553006613469 3191769275567457377480051)
                  ·
                    refine ⟨4787653913351186066220077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191769275567457377480051 4787653913351186066220077)
                    ·
                      refine ⟨1795370217506694774832529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787653913351186066220077 1795370217506694774832529)
                      ·
                        rfl

theorem cell23_3496471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3496471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496471 prefixEnd_3496471 := by exact prefixLift 3496471
  have htrace : WordTrace (prefixWord ++ tailWord_3496471) baseStart_3496471 baseEnd_3496471 := by
    simpa [prefixWord, tailWord_3496471, baseEnd_3496471] using wordTrace_append hprefix tailTrace_3496471
  have hstable : (prefixWord ++ tailWord_3496471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496471).length < 2 ^ (prefixWord ++ tailWord_3496471).sum := by decide
  have hdescent : baseEnd_3496471 < baseStart_3496471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496473 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3496473 : Nat := 118140960795 + 3496473 * 2 ^ 59
def prefixEnd_3496473 : Nat := 4983230072969 + 3 ^ 40 * 3496473 * 2
def baseEnd_3496473 : Nat := 1795371244468003767007519

theorem tailTrace_3496473 : CollatzResearch.WordTrace tailWord_3496473 prefixEnd_3496473 1795371244468003767007519 := by
  unfold tailWord_3496473
  simp only [CollatzResearch.WordTrace]
  refine ⟨127526847061882945891966073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85017898041255297261310715 127526847061882945891966073)
  ·
    refine ⟨95645135296412209418974555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127526847061882945891966073 95645135296412209418974555)
    ·
      refine ⟨143467702944618314128461833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95645135296412209418974555 143467702944618314128461833)
      ·
        refine ⟨107600777208463735596346375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143467702944618314128461833 107600777208463735596346375)
        ·
          refine ⟨161401165812695603394519563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107600777208463735596346375 161401165812695603394519563)
          ·
            refine ⟨242101748719043405091779345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161401165812695603394519563 242101748719043405091779345)
            ·
              refine ⟨181576311539282553818834509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242101748719043405091779345 181576311539282553818834509)
              ·
                refine ⟨68091116827230957682062941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181576311539282553818834509 68091116827230957682062941)
                ·
                  refine ⟨25534168810211609130773603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68091116827230957682062941 25534168810211609130773603)
                  ·
                    refine ⟨38301253215317413696160405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25534168810211609130773603 38301253215317413696160405)
                    ·
                      refine ⟨1795371244468003767007519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38301253215317413696160405 1795371244468003767007519)
                      ·
                        rfl

theorem cell23_3496473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3496473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496473 prefixEnd_3496473 := by exact prefixLift 3496473
  have htrace : WordTrace (prefixWord ++ tailWord_3496473) baseStart_3496473 baseEnd_3496473 := by
    simpa [prefixWord, tailWord_3496473, baseEnd_3496473] using wordTrace_append hprefix tailTrace_3496473
  have hstable : (prefixWord ++ tailWord_3496473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496473).length < 2 ^ (prefixWord ++ tailWord_3496473).sum := by decide
  have hdescent : baseEnd_3496473 < baseStart_3496473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496497 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3496497 : Nat := 118140960795 + 3496497 * 2 ^ 59
def prefixEnd_3496497 : Nat := 4983230072969 + 3 ^ 40 * 3496497 * 2
def baseEnd_3496497 : Nat := 1795383568003711673107409

theorem tailTrace_3496497 : CollatzResearch.WordTrace tailWord_3496497 prefixEnd_3496497 1795383568003711673107409 := by
  unfold tailWord_3496497
  simp only [CollatzResearch.WordTrace]
  refine ⟨127527722413795997990839745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85018481609197331993893163 127527722413795997990839745)
  ·
    refine ⟨95645791810346998493129809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127527722413795997990839745 95645791810346998493129809)
    ·
      refine ⟨71734343857760248869847357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95645791810346998493129809 71734343857760248869847357)
      ·
        refine ⟨26900378946660093326192759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71734343857760248869847357 26900378946660093326192759)
        ·
          refine ⟨40350568419990139989289139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26900378946660093326192759 40350568419990139989289139)
          ·
            refine ⟨60525852629985209983933709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40350568419990139989289139 60525852629985209983933709)
            ·
              refine ⟨22697194736244453743975141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60525852629985209983933709 22697194736244453743975141)
              ·
                refine ⟨4255724013045835076995339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22697194736244453743975141 4255724013045835076995339)
                ·
                  refine ⟨6383586019568752615493009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4255724013045835076995339 6383586019568752615493009)
                  ·
                    refine ⟨4787689514676564461619757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6383586019568752615493009 4787689514676564461619757)
                    ·
                      refine ⟨1795383568003711673107409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787689514676564461619757 1795383568003711673107409)
                      ·
                        rfl

theorem cell23_3496497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3496497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496497 prefixEnd_3496497 := by exact prefixLift 3496497
  have htrace : WordTrace (prefixWord ++ tailWord_3496497) baseStart_3496497 baseEnd_3496497 := by
    simpa [prefixWord, tailWord_3496497, baseEnd_3496497] using wordTrace_append hprefix tailTrace_3496497
  have hstable : (prefixWord ++ tailWord_3496497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496497).length < 2 ^ (prefixWord ++ tailWord_3496497).sum := by decide
  have hdescent : baseEnd_3496497 < baseStart_3496497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496527 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_3496527 : Nat := 118140960795 + 3496527 * 2 ^ 59
def prefixEnd_3496527 : Nat := 4983230072969 + 3 ^ 40 * 3496527 * 2
def baseEnd_3496527 : Nat := 1795398972423346555732271

theorem tailTrace_3496527 : CollatzResearch.WordTrace tailWord_3496527 prefixEnd_3496527 1795398972423346555732271 := by
  unfold tailWord_3496527
  simp only [CollatzResearch.WordTrace]
  refine ⟨127528816603687313114431835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85019211069124875409621223 127528816603687313114431835)
  ·
    refine ⟨191293224905530969671647753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127528816603687313114431835 191293224905530969671647753)
    ·
      refine ⟨143469918679148227253735815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191293224905530969671647753 143469918679148227253735815)
      ·
        refine ⟨215204878018722340880603723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143469918679148227253735815 215204878018722340880603723)
        ·
          refine ⟨322807317028083511320905585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215204878018722340880603723 322807317028083511320905585)
          ·
            refine ⟨242105487771062633490679189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322807317028083511320905585 242105487771062633490679189)
            ·
              refine ⟨11348694739268560944875587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242105487771062633490679189 11348694739268560944875587)
              ·
                refine ⟨17023042108902841417313381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348694739268560944875587 17023042108902841417313381)
                ·
                  refine ⟨3191820395419282765746259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17023042108902841417313381 3191820395419282765746259)
                  ·
                    refine ⟨4787730593128924148619389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3191820395419282765746259 4787730593128924148619389)
                    ·
                      refine ⟨1795398972423346555732271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4787730593128924148619389 1795398972423346555732271)
                      ·
                        rfl

theorem cell23_3496527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_3496527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496527 prefixEnd_3496527 := by exact prefixLift 3496527
  have htrace : WordTrace (prefixWord ++ tailWord_3496527) baseStart_3496527 baseEnd_3496527 := by
    simpa [prefixWord, tailWord_3496527, baseEnd_3496527] using wordTrace_append hprefix tailTrace_3496527
  have hstable : (prefixWord ++ tailWord_3496527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496527).length < 2 ^ (prefixWord ++ tailWord_3496527).sum := by decide
  have hdescent : baseEnd_3496527 < baseStart_3496527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496530 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3496530 : Nat := 118140960795 + 3496530 * 2 ^ 59
def prefixEnd_3496530 : Nat := 4983230072969 + 3 ^ 40 * 3496530 * 2
def baseEnd_3496530 : Nat := 598466837621770014664919

theorem tailTrace_3496530 : CollatzResearch.WordTrace tailWord_3496530 prefixEnd_3496530 598466837621770014664919 := by
  unfold tailWord_3496530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31882231505669111156697761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85019284015117629751194029 31882231505669111156697761)
  ·
    refine ⟨23911673629251833367523321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31882231505669111156697761 23911673629251833367523321)
    ·
      refine ⟨17933755221938875025642491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23911673629251833367523321 17933755221938875025642491)
      ·
        refine ⟨26900632832908312538463737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933755221938875025642491 26900632832908312538463737)
        ·
          refine ⟨20175474624681234403847803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26900632832908312538463737 20175474624681234403847803)
          ·
            refine ⟨30263211937021851605771705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20175474624681234403847803 30263211937021851605771705)
            ·
              refine ⟨22697408952766388704328779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30263211937021851605771705 22697408952766388704328779)
              ·
                refine ⟨34046113429149583056493169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22697408952766388704328779 34046113429149583056493169)
                ·
                  refine ⟨25534585071862187292369877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34046113429149583056493169 25534585071862187292369877)
                  ·
                    refine ⟨598466837621770014664919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25534585071862187292369877 598466837621770014664919)
                    ·
                      rfl

theorem cell23_3496530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3496530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496530 prefixEnd_3496530 := by exact prefixLift 3496530
  have htrace : WordTrace (prefixWord ++ tailWord_3496530) baseStart_3496530 baseEnd_3496530 := by
    simpa [prefixWord, tailWord_3496530, baseEnd_3496530] using wordTrace_append hprefix tailTrace_3496530
  have hstable : (prefixWord ++ tailWord_3496530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496530).length < 2 ^ (prefixWord ++ tailWord_3496530).sum := by decide
  have hdescent : baseEnd_3496530 < baseStart_3496530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496554 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_3496554 : Nat := 118140960795 + 3496554 * 2 ^ 59
def prefixEnd_3496554 : Nat := 4983230072969 + 3 ^ 40 * 3496554 * 2
def baseEnd_3496554 : Nat := 1795412836401017950094647

theorem tailTrace_3496554 : CollatzResearch.WordTrace tailWord_3496554 prefixEnd_3496554 1795412836401017950094647 := by
  unfold tailWord_3496554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31882450343647374181416179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85019867583059664483776477 31882450343647374181416179)
  ·
    refine ⟨47823675515471061272124269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31882450343647374181416179 47823675515471061272124269)
    ·
      refine ⟨17933878318301647977046601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47823675515471061272124269 17933878318301647977046601)
      ·
        refine ⟨13450408738726235982784951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17933878318301647977046601 13450408738726235982784951)
        ·
          refine ⟨20175613108089353974177427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450408738726235982784951 20175613108089353974177427)
          ·
            refine ⟨30263419662134030961266141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20175613108089353974177427 30263419662134030961266141)
            ·
              refine ⟨11348782373300261610474803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30263419662134030961266141 11348782373300261610474803)
              ·
                refine ⟨17023173559950392415712205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11348782373300261610474803 17023173559950392415712205)
                ·
                  refine ⟨6383690084981397155892077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17023173559950392415712205 6383690084981397155892077)
                  ·
                    refine ⟨2393883781868023933459529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6383690084981397155892077 2393883781868023933459529)
                    ·
                      refine ⟨1795412836401017950094647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393883781868023933459529 1795412836401017950094647)
                      ·
                        rfl

theorem cell23_3496554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_3496554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496554 prefixEnd_3496554 := by exact prefixLift 3496554
  have htrace : WordTrace (prefixWord ++ tailWord_3496554) baseStart_3496554 baseEnd_3496554 := by
    simpa [prefixWord, tailWord_3496554, baseEnd_3496554] using wordTrace_append hprefix tailTrace_3496554
  have hstable : (prefixWord ++ tailWord_3496554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496554).length < 2 ^ (prefixWord ++ tailWord_3496554).sum := by decide
  have hdescent : baseEnd_3496554 < baseStart_3496554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496567 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_3496567 : Nat := 118140960795 + 3496567 * 2 ^ 59
def prefixEnd_3496567 : Nat := 4983230072969 + 3 ^ 40 * 3496567 * 2
def baseEnd_3496567 : Nat := 1795419511649526399232087

theorem tailTrace_3496567 : CollatzResearch.WordTrace tailWord_3496567 prefixEnd_3496567 1795419511649526399232087 := by
  unfold tailWord_3496567
  simp only [CollatzResearch.WordTrace]
  refine ⟨127530275523542399945887955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85020183682361599963925303 127530275523542399945887955)
  ·
    refine ⟨191295413285313599918831933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127530275523542399945887955 191295413285313599918831933)
    ·
      refine ⟨71735779981992599969561975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191295413285313599918831933 71735779981992599969561975)
      ·
        refine ⟨107603669972988899954342963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71735779981992599969561975 107603669972988899954342963)
        ·
          refine ⟨161405504959483349931514445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107603669972988899954342963 161405504959483349931514445)
          ·
            refine ⟨60527064359806256224317917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161405504959483349931514445 60527064359806256224317917)
            ·
              refine ⟨22697649134927346084119219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60527064359806256224317917 22697649134927346084119219)
              ·
                refine ⟨34046473702391019126178829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22697649134927346084119219 34046473702391019126178829)
                ·
                  refine ⟨12767427638396632172317061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34046473702391019126178829 12767427638396632172317061)
                  ·
                    refine ⟨2393892682199368532309449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12767427638396632172317061 2393892682199368532309449)
                    ·
                      refine ⟨1795419511649526399232087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2393892682199368532309449 1795419511649526399232087)
                      ·
                        rfl

theorem cell23_3496567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_3496567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496567 prefixEnd_3496567 := by exact prefixLift 3496567
  have htrace : WordTrace (prefixWord ++ tailWord_3496567) baseStart_3496567 baseEnd_3496567 := by
    simpa [prefixWord, tailWord_3496567, baseEnd_3496567] using wordTrace_append hprefix tailTrace_3496567
  have hstable : (prefixWord ++ tailWord_3496567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496567).length < 2 ^ (prefixWord ++ tailWord_3496567).sum := by decide
  have hdescent : baseEnd_3496567 < baseStart_3496567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496641 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 7]
def baseStart_3496641 : Nat := 118140960795 + 3496641 * 2 ^ 59
def prefixEnd_3496641 : Nat := 4983230072969 + 3 ^ 40 * 3496641 * 2
def baseEnd_3496641 : Nat := 199495278801995456634083

theorem tailTrace_3496641 : CollatzResearch.WordTrace tailWord_3496641 prefixEnd_3496641 199495278801995456634083 := by
  unfold tailWord_3496641
  simp only [CollatzResearch.WordTrace]
  refine ⟨127532974525274310584081777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85021983016849540389387851 127532974525274310584081777)
  ·
    refine ⟨95649730893955732938061333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127532974525274310584081777 95649730893955732938061333)
    ·
      refine ⟨4483581135654174981471625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95649730893955732938061333 4483581135654174981471625)
      ·
        refine ⟨3362685851740631236103719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4483581135654174981471625 3362685851740631236103719)
        ·
          refine ⟨5044028777610946854155579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362685851740631236103719 5044028777610946854155579)
          ·
            refine ⟨7566043166416420281233369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044028777610946854155579 7566043166416420281233369)
            ·
              refine ⟨5674532374812315210925027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566043166416420281233369 5674532374812315210925027)
              ·
                refine ⟨8511798562218472816387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674532374812315210925027 8511798562218472816387541)
                ·
                  refine ⟨199495278801995456634083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8511798562218472816387541 199495278801995456634083)
                  ·
                    rfl

theorem cell23_3496641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_3496641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496641 prefixEnd_3496641 := by exact prefixLift 3496641
  have htrace : WordTrace (prefixWord ++ tailWord_3496641) baseStart_3496641 baseEnd_3496641 := by
    simpa [prefixWord, tailWord_3496641, baseEnd_3496641] using wordTrace_append hprefix tailTrace_3496641
  have hstable : (prefixWord ++ tailWord_3496641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496641).length < 2 ^ (prefixWord ++ tailWord_3496641).sum := by decide
  have hdescent : baseEnd_3496641 < baseStart_3496641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496747 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4]
def baseStart_3496747 : Nat := 118140960795 + 3496747 * 2 ^ 59
def prefixEnd_3496747 : Nat := 4983230072969 + 3 ^ 40 * 3496747 * 2
def baseEnd_3496747 : Nat := 1795511938167335694981259

theorem tailTrace_3496747 : CollatzResearch.WordTrace tailWord_3496747 prefixEnd_3496747 1795511938167335694981259 := by
  unfold tailWord_3496747
  simp only [CollatzResearch.WordTrace]
  refine ⟨127536840662890290687440495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85024560441926860458293663 127536840662890290687440495)
  ·
    refine ⟨191305260994335436031160743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127536840662890290687440495 191305260994335436031160743)
    ·
      refine ⟨286957891491503154046741115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191305260994335436031160743 286957891491503154046741115)
      ·
        refine ⟨430436837237254731070111673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286957891491503154046741115 430436837237254731070111673)
        ·
          refine ⟨322827627927941048302583755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430436837237254731070111673 322827627927941048302583755)
          ·
            refine ⟨484241441891911572453875633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322827627927941048302583755 484241441891911572453875633)
            ·
              refine ⟨363181081418933679340406725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484241441891911572453875633 363181081418933679340406725)
              ·
                refine ⟨68096452766050064876326261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363181081418933679340406725 68096452766050064876326261)
                ·
                  refine ⟨6384042446817193582155587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68096452766050064876326261 6384042446817193582155587)
                  ·
                    refine ⟨9576063670225790373233381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384042446817193582155587 9576063670225790373233381)
                    ·
                      refine ⟨1795511938167335694981259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9576063670225790373233381 1795511938167335694981259)
                      ·
                        rfl

theorem cell23_3496747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 4].length) (baseStart_3496747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496747 prefixEnd_3496747 := by exact prefixLift 3496747
  have htrace : WordTrace (prefixWord ++ tailWord_3496747) baseStart_3496747 baseEnd_3496747 := by
    simpa [prefixWord, tailWord_3496747, baseEnd_3496747] using wordTrace_append hprefix tailTrace_3496747
  have hstable : (prefixWord ++ tailWord_3496747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496747).length < 2 ^ (prefixWord ++ tailWord_3496747).sum := by decide
  have hdescent : baseEnd_3496747 < baseStart_3496747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496764 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_3496764 : Nat := 118140960795 + 3496764 * 2 ^ 59
def prefixEnd_3496764 : Nat := 4983230072969 + 3 ^ 40 * 3496764 * 2
def baseEnd_3496764 : Nat := 1795520667338462128468681

theorem tailTrace_3496764 : CollatzResearch.WordTrace tailWord_3496764 prefixEnd_3496764 1795520667338462128468681 := by
  unfold tailWord_3496764
  simp only [CollatzResearch.WordTrace]
  refine ⟨63768730351914351295404673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85024973802552468393872897 63768730351914351295404673)
  ·
    refine ⟨47826547763935763471553505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63768730351914351295404673 47826547763935763471553505)
    ·
      refine ⟨35869910822951822603665129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47826547763935763471553505 35869910822951822603665129)
      ·
        refine ⟨26902433117213866952748847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35869910822951822603665129 26902433117213866952748847)
        ·
          refine ⟨40353649675820800429123271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26902433117213866952748847 40353649675820800429123271)
          ·
            refine ⟨60530474513731200643684907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40353649675820800429123271 60530474513731200643684907)
            ·
              refine ⟨90795711770596800965527361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60530474513731200643684907 90795711770596800965527361)
              ·
                refine ⟨68096783827947600724145521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90795711770596800965527361 68096783827947600724145521)
                ·
                  refine ⟨51072587870960700543109141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68096783827947600724145521 51072587870960700543109141)
                  ·
                    refine ⟨2394027556451282837958241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51072587870960700543109141 2394027556451282837958241)
                    ·
                      refine ⟨1795520667338462128468681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394027556451282837958241 1795520667338462128468681)
                      ·
                        rfl

theorem cell23_3496764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_3496764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496764 prefixEnd_3496764 := by exact prefixLift 3496764
  have htrace : WordTrace (prefixWord ++ tailWord_3496764) baseStart_3496764 baseEnd_3496764 := by
    simpa [prefixWord, tailWord_3496764, baseEnd_3496764] using wordTrace_append hprefix tailTrace_3496764
  have hstable : (prefixWord ++ tailWord_3496764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496764).length < 2 ^ (prefixWord ++ tailWord_3496764).sum := by decide
  have hdescent : baseEnd_3496764 < baseStart_3496764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496784 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_3496784 : Nat := 118140960795 + 3496784 * 2 ^ 59
def prefixEnd_3496784 : Nat := 4983230072969 + 3 ^ 40 * 3496784 * 2
def baseEnd_3496784 : Nat := 1795530936951552050218589

theorem tailTrace_3496784 : CollatzResearch.WordTrace tailWord_3496784 prefixEnd_3496784 1795530936951552050218589 := by
  unfold tailWord_3496784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63769095081878123003268703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85025460109170830671024937 63769095081878123003268703)
  ·
    refine ⟨95653642622817184504903055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63769095081878123003268703 95653642622817184504903055)
    ·
      refine ⟨143480463934225776757354583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95653642622817184504903055 143480463934225776757354583)
      ·
        refine ⟨215220695901338665136031875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143480463934225776757354583 215220695901338665136031875)
        ·
          refine ⟨322831043852007997704047813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215220695901338665136031875 322831043852007997704047813)
          ·
            refine ⟨60530820722251499569508965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322831043852007997704047813 60530820722251499569508965)
            ·
              refine ⟨11349528885422156169282931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60530820722251499569508965 11349528885422156169282931)
              ·
                refine ⟨17024293328133234253924397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11349528885422156169282931 17024293328133234253924397)
                ·
                  refine ⟨6384109998049962845221649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17024293328133234253924397 6384109998049962845221649)
                  ·
                    refine ⟨4788082498537472133916237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384109998049962845221649 4788082498537472133916237)
                    ·
                      refine ⟨1795530936951552050218589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788082498537472133916237 1795530936951552050218589)
                      ·
                        rfl

theorem cell23_3496784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_3496784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496784 prefixEnd_3496784 := by exact prefixLift 3496784
  have htrace : WordTrace (prefixWord ++ tailWord_3496784) baseStart_3496784 baseEnd_3496784 := by
    simpa [prefixWord, tailWord_3496784, baseEnd_3496784] using wordTrace_append hprefix tailTrace_3496784
  have hstable : (prefixWord ++ tailWord_3496784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496784).length < 2 ^ (prefixWord ++ tailWord_3496784).sum := by decide
  have hdescent : baseEnd_3496784 < baseStart_3496784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496785 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_3496785 : Nat := 118140960795 + 3496785 * 2 ^ 59
def prefixEnd_3496785 : Nat := 4983230072969 + 3 ^ 40 * 3496785 * 2
def baseEnd_3496785 : Nat := 1795531450432206546306085

theorem tailTrace_3496785 : CollatzResearch.WordTrace tailWord_3496785 prefixEnd_3496785 1795531450432206546306085 := by
  unfold tailWord_3496785
  simp only [CollatzResearch.WordTrace]
  refine ⟨127538226636752623177323809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85025484424501748784882539 127538226636752623177323809)
  ·
    refine ⟨95653669977564467382992857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127538226636752623177323809 95653669977564467382992857)
    ·
      refine ⟨71740252483173350537244643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95653669977564467382992857 71740252483173350537244643)
      ·
        refine ⟨107610378724760025805866965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71740252483173350537244643 107610378724760025805866965)
        ·
          refine ⟨2522118251361563104825007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 107610378724760025805866965 2522118251361563104825007)
          ·
            refine ⟨3783177377042344657237511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522118251361563104825007 3783177377042344657237511)
            ·
              refine ⟨5674766065563516985856267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783177377042344657237511 5674766065563516985856267)
              ·
                refine ⟨8512149098345275478784401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5674766065563516985856267 8512149098345275478784401)
                ·
                  refine ⟨6384111823758956609088301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8512149098345275478784401 6384111823758956609088301)
                  ·
                    refine ⟨2394041933909608728408113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6384111823758956609088301 2394041933909608728408113)
                    ·
                      refine ⟨1795531450432206546306085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394041933909608728408113 1795531450432206546306085)
                      ·
                        rfl

theorem cell23_3496785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_3496785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496785 prefixEnd_3496785 := by exact prefixLift 3496785
  have htrace : WordTrace (prefixWord ++ tailWord_3496785) baseStart_3496785 baseEnd_3496785 := by
    simpa [prefixWord, tailWord_3496785, baseEnd_3496785] using wordTrace_append hprefix tailTrace_3496785
  have hstable : (prefixWord ++ tailWord_3496785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496785).length < 2 ^ (prefixWord ++ tailWord_3496785).sum := by decide
  have hdescent : baseEnd_3496785 < baseStart_3496785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496794 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3496794 : Nat := 118140960795 + 3496794 * 2 ^ 59
def prefixEnd_3496794 : Nat := 4983230072969 + 3 ^ 40 * 3496794 * 2
def baseEnd_3496794 : Nat := 1795536071758097011093543

theorem tailTrace_3496794 : CollatzResearch.WordTrace tailWord_3496794 prefixEnd_3496794 1795536071758097011093543 := by
  unfold tailWord_3496794
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884638723430004428600359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85025703262480011809600957 31884638723430004428600359)
  ·
    refine ⟨47826958085145006642900539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31884638723430004428600359 47826958085145006642900539)
    ·
      refine ⟨71740437127717509964350809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47826958085145006642900539 71740437127717509964350809)
      ·
        refine ⟨53805327845788132473263107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71740437127717509964350809 53805327845788132473263107)
        ·
          refine ⟨80707991768682198709894661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53805327845788132473263107 80707991768682198709894661)
          ·
            refine ⟨15132748456627912258105249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80707991768682198709894661 15132748456627912258105249)
            ·
              refine ⟨11349561342470934193578937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15132748456627912258105249 11349561342470934193578937)
              ·
                refine ⟨8512171006853200645184203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11349561342470934193578937 8512171006853200645184203)
                ·
                  refine ⟨12768256510279800967776305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512171006853200645184203 12768256510279800967776305)
                  ·
                    refine ⟨9576192382709850725832229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12768256510279800967776305 9576192382709850725832229)
                    ·
                      refine ⟨1795536071758097011093543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9576192382709850725832229 1795536071758097011093543)
                      ·
                        rfl

theorem cell23_3496794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3496794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496794 prefixEnd_3496794 := by exact prefixLift 3496794
  have htrace : WordTrace (prefixWord ++ tailWord_3496794) baseStart_3496794 baseEnd_3496794 := by
    simpa [prefixWord, tailWord_3496794, baseEnd_3496794] using wordTrace_append hprefix tailTrace_3496794
  have hstable : (prefixWord ++ tailWord_3496794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496794).length < 2 ^ (prefixWord ++ tailWord_3496794).sum := by decide
  have hdescent : baseEnd_3496794 < baseStart_3496794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496808 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_3496808 : Nat := 118140960795 + 3496808 * 2 ^ 59
def prefixEnd_3496808 : Nat := 4983230072969 + 3 ^ 40 * 3496808 * 2
def baseEnd_3496808 : Nat := 598514420162419985439493

theorem tailTrace_3496808 : CollatzResearch.WordTrace tailWord_3496808 prefixEnd_3496808 598514420162419985439493 := by
  unfold tailWord_3496808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63769532757834649052705539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85026043677112865403607385 63769532757834649052705539)
  ·
    refine ⟨95654299136751973579058309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63769532757834649052705539 95654299136751973579058309)
    ·
      refine ⟨17935181088140995046073433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95654299136751973579058309 17935181088140995046073433)
      ·
        refine ⟨13451385816105746284555075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17935181088140995046073433 13451385816105746284555075)
        ·
          refine ⟨20177078724158619426832613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13451385816105746284555075 20177078724158619426832613)
          ·
            refine ⟨3783202260779741142531115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20177078724158619426832613 3783202260779741142531115)
            ·
              refine ⟨5674803391169611713796673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783202260779741142531115 5674803391169611713796673)
              ·
                refine ⟨4256102543377208785347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674803391169611713796673 4256102543377208785347505)
                ·
                  refine ⟨3192076907532906589010629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4256102543377208785347505 3192076907532906589010629)
                  ·
                    refine ⟨598514420162419985439493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192076907532906589010629 598514420162419985439493)
                    ·
                      rfl

theorem cell23_3496808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_3496808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496808 prefixEnd_3496808 := by exact prefixLift 3496808
  have htrace : WordTrace (prefixWord ++ tailWord_3496808) baseStart_3496808 baseEnd_3496808 := by
    simpa [prefixWord, tailWord_3496808, baseEnd_3496808] using wordTrace_append hprefix tailTrace_3496808
  have hstable : (prefixWord ++ tailWord_3496808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496808).length < 2 ^ (prefixWord ++ tailWord_3496808).sum := by decide
  have hdescent : baseEnd_3496808 < baseStart_3496808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496824 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_3496824 : Nat := 118140960795 + 3496824 * 2 ^ 59
def prefixEnd_3496824 : Nat := 4983230072969 + 3 ^ 40 * 3496824 * 2
def baseEnd_3496824 : Nat := 1795551476177731893718405

theorem tailTrace_3496824 : CollatzResearch.WordTrace tailWord_3496824 prefixEnd_3496824 1795551476177731893718405 := by
  unfold tailWord_3496824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63769824541805666418996763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85026432722407555225329017 63769824541805666418996763)
  ·
    refine ⟨95654736812708499628495145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63769824541805666418996763 95654736812708499628495145)
    ·
      refine ⟨71741052609531374721371359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95654736812708499628495145 71741052609531374721371359)
      ·
        refine ⟨107611578914297062082057039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71741052609531374721371359 107611578914297062082057039)
        ·
          refine ⟨161417368371445593123085559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107611578914297062082057039 161417368371445593123085559)
          ·
            refine ⟨242126052557168389684628339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161417368371445593123085559 242126052557168389684628339)
            ·
              refine ⟨363189078835752584526942509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242126052557168389684628339 363189078835752584526942509)
              ·
                refine ⟨136195904563407219197603441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363189078835752584526942509 136195904563407219197603441)
                ·
                  refine ⟨102146928422555414398202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136195904563407219197603441 102146928422555414398202581)
                  ·
                    refine ⟨2394068634903642524957873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102146928422555414398202581 2394068634903642524957873)
                    ·
                      refine ⟨1795551476177731893718405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394068634903642524957873 1795551476177731893718405)
                      ·
                        rfl

theorem cell23_3496824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_3496824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496824 prefixEnd_3496824 := by exact prefixLift 3496824
  have htrace : WordTrace (prefixWord ++ tailWord_3496824) baseStart_3496824 baseEnd_3496824 := by
    simpa [prefixWord, tailWord_3496824, baseEnd_3496824] using wordTrace_append hprefix tailTrace_3496824
  have hstable : (prefixWord ++ tailWord_3496824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496824).length < 2 ^ (prefixWord ++ tailWord_3496824).sum := by decide
  have hdescent : baseEnd_3496824 < baseStart_3496824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496831 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_3496831 : Nat := 118140960795 + 3496831 * 2 ^ 59
def prefixEnd_3496831 : Nat := 4983230072969 + 3 ^ 40 * 3496831 * 2
def baseEnd_3496831 : Nat := 1795555070542313366330873

theorem tailTrace_3496831 : CollatzResearch.WordTrace tailWord_3496831 prefixEnd_3496831 1795555070542313366330873 := by
  unfold tailWord_3496831
  simp only [CollatzResearch.WordTrace]
  refine ⟨127539904394585973033498347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85026602929723982022332231 127539904394585973033498347)
  ·
    refine ⟨191309856591878959550247521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127539904394585973033498347 191309856591878959550247521)
    ·
      refine ⟨143482392443909219662685641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191309856591878959550247521 143482392443909219662685641)
      ·
        refine ⟨107611794332931914747014231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143482392443909219662685641 107611794332931914747014231)
        ·
          refine ⟨161417691499397872120521347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107611794332931914747014231 161417691499397872120521347)
          ·
            refine ⟨242126537249096808180782021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161417691499397872120521347 242126537249096808180782021)
            ·
              refine ⟨45398725734205651533896629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242126537249096808180782021 45398725734205651533896629)
              ·
                refine ⟨4256130537581779831302809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45398725734205651533896629 4256130537581779831302809)
                ·
                  refine ⟨3192097903186334873477107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4256130537581779831302809 3192097903186334873477107)
                  ·
                    refine ⟨4788146854779502310215661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192097903186334873477107 4788146854779502310215661)
                    ·
                      refine ⟨1795555070542313366330873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788146854779502310215661 1795555070542313366330873)
                      ·
                        rfl

theorem cell23_3496831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_3496831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496831 prefixEnd_3496831 := by exact prefixLift 3496831
  have htrace : WordTrace (prefixWord ++ tailWord_3496831) baseStart_3496831 baseEnd_3496831 := by
    simpa [prefixWord, tailWord_3496831, baseEnd_3496831] using wordTrace_append hprefix tailTrace_3496831
  have hstable : (prefixWord ++ tailWord_3496831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496831).length < 2 ^ (prefixWord ++ tailWord_3496831).sum := by decide
  have hdescent : baseEnd_3496831 < baseStart_3496831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496886 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3496886 : Nat := 118140960795 + 3496886 * 2 ^ 59
def prefixEnd_3496886 : Nat := 4983230072969 + 3 ^ 40 * 3496886 * 2
def baseEnd_3496886 : Nat := 1795583311978310651143121

theorem tailTrace_3496886 : CollatzResearch.WordTrace tailWord_3496886 prefixEnd_3496886 1795583311978310651143121 := by
  unfold tailWord_3496886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971369400586669839171907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85027940272924478284500341 7971369400586669839171907)
  ·
    refine ⟨11957054100880004758757861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7971369400586669839171907 11957054100880004758757861)
    ·
      refine ⟨2241947643915000892267099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11957054100880004758757861 2241947643915000892267099)
      ·
        refine ⟨3362921465872501338400649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241947643915000892267099 3362921465872501338400649)
        ·
          refine ⟨2522191099404376003800487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362921465872501338400649 2522191099404376003800487)
          ·
            refine ⟨3783286649106564005700731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522191099404376003800487 3783286649106564005700731)
            ·
              refine ⟨5674929973659846008551097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3783286649106564005700731 5674929973659846008551097)
              ·
                refine ⟨4256197480244884506413323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5674929973659846008551097 4256197480244884506413323)
                ·
                  refine ⟨6384296220367326759619985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256197480244884506413323 6384296220367326759619985)
                  ·
                    refine ⟨4788222165275495069714989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384296220367326759619985 4788222165275495069714989)
                    ·
                      refine ⟨1795583311978310651143121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788222165275495069714989 1795583311978310651143121)
                      ·
                        rfl

theorem cell23_3496886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3496886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496886 prefixEnd_3496886 := by exact prefixLift 3496886
  have htrace : WordTrace (prefixWord ++ tailWord_3496886) baseStart_3496886 baseEnd_3496886 := by
    simpa [prefixWord, tailWord_3496886, baseEnd_3496886] using wordTrace_append hprefix tailTrace_3496886
  have hstable : (prefixWord ++ tailWord_3496886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496886).length < 2 ^ (prefixWord ++ tailWord_3496886).sum := by decide
  have hdescent : baseEnd_3496886 < baseStart_3496886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496894 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3496894 : Nat := 118140960795 + 3496894 * 2 ^ 59
def prefixEnd_3496894 : Nat := 4983230072969 + 3 ^ 40 * 3496894 * 2
def baseEnd_3496894 : Nat := 199509713313727402204787

theorem tailTrace_3496894 : CollatzResearch.WordTrace tailWord_3496894 prefixEnd_3496894 199509713313727402204787 := by
  unfold tailWord_3496894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942775274169716849130217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85028134795571823195361157 15942775274169716849130217)
  ·
    refine ⟨11957081455627287636847663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15942775274169716849130217 11957081455627287636847663)
    ·
      refine ⟨17935622183440931455271495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957081455627287636847663 17935622183440931455271495)
      ·
        refine ⟨26903433275161397182907243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935622183440931455271495 26903433275161397182907243)
        ·
          refine ⟨40355149912742095774360865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26903433275161397182907243 40355149912742095774360865)
          ·
            refine ⟨30266362434556571830770649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40355149912742095774360865 30266362434556571830770649)
            ·
              refine ⟨22699771825917428873077987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30266362434556571830770649 22699771825917428873077987)
              ·
                refine ⟨34049657738876143309616981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22699771825917428873077987 34049657738876143309616981)
                ·
                  refine ⟨199509713313727402204787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34049657738876143309616981 199509713313727402204787)
                  ·
                    rfl

theorem cell23_3496894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3496894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496894 prefixEnd_3496894 := by exact prefixLift 3496894
  have htrace : WordTrace (prefixWord ++ tailWord_3496894) baseStart_3496894 baseEnd_3496894 := by
    simpa [prefixWord, tailWord_3496894, baseEnd_3496894] using wordTrace_append hprefix tailTrace_3496894
  have hstable : (prefixWord ++ tailWord_3496894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496894).length < 2 ^ (prefixWord ++ tailWord_3496894).sum := by decide
  have hdescent : baseEnd_3496894 < baseStart_3496894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496931 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3496931 : Nat := 118140960795 + 3496931 * 2 ^ 59
def prefixEnd_3496931 : Nat := 4983230072969 + 3 ^ 40 * 3496931 * 2
def baseEnd_3496931 : Nat := 1795606418607762975080413

theorem tailTrace_3496931 : CollatzResearch.WordTrace tailWord_3496931 prefixEnd_3496931 1795606418607762975080413 := by
  unfold tailWord_3496931
  simp only [CollatzResearch.WordTrace]
  refine ⟨127543551694223690112138647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85029034462815793408092431 127543551694223690112138647)
  ·
    refine ⟨191315327541335535168207971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127543551694223690112138647 191315327541335535168207971)
    ·
      refine ⟨286972991312003302752311957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191315327541335535168207971 286972991312003302752311957)
      ·
        refine ⟨13451858967750154816514623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286972991312003302752311957 13451858967750154816514623)
        ·
          refine ⟨20177788451625232224771935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13451858967750154816514623 20177788451625232224771935)
          ·
            refine ⟨30266682677437848337157903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177788451625232224771935 30266682677437848337157903)
            ·
              refine ⟨45400024016156772505736855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30266682677437848337157903 45400024016156772505736855)
              ·
                refine ⟨68100036024235158758605283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45400024016156772505736855 68100036024235158758605283)
                ·
                  refine ⟨102150054036352738137907925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68100036024235158758605283 102150054036352738137907925)
                  ·
                    refine ⟨2394141891477017300107217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102150054036352738137907925 2394141891477017300107217)
                    ·
                      refine ⟨1795606418607762975080413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394141891477017300107217 1795606418607762975080413)
                      ·
                        rfl

theorem cell23_3496931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3496931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496931 prefixEnd_3496931 := by exact prefixLift 3496931
  have htrace : WordTrace (prefixWord ++ tailWord_3496931) baseStart_3496931 baseEnd_3496931 := by
    simpa [prefixWord, tailWord_3496931, baseEnd_3496931] using wordTrace_append hprefix tailTrace_3496931
  have hstable : (prefixWord ++ tailWord_3496931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496931).length < 2 ^ (prefixWord ++ tailWord_3496931).sum := by decide
  have hdescent : baseEnd_3496931 < baseStart_3496931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496944 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_3496944 : Nat := 118140960795 + 3496944 * 2 ^ 59
def prefixEnd_3496944 : Nat := 4983230072969 + 3 ^ 40 * 3496944 * 2
def baseEnd_3496944 : Nat := 1795613093856271424217853

theorem tailTrace_3496944 : CollatzResearch.WordTrace tailWord_3496944 prefixEnd_3496944 1795613093856271424217853 := by
  unfold tailWord_3496944
  simp only [CollatzResearch.WordTrace]
  refine ⟨63772012921588296666180943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85029350562117728888241257 63772012921588296666180943)
  ·
    refine ⟨95658019382382444999271415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63772012921588296666180943 95658019382382444999271415)
    ·
      refine ⟨143487029073573667498907123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95658019382382444999271415 143487029073573667498907123)
      ·
        refine ⟨215230543610360501248360685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143487029073573667498907123 215230543610360501248360685)
        ·
          refine ⟨80711453853885187968135257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215230543610360501248360685 80711453853885187968135257)
          ·
            refine ⟨60533590390413890976101443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80711453853885187968135257 60533590390413890976101443)
            ·
              refine ⟨90800385585620836464152165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60533590390413890976101443 90800385585620836464152165)
              ·
                refine ⟨17025072297303906837028531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90800385585620836464152165 17025072297303906837028531)
                ·
                  refine ⟨25537608445955860255542797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17025072297303906837028531 25537608445955860255542797)
                  ·
                    refine ⟨9576603167233447595828549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25537608445955860255542797 9576603167233447595828549)
                    ·
                      refine ⟨1795613093856271424217853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9576603167233447595828549 1795613093856271424217853)
                      ·
                        rfl

theorem cell23_3496944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_3496944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496944 prefixEnd_3496944 := by exact prefixLift 3496944
  have htrace : WordTrace (prefixWord ++ tailWord_3496944) baseStart_3496944 baseEnd_3496944 := by
    simpa [prefixWord, tailWord_3496944, baseEnd_3496944] using wordTrace_append hprefix tailTrace_3496944
  have hstable : (prefixWord ++ tailWord_3496944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496944).length < 2 ^ (prefixWord ++ tailWord_3496944).sum := by decide
  have hdescent : baseEnd_3496944 < baseStart_3496944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496958 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3496958 : Nat := 118140960795 + 3496958 * 2 ^ 59
def prefixEnd_3496958 : Nat := 4983230072969 + 3 ^ 40 * 3496958 * 2
def baseEnd_3496958 : Nat := 598540094195144789814263

theorem tailTrace_3496958 : CollatzResearch.WordTrace tailWord_3496958 prefixEnd_3496958 598540094195144789814263 := by
  unfold tailWord_3496958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943067058140734215421441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85029690976750582482247685 15943067058140734215421441)
  ·
    refine ⟨11957300293605550661566081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15943067058140734215421441 11957300293605550661566081)
    ·
      refine ⟨8967975220204162996174561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11957300293605550661566081 8967975220204162996174561)
      ·
        refine ⟨6725981415153122247130921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8967975220204162996174561 6725981415153122247130921)
        ·
          refine ⟨5044486061364841685348191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6725981415153122247130921 5044486061364841685348191)
          ·
            refine ⟨7566729092047262528022287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044486061364841685348191 7566729092047262528022287)
            ·
              refine ⟨11350093638070893792033431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566729092047262528022287 11350093638070893792033431)
              ·
                refine ⟨17025140457106340688050147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11350093638070893792033431 17025140457106340688050147)
                ·
                  refine ⟨25537710685659511032075221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17025140457106340688050147 25537710685659511032075221)
                  ·
                    refine ⟨598540094195144789814263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25537710685659511032075221 598540094195144789814263)
                    ·
                      rfl

theorem cell23_3496958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3496958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496958 prefixEnd_3496958 := by exact prefixLift 3496958
  have htrace : WordTrace (prefixWord ++ tailWord_3496958) baseStart_3496958 baseEnd_3496958 := by
    simpa [prefixWord, tailWord_3496958, baseEnd_3496958] using wordTrace_append hprefix tailTrace_3496958
  have hstable : (prefixWord ++ tailWord_3496958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496958).length < 2 ^ (prefixWord ++ tailWord_3496958).sum := by decide
  have hdescent : baseEnd_3496958 < baseStart_3496958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496961 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3496961 : Nat := 118140960795 + 3496961 * 2 ^ 59
def prefixEnd_3496961 : Nat := 4983230072969 + 3 ^ 40 * 3496961 * 2
def baseEnd_3496961 : Nat := 1795621823027397857705275

theorem tailTrace_3496961 : CollatzResearch.WordTrace tailWord_3496961 prefixEnd_3496961 1795621823027397857705275 := by
  unfold tailWord_3496961
  simp only [CollatzResearch.WordTrace]
  refine ⟨127544645884115005235730737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85029763922743336823820491 127544645884115005235730737)
  ·
    refine ⟨95658484413086253926798053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127544645884115005235730737 95658484413086253926798053)
    ·
      refine ⟨17935965827453672611274635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95658484413086253926798053 17935965827453672611274635)
      ·
        refine ⟨26903948741180508916911953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17935965827453672611274635 26903948741180508916911953)
        ·
          refine ⟨20177961555885381687683965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26903948741180508916911953 20177961555885381687683965)
          ·
            refine ⟨7566735583457018132881487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20177961555885381687683965 7566735583457018132881487)
            ·
              refine ⟨11350103375185527199322231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7566735583457018132881487 11350103375185527199322231)
              ·
                refine ⟨17025155062778290798983347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11350103375185527199322231 17025155062778290798983347)
                ·
                  refine ⟨25537732594167436198475021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17025155062778290798983347 25537732594167436198475021)
                  ·
                    refine ⟨9576649722812788574428133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25537732594167436198475021 9576649722812788574428133)
                    ·
                      refine ⟨1795621823027397857705275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9576649722812788574428133 1795621823027397857705275)
                      ·
                        rfl

theorem cell23_3496961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3496961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496961 prefixEnd_3496961 := by exact prefixLift 3496961
  have htrace : WordTrace (prefixWord ++ tailWord_3496961) baseStart_3496961 baseEnd_3496961 := by
    simpa [prefixWord, tailWord_3496961, baseEnd_3496961] using wordTrace_append hprefix tailTrace_3496961
  have hstable : (prefixWord ++ tailWord_3496961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496961).length < 2 ^ (prefixWord ++ tailWord_3496961).sum := by decide
  have hdescent : baseEnd_3496961 < baseStart_3496961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3496962 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3496962 : Nat := 118140960795 + 3496962 * 2 ^ 59
def prefixEnd_3496962 : Nat := 4983230072969 + 3 ^ 40 * 3496962 * 2
def baseEnd_3496962 : Nat := 199513592945339150421419

theorem tailTrace_3496962 : CollatzResearch.WordTrace tailWord_3496962 prefixEnd_3496962 199513592945339150421419 := by
  unfold tailWord_3496962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31886170589277845601629285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85029788238074254937678093 31886170589277845601629285)
  ·
    refine ⟨5978656985489596050305491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31886170589277845601629285 5978656985489596050305491)
    ·
      refine ⟨8967985478234394075458237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978656985489596050305491 8967985478234394075458237)
      ·
        refine ⟨3362994554337897778296839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8967985478234394075458237 3362994554337897778296839)
        ·
          refine ⟨5044491831506846667445259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362994554337897778296839 5044491831506846667445259)
          ·
            refine ⟨7566737747260270001167889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044491831506846667445259 7566737747260270001167889)
            ·
              refine ⟨5675053310445202500875917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7566737747260270001167889 5675053310445202500875917)
              ·
                refine ⟨2128144991416950937828469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675053310445202500875917 2128144991416950937828469)
                ·
                  refine ⟨199513592945339150421419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2128144991416950937828469 199513592945339150421419)
                  ·
                    rfl

theorem cell23_3496962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3496962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3496962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3496962 prefixEnd_3496962 := by exact prefixLift 3496962
  have htrace : WordTrace (prefixWord ++ tailWord_3496962) baseStart_3496962 baseEnd_3496962 := by
    simpa [prefixWord, tailWord_3496962, baseEnd_3496962] using wordTrace_append hprefix tailTrace_3496962
  have hstable : (prefixWord ++ tailWord_3496962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3496962).length < 2 ^ (prefixWord ++ tailWord_3496962).sum := by decide
  have hdescent : baseEnd_3496962 < baseStart_3496962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3496962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497004 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3497004 : Nat := 118140960795 + 3497004 * 2 ^ 59
def prefixEnd_3497004 : Nat := 4983230072969 + 3 ^ 40 * 3497004 * 2
def baseEnd_3497004 : Nat := 1795643902695541189467577

theorem tailTrace_3497004 : CollatzResearch.WordTrace tailWord_3497004 prefixEnd_3497004 1795643902695541189467577 := by
  unfold tailWord_3497004
  simp only [CollatzResearch.WordTrace]
  refine ⟨63773107111479611789773033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85030809481972815719697377 63773107111479611789773033)
  ·
    refine ⟨47829830333609708842329775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63773107111479611789773033 47829830333609708842329775)
    ·
      refine ⟨71744745500414563263494663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47829830333609708842329775 71744745500414563263494663)
      ·
        refine ⟨107617118250621844895241995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71744745500414563263494663 107617118250621844895241995)
        ·
          refine ⟨161425677375932767342862993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107617118250621844895241995 161425677375932767342862993)
          ·
            refine ⟨121069258031949575507147245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161425677375932767342862993 121069258031949575507147245)
            ·
              refine ⟨45400971761981090815180217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121069258031949575507147245 45400971761981090815180217)
              ·
                refine ⟨34050728821485818111385163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45400971761981090815180217 34050728821485818111385163)
                ·
                  refine ⟨51076093232228727167077745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34050728821485818111385163 51076093232228727167077745)
                  ·
                    refine ⟨38307069924171545375308309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51076093232228727167077745 38307069924171545375308309)
                    ·
                      refine ⟨1795643902695541189467577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38307069924171545375308309 1795643902695541189467577)
                      ·
                        rfl

theorem cell23_3497004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3497004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497004 prefixEnd_3497004 := by exact prefixLift 3497004
  have htrace : WordTrace (prefixWord ++ tailWord_3497004) baseStart_3497004 baseEnd_3497004 := by
    simpa [prefixWord, tailWord_3497004, baseEnd_3497004] using wordTrace_append hprefix tailTrace_3497004
  have hstable : (prefixWord ++ tailWord_3497004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497004).length < 2 ^ (prefixWord ++ tailWord_3497004).sum := by decide
  have hdescent : baseEnd_3497004 < baseStart_3497004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497022 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_3497022 : Nat := 118140960795 + 3497022 * 2 ^ 59
def prefixEnd_3497022 : Nat := 4983230072969 + 3 ^ 40 * 3497022 * 2
def baseEnd_3497022 : Nat := 598551048449107373014165

theorem tailTrace_3497022 : CollatzResearch.WordTrace tailWord_3497022 prefixEnd_3497022 598551048449107373014165 := by
  unfold tailWord_3497022
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943358842111751581712665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85031247157929341769134213 15943358842111751581712665)
  ·
    refine ⟨11957519131583813686284499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15943358842111751581712665 11957519131583813686284499)
    ·
      refine ⟨17936278697375720529426749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957519131583813686284499 17936278697375720529426749)
      ·
        refine ⟨6726104511515895198535031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17936278697375720529426749 6726104511515895198535031)
        ·
          refine ⟨10089156767273842797802547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726104511515895198535031 10089156767273842797802547)
          ·
            refine ⟨15133735150910764196703821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089156767273842797802547 15133735150910764196703821)
            ·
              refine ⟨5675150681591536573763933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15133735150910764196703821 5675150681591536573763933)
              ·
                refine ⟨2128181505596826215161475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5675150681591536573763933 2128181505596826215161475)
                ·
                  refine ⟨3192272258395239322742213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128181505596826215161475 3192272258395239322742213)
                  ·
                    refine ⟨598551048449107373014165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192272258395239322742213 598551048449107373014165)
                    ·
                      rfl

theorem cell23_3497022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_3497022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497022 prefixEnd_3497022 := by exact prefixLift 3497022
  have htrace : WordTrace (prefixWord ++ tailWord_3497022) baseStart_3497022 baseEnd_3497022 := by
    simpa [prefixWord, tailWord_3497022, baseEnd_3497022] using wordTrace_append hprefix tailTrace_3497022
  have hstable : (prefixWord ++ tailWord_3497022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497022).length < 2 ^ (prefixWord ++ tailWord_3497022).sum := by decide
  have hdescent : baseEnd_3497022 < baseStart_3497022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497061 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3497061 : Nat := 118140960795 + 3497061 * 2 ^ 59
def prefixEnd_3497061 : Nat := 4983230072969 + 3 ^ 40 * 3497061 * 2
def baseEnd_3497061 : Nat := 598557723697615822151605

theorem tailTrace_3497061 : CollatzResearch.WordTrace tailWord_3497061 prefixEnd_3497061 598557723697615822151605 := by
  unfold tailWord_3497061
  simp only [CollatzResearch.WordTrace]
  refine ⟨127548293183752722314371037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85032195455835148209580691 127548293183752722314371037)
  ·
    refine ⟨47830609943907270867889139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127548293183752722314371037 47830609943907270867889139)
    ·
      refine ⟨71745914915860906301833709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47830609943907270867889139 71745914915860906301833709)
      ·
        refine ⟨26904718093447839863187641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71745914915860906301833709 26904718093447839863187641)
        ·
          refine ⟨20178538570085879897390731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26904718093447839863187641 20178538570085879897390731)
          ·
            refine ⟨30267807855128819846086097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178538570085879897390731 30267807855128819846086097)
            ·
              refine ⟨22700855891346614884564573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30267807855128819846086097 22700855891346614884564573)
              ·
                refine ⟨8512820959254980581711715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22700855891346614884564573 8512820959254980581711715)
                ·
                  refine ⟨12769231438882470872567573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512820959254980581711715 12769231438882470872567573)
                  ·
                    refine ⟨598557723697615822151605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12769231438882470872567573 598557723697615822151605)
                    ·
                      rfl

theorem cell23_3497061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3497061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497061 prefixEnd_3497061 := by exact prefixLift 3497061
  have htrace : WordTrace (prefixWord ++ tailWord_3497061) baseStart_3497061 baseEnd_3497061 := by
    simpa [prefixWord, tailWord_3497061, baseEnd_3497061] using wordTrace_append hprefix tailTrace_3497061
  have hstable : (prefixWord ++ tailWord_3497061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497061).length < 2 ^ (prefixWord ++ tailWord_3497061).sum := by decide
  have hdescent : baseEnd_3497061 < baseStart_3497061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497078 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_3497078 : Nat := 118140960795 + 3497078 * 2 ^ 59
def prefixEnd_3497078 : Nat := 4983230072969 + 3 ^ 40 * 3497078 * 2
def baseEnd_3497078 : Nat := 598560633421324633314079

theorem tailTrace_3497078 : CollatzResearch.WordTrace tailWord_3497078 prefixEnd_3497078 598560633421324633314079 := by
  unfold tailWord_3497078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971807076543195888608743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85032608816460756145159925 7971807076543195888608743)
  ·
    refine ⟨11957710614814793832913115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7971807076543195888608743 11957710614814793832913115)
    ·
      refine ⟨17936565922222190749369673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11957710614814793832913115 17936565922222190749369673)
      ·
        refine ⟨13452424441666643062027255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17936565922222190749369673 13452424441666643062027255)
        ·
          refine ⟨20178636662499964593040883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13452424441666643062027255 20178636662499964593040883)
          ·
            refine ⟨30267954993749946889561325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178636662499964593040883 30267954993749946889561325)
            ·
              refine ⟨11350483122656230083585497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30267954993749946889561325 11350483122656230083585497)
              ·
                refine ⟨8512862341992172562689123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11350483122656230083585497 8512862341992172562689123)
                ·
                  refine ⟨12769293512988258844033685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8512862341992172562689123 12769293512988258844033685)
                  ·
                    refine ⟨598560633421324633314079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12769293512988258844033685 598560633421324633314079)
                    ·
                      rfl

theorem cell23_3497078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_3497078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497078 prefixEnd_3497078 := by exact prefixLift 3497078
  have htrace : WordTrace (prefixWord ++ tailWord_3497078) baseStart_3497078 baseEnd_3497078 := by
    simpa [prefixWord, tailWord_3497078, baseEnd_3497078] using wordTrace_append hprefix tailTrace_3497078
  have hstable : (prefixWord ++ tailWord_3497078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497078).length < 2 ^ (prefixWord ++ tailWord_3497078).sum := by decide
  have hdescent : baseEnd_3497078 < baseStart_3497078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497085 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_3497085 : Nat := 118140960795 + 3497085 * 2 ^ 59
def prefixEnd_3497085 : Nat := 4983230072969 + 3 ^ 40 * 3497085 * 2
def baseEnd_3497085 : Nat := 1795685494628555372554705

theorem tailTrace_3497085 : CollatzResearch.WordTrace tailWord_3497085 prefixEnd_3497085 1795685494628555372554705 := by
  unfold tailWord_3497085
  simp only [CollatzResearch.WordTrace]
  refine ⟨127549168535665774413244709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85032779023777182942163139 127549168535665774413244709)
  ·
    refine ⟨23915469100437332702483383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127549168535665774413244709 23915469100437332702483383)
    ·
      refine ⟨35873203650655999053725075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23915469100437332702483383 35873203650655999053725075)
      ·
        refine ⟨53809805475983998580587613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35873203650655999053725075 53809805475983998580587613)
        ·
          refine ⟨20178677053493999467720355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53809805475983998580587613 20178677053493999467720355)
          ·
            refine ⟨30268015580240999201580533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178677053493999467720355 30268015580240999201580533)
            ·
              refine ⟨2837626460647593675148175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30268015580240999201580533 2837626460647593675148175)
              ·
                refine ⟨4256439690971390512722263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837626460647593675148175 4256439690971390512722263)
                ·
                  refine ⟨6384659536457085769083395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256439690971390512722263 6384659536457085769083395)
                  ·
                    refine ⟨9576989304685628653625093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384659536457085769083395 9576989304685628653625093)
                    ·
                      refine ⟨1795685494628555372554705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9576989304685628653625093 1795685494628555372554705)
                      ·
                        rfl

theorem cell23_3497085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_3497085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497085 prefixEnd_3497085 := by exact prefixLift 3497085
  have htrace : WordTrace (prefixWord ++ tailWord_3497085) baseStart_3497085 baseEnd_3497085 := by
    simpa [prefixWord, tailWord_3497085, baseEnd_3497085] using wordTrace_append hprefix tailTrace_3497085
  have hstable : (prefixWord ++ tailWord_3497085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497085).length < 2 ^ (prefixWord ++ tailWord_3497085).sum := by decide
  have hdescent : baseEnd_3497085 < baseStart_3497085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497088 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_3497088 : Nat := 118140960795 + 3497088 * 2 ^ 59
def prefixEnd_3497088 : Nat := 4983230072969 + 3 ^ 40 * 3497088 * 2
def baseEnd_3497088 : Nat := 1795687035070518860817191

theorem tailTrace_3497088 : CollatzResearch.WordTrace tailWord_3497088 prefixEnd_3497088 1795687035070518860817191 := by
  unfold tailWord_3497088
  simp only [CollatzResearch.WordTrace]
  refine ⟨63774638977327452962801959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85032851969769937283735945 63774638977327452962801959)
  ·
    refine ⟨95661958465991179444202939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63774638977327452962801959 95661958465991179444202939)
    ·
      refine ⟨143492937698986769166304409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95661958465991179444202939 143492937698986769166304409)
      ·
        refine ⟨107619703274240076874728307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143492937698986769166304409 107619703274240076874728307)
        ·
          refine ⟨161429554911360115312092461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107619703274240076874728307 161429554911360115312092461)
          ·
            refine ⟨60536083091760043242034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161429554911360115312092461 60536083091760043242034673)
            ·
              refine ⟨45402062318820032431526005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60536083091760043242034673 45402062318820032431526005)
              ·
                refine ⟨4256443342389378040455563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45402062318820032431526005 4256443342389378040455563)
                ·
                  refine ⟨6384665013584067060683345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256443342389378040455563 6384665013584067060683345)
                  ·
                    refine ⟨4788498760188050295512509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6384665013584067060683345 4788498760188050295512509)
                    ·
                      refine ⟨1795687035070518860817191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788498760188050295512509 1795687035070518860817191)
                      ·
                        rfl

theorem cell23_3497088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_3497088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497088 prefixEnd_3497088 := by exact prefixLift 3497088
  have htrace : WordTrace (prefixWord ++ tailWord_3497088) baseStart_3497088 baseEnd_3497088 := by
    simpa [prefixWord, tailWord_3497088, baseEnd_3497088] using wordTrace_append hprefix tailTrace_3497088
  have hstable : (prefixWord ++ tailWord_3497088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497088).length < 2 ^ (prefixWord ++ tailWord_3497088).sum := by decide
  have hdescent : baseEnd_3497088 < baseStart_3497088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497096 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3497096 : Nat := 118140960795 + 3497096 * 2 ^ 59
def prefixEnd_3497096 : Nat := 4983230072969 + 3 ^ 40 * 3497096 * 2
def baseEnd_3497096 : Nat := 1795691142915754829517155

theorem tailTrace_3497096 : CollatzResearch.WordTrace tailWord_3497096 prefixEnd_3497096 1795691142915754829517155 := by
  unfold tailWord_3497096
  simp only [CollatzResearch.WordTrace]
  refine ⟨63774784869312961645947571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85033046492417282194596761 63774784869312961645947571)
  ·
    refine ⟨95662177303969442468921357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63774784869312961645947571 95662177303969442468921357)
    ·
      refine ⟨35873316488988540925845509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95662177303969442468921357 35873316488988540925845509)
      ·
        refine ⟨6726246841685351423596033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35873316488988540925845509 6726246841685351423596033)
        ·
          refine ⟨5044685131264013567697025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726246841685351423596033 5044685131264013567697025)
          ·
            refine ⟨3783513848448010175772769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5044685131264013567697025 3783513848448010175772769)
            ·
              refine ⟨2837635386336007631829577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783513848448010175772769 2837635386336007631829577)
              ·
                refine ⟨2128226539752005723872183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837635386336007631829577 2128226539752005723872183)
                ·
                  refine ⟨3192339809628008585808275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128226539752005723872183 3192339809628008585808275)
                  ·
                    refine ⟨4788509714442012878712413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192339809628008585808275 4788509714442012878712413)
                    ·
                      refine ⟨1795691142915754829517155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788509714442012878712413 1795691142915754829517155)
                      ·
                        rfl

theorem cell23_3497096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3497096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497096 prefixEnd_3497096 := by exact prefixLift 3497096
  have htrace : WordTrace (prefixWord ++ tailWord_3497096) baseStart_3497096 baseEnd_3497096 := by
    simpa [prefixWord, tailWord_3497096, baseEnd_3497096] using wordTrace_append hprefix tailTrace_3497096
  have hstable : (prefixWord ++ tailWord_3497096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497096).length < 2 ^ (prefixWord ++ tailWord_3497096).sum := by decide
  have hdescent : baseEnd_3497096 < baseStart_3497096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497121 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3497121 : Nat := 118140960795 + 3497121 * 2 ^ 59
def prefixEnd_3497121 : Nat := 4983230072969 + 3 ^ 40 * 3497121 * 2
def baseEnd_3497121 : Nat := 598567993310705743901513

theorem tailTrace_3497121 : CollatzResearch.WordTrace tailWord_3497121 prefixEnd_3497121 598567993310705743901513 := by
  unfold tailWord_3497121
  simp only [CollatzResearch.WordTrace]
  refine ⟨127550481563535352561555217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85033654375690235041036811 127550481563535352561555217)
  ·
    refine ⟨95662861172651514421166413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127550481563535352561555217 95662861172651514421166413)
    ·
      refine ⟨35873572939744317907937405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95662861172651514421166413 35873572939744317907937405)
      ·
        refine ⟨13452589852404119215476527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35873572939744317907937405 13452589852404119215476527)
        ·
          refine ⟨20178884778606178823214791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13452589852404119215476527 20178884778606178823214791)
          ·
            refine ⟨30268327167909268234822187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20178884778606178823214791 30268327167909268234822187)
            ·
              refine ⟨45402490751863902352233281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30268327167909268234822187 45402490751863902352233281)
              ·
                refine ⟨34051868063897926764174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45402490751863902352233281 34051868063897926764174961)
                ·
                  refine ⟨25538901047923445073131221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34051868063897926764174961 25538901047923445073131221)
                  ·
                    refine ⟨598567993310705743901513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25538901047923445073131221 598567993310705743901513)
                    ·
                      rfl

theorem cell23_3497121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3497121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497121 prefixEnd_3497121 := by exact prefixLift 3497121
  have htrace : WordTrace (prefixWord ++ tailWord_3497121) baseStart_3497121 baseEnd_3497121 := by
    simpa [prefixWord, tailWord_3497121, baseEnd_3497121] using wordTrace_append hprefix tailTrace_3497121
  have hstable : (prefixWord ++ tailWord_3497121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497121).length < 2 ^ (prefixWord ++ tailWord_3497121).sum := by decide
  have hdescent : baseEnd_3497121 < baseStart_3497121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497151 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 2, 6]
def baseStart_3497151 : Nat := 118140960795 + 3497151 * 2 ^ 59
def prefixEnd_3497151 : Nat := 4983230072969 + 3 ^ 40 * 3497151 * 2
def baseEnd_3497151 : Nat := 598573128117250704776467

theorem tailTrace_3497151 : CollatzResearch.WordTrace tailWord_3497151 prefixEnd_3497151 598573128117250704776467 := by
  unfold tailWord_3497151
  simp only [CollatzResearch.WordTrace]
  refine ⟨127551575753426667685147307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85034383835617778456764871 127551575753426667685147307)
  ·
    refine ⟨191327363630140001527720961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127551575753426667685147307 191327363630140001527720961)
    ·
      refine ⟨143495522722605001145790721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191327363630140001527720961 143495522722605001145790721)
      ·
        refine ⟨107621642041953750859343041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143495522722605001145790721 107621642041953750859343041)
        ·
          refine ⟨80716231531465313144507281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107621642041953750859343041 80716231531465313144507281)
          ·
            refine ⟨60537173648598984858380461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80716231531465313144507281 60537173648598984858380461)
            ·
              refine ⟨22701440118224619321892673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60537173648598984858380461 22701440118224619321892673)
              ·
                refine ⟨17026080088668464491419505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22701440118224619321892673 17026080088668464491419505)
                ·
                  refine ⟨12769560066501348368564629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17026080088668464491419505 12769560066501348368564629)
                  ·
                    refine ⟨598573128117250704776467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12769560066501348368564629 598573128117250704776467)
                    ·
                      rfl

theorem cell23_3497151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_3497151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497151 prefixEnd_3497151 := by exact prefixLift 3497151
  have htrace : WordTrace (prefixWord ++ tailWord_3497151) baseStart_3497151 baseEnd_3497151 := by
    simpa [prefixWord, tailWord_3497151, baseEnd_3497151] using wordTrace_append hprefix tailTrace_3497151
  have hstable : (prefixWord ++ tailWord_3497151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497151).length < 2 ^ (prefixWord ++ tailWord_3497151).sum := by decide
  have hdescent : baseEnd_3497151 < baseStart_3497151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497175 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_3497175 : Nat := 118140960795 + 3497175 * 2 ^ 59
def prefixEnd_3497175 : Nat := 4983230072969 + 3 ^ 40 * 3497175 * 2
def baseEnd_3497175 : Nat := 1795731707887460020429291

theorem tailTrace_3497175 : CollatzResearch.WordTrace tailWord_3497175 prefixEnd_3497175 1795731707887460020429291 := by
  unfold tailWord_3497175
  simp only [CollatzResearch.WordTrace]
  refine ⟨127552451105339719784020979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85034967403559813189347319 127552451105339719784020979)
  ·
    refine ⟨191328676658009579676031469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127552451105339719784020979 191328676658009579676031469)
    ·
      refine ⟨71748253746753592378511801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191328676658009579676031469 71748253746753592378511801)
      ·
        refine ⟨53811190310065194283883851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71748253746753592378511801 53811190310065194283883851)
        ·
          refine ⟨80716785465097791425825777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53811190310065194283883851 80716785465097791425825777)
          ·
            refine ⟨60537589098823343569369333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80716785465097791425825777 60537589098823343569369333)
            ·
              refine ⟨5675398978014688459628375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60537589098823343569369333 5675398978014688459628375)
              ·
                refine ⟨8513098467022032689442563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5675398978014688459628375 8513098467022032689442563)
                ·
                  refine ⟨12769647700533049034163845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513098467022032689442563 12769647700533049034163845)
                  ·
                    refine ⟨2394308943849946693905721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12769647700533049034163845 2394308943849946693905721)
                    ·
                      refine ⟨1795731707887460020429291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394308943849946693905721 1795731707887460020429291)
                      ·
                        rfl

theorem cell23_3497175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_3497175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497175 prefixEnd_3497175 := by exact prefixLift 3497175
  have htrace : WordTrace (prefixWord ++ tailWord_3497175) baseStart_3497175 baseEnd_3497175 := by
    simpa [prefixWord, tailWord_3497175, baseEnd_3497175] using wordTrace_append hprefix tailTrace_3497175
  have hstable : (prefixWord ++ tailWord_3497175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497175).length < 2 ^ (prefixWord ++ tailWord_3497175).sum := by decide
  have hdescent : baseEnd_3497175 < baseStart_3497175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497245 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_3497245 : Nat := 118140960795 + 3497245 * 2 ^ 59
def prefixEnd_3497245 : Nat := 4983230072969 + 3 ^ 40 * 3497245 * 2
def baseEnd_3497245 : Nat := 598589217177758248851323

theorem tailTrace_3497245 : CollatzResearch.WordTrace tailWord_3497245 prefixEnd_3497245 598589217177758248851323 := by
  unfold tailWord_3497245
  simp only [CollatzResearch.WordTrace]
  refine ⟨127555004215086121739069189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85036669476724081159379459 127555004215086121739069189)
  ·
    refine ⟨23916563290328647826075473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127555004215086121739069189 23916563290328647826075473)
    ·
      refine ⟨17937422467746485869556605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23916563290328647826075473 17937422467746485869556605)
      ·
        refine ⟨6726533425404932201083727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17937422467746485869556605 6726533425404932201083727)
        ·
          refine ⟨10089800138107398301625591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726533425404932201083727 10089800138107398301625591)
          ·
            refine ⟨15134700207161097452438387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089800138107398301625591 15134700207161097452438387)
            ·
              refine ⟨22702050310741646178657581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15134700207161097452438387 22702050310741646178657581)
              ·
                refine ⟨8513268866528117316996593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22702050310741646178657581 8513268866528117316996593)
                ·
                  refine ⟨6384951649896087987747445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8513268866528117316996593 6384951649896087987747445)
                  ·
                    refine ⟨598589217177758248851323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6384951649896087987747445 598589217177758248851323)
                    ·
                      rfl

theorem cell23_3497245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_3497245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497245 prefixEnd_3497245 := by exact prefixLift 3497245
  have htrace : WordTrace (prefixWord ++ tailWord_3497245) baseStart_3497245 baseEnd_3497245 := by
    simpa [prefixWord, tailWord_3497245, baseEnd_3497245] using wordTrace_append hprefix tailTrace_3497245
  have hstable : (prefixWord ++ tailWord_3497245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497245).length < 2 ^ (prefixWord ++ tailWord_3497245).sum := by decide
  have hdescent : baseEnd_3497245 < baseStart_3497245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497265 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3497265 : Nat := 118140960795 + 3497265 * 2 ^ 59
def prefixEnd_3497265 : Nat := 4983230072969 + 3 ^ 40 * 3497265 * 2
def baseEnd_3497265 : Nat := 1795777921146364668303877

theorem tailTrace_3497265 : CollatzResearch.WordTrace tailWord_3497265 prefixEnd_3497265 1795777921146364668303877 := by
  unfold tailWord_3497265
  simp only [CollatzResearch.WordTrace]
  refine ⟨127555733675013665154797249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85037155783342443436531499 127555733675013665154797249)
  ·
    refine ⟨95666800256260248866097937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127555733675013665154797249 95666800256260248866097937)
    ·
      refine ⟨71750100192195186649573453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95666800256260248866097937 71750100192195186649573453)
      ·
        refine ⟨26906287572073194993590045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71750100192195186649573453 26906287572073194993590045)
        ·
          refine ⟨10089857839527448122596267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26906287572073194993590045 10089857839527448122596267)
          ·
            refine ⟨15134786759291172183894401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089857839527448122596267 15134786759291172183894401)
            ·
              refine ⟨11351090069468379137920801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15134786759291172183894401 11351090069468379137920801)
              ·
                refine ⟨8513317552101284353440601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11351090069468379137920801 8513317552101284353440601)
                ·
                  refine ⟨6384988164075963265080451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8513317552101284353440601 6384988164075963265080451)
                  ·
                    refine ⟨9577482246113944897620677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6384988164075963265080451 9577482246113944897620677)
                    ·
                      refine ⟨1795777921146364668303877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9577482246113944897620677 1795777921146364668303877)
                      ·
                        rfl

theorem cell23_3497265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3497265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497265 prefixEnd_3497265 := by exact prefixLift 3497265
  have htrace : WordTrace (prefixWord ++ tailWord_3497265) baseStart_3497265 baseEnd_3497265 := by
    simpa [prefixWord, tailWord_3497265, baseEnd_3497265] using wordTrace_append hprefix tailTrace_3497265
  have hstable : (prefixWord ++ tailWord_3497265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497265).length < 2 ^ (prefixWord ++ tailWord_3497265).sum := by decide
  have hdescent : baseEnd_3497265 < baseStart_3497265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497352 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_3497352 : Nat := 118140960795 + 3497352 * 2 ^ 59
def prefixEnd_3497352 : Nat := 4983230072969 + 3 ^ 40 * 3497352 * 2
def baseEnd_3497352 : Nat := 598607531321101942638659

theorem tailTrace_3497352 : CollatzResearch.WordTrace tailWord_3497352 prefixEnd_3497352 598607531321101942638659 := by
  unfold tailWord_3497352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63779453412849239506607155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85039271217132319342142873 63779453412849239506607155)
  ·
    refine ⟨95669180119273859259910733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63779453412849239506607155 95669180119273859259910733)
    ·
      refine ⟨35875942544727697222466525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95669180119273859259910733 35875942544727697222466525)
      ·
        refine ⟨13453478454272886458424947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35875942544727697222466525 13453478454272886458424947)
        ·
          refine ⟨20180217681409329687637421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13453478454272886458424947 20180217681409329687637421)
          ·
            refine ⟨7567581630528498632864033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20180217681409329687637421 7567581630528498632864033)
            ·
              refine ⟨5675686222896373974648025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7567581630528498632864033 5675686222896373974648025)
              ·
                refine ⟨4256764667172280480986019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675686222896373974648025 4256764667172280480986019)
                ·
                  refine ⟨6385147000758420721479029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256764667172280480986019 6385147000758420721479029)
                  ·
                    refine ⟨598607531321101942638659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6385147000758420721479029 598607531321101942638659)
                    ·
                      rfl

theorem cell23_3497352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_3497352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497352 prefixEnd_3497352 := by exact prefixLift 3497352
  have htrace : WordTrace (prefixWord ++ tailWord_3497352) baseStart_3497352 baseEnd_3497352 := by
    simpa [prefixWord, tailWord_3497352, baseEnd_3497352] using wordTrace_append hprefix tailTrace_3497352
  have hstable : (prefixWord ++ tailWord_3497352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497352).length < 2 ^ (prefixWord ++ tailWord_3497352).sum := by decide
  have hdescent : baseEnd_3497352 < baseStart_3497352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497355 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 6, 2]
def baseStart_3497355 : Nat := 118140960795 + 3497355 * 2 ^ 59
def prefixEnd_3497355 : Nat := 4983230072969 + 3 ^ 40 * 3497355 * 2
def baseEnd_3497355 : Nat := 1795824134405269316178463

theorem tailTrace_3497355 : CollatzResearch.WordTrace tailWord_3497355 prefixEnd_3497355 1795824134405269316178463 := by
  unfold tailWord_3497355
  simp only [CollatzResearch.WordTrace]
  refine ⟨127559016244687610525573519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85039344163125073683715679 127559016244687610525573519)
  ·
    refine ⟨191338524367031415788360279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127559016244687610525573519 191338524367031415788360279)
    ·
      refine ⟨287007786550547123682540419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191338524367031415788360279 287007786550547123682540419)
      ·
        refine ⟨430511679825820685523810629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287007786550547123682540419 430511679825820685523810629)
        ·
          refine ⟨80720939967341378535714493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430511679825820685523810629 80720939967341378535714493)
          ·
            refine ⟨30270352487753016950892935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80720939967341378535714493 30270352487753016950892935)
            ·
              refine ⟨45405528731629525426339403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30270352487753016950892935 45405528731629525426339403)
              ·
                refine ⟨68108293097444288139509105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45405528731629525426339403 68108293097444288139509105)
                ·
                  refine ⟨51081219823083216104631829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68108293097444288139509105 51081219823083216104631829)
                  ·
                    refine ⟨2394432179207025754904617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51081219823083216104631829 2394432179207025754904617)
                    ·
                      refine ⟨1795824134405269316178463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394432179207025754904617 1795824134405269316178463)
                      ·
                        rfl

theorem cell23_3497355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 6, 2].length) (baseStart_3497355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497355 prefixEnd_3497355 := by exact prefixLift 3497355
  have htrace : WordTrace (prefixWord ++ tailWord_3497355) baseStart_3497355 baseEnd_3497355 := by
    simpa [prefixWord, tailWord_3497355, baseEnd_3497355] using wordTrace_append hprefix tailTrace_3497355
  have hstable : (prefixWord ++ tailWord_3497355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497355).length < 2 ^ (prefixWord ++ tailWord_3497355).sum := by decide
  have hdescent : baseEnd_3497355 < baseStart_3497355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497365 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3497365 : Nat := 118140960795 + 3497365 * 2 ^ 59
def prefixEnd_3497365 : Nat := 4983230072969 + 3 ^ 40 * 3497365 * 2
def baseEnd_3497365 : Nat := 598609756403938092351139

theorem tailTrace_3497365 : CollatzResearch.WordTrace tailWord_3497365 prefixEnd_3497365 598609756403938092351139 := by
  unfold tailWord_3497365
  simp only [CollatzResearch.WordTrace]
  refine ⟨127559380974651382233437549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85039587316434254822291699 127559380974651382233437549)
  ·
    refine ⟨47834767865494268337539081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127559380974651382233437549 47834767865494268337539081)
    ·
      refine ⟨35876075899120701253154311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47834767865494268337539081 35876075899120701253154311)
      ·
        refine ⟨53814113848681051879731467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35876075899120701253154311 53814113848681051879731467)
        ·
          refine ⟨80721170773021577819597201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53814113848681051879731467 80721170773021577819597201)
          ·
            refine ⟨60540878079766183364697901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80721170773021577819597201 60540878079766183364697901)
            ·
              refine ⟨22702829279912318761761713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60540878079766183364697901 22702829279912318761761713)
              ·
                refine ⟨17027121959934239071321285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22702829279912318761761713 17027121959934239071321285)
                ·
                  refine ⟨3192585367487669825872741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17027121959934239071321285 3192585367487669825872741)
                  ·
                    refine ⟨598609756403938092351139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3192585367487669825872741 598609756403938092351139)
                    ·
                      rfl

theorem cell23_3497365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3497365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497365 prefixEnd_3497365 := by exact prefixLift 3497365
  have htrace : WordTrace (prefixWord ++ tailWord_3497365) baseStart_3497365 baseEnd_3497365 := by
    simpa [prefixWord, tailWord_3497365, baseEnd_3497365] using wordTrace_append hprefix tailTrace_3497365
  have hstable : (prefixWord ++ tailWord_3497365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497365).length < 2 ^ (prefixWord ++ tailWord_3497365).sum := by decide
  have hdescent : baseEnd_3497365 < baseStart_3497365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497375 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3497375 : Nat := 118140960795 + 3497375 * 2 ^ 59
def prefixEnd_3497375 : Nat := 4983230072969 + 3 ^ 40 * 3497375 * 2
def baseEnd_3497375 : Nat := 1795834404018359237928371

theorem tailTrace_3497375 : CollatzResearch.WordTrace tailWord_3497375 prefixEnd_3497375 1795834404018359237928371 := by
  unfold tailWord_3497375
  simp only [CollatzResearch.WordTrace]
  refine ⟨127559745704615153941301579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85039830469743435960867719 127559745704615153941301579)
  ·
    refine ⟨191339618556922730911952369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127559745704615153941301579 191339618556922730911952369)
    ·
      refine ⟨143504713917692048183964277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191339618556922730911952369 143504713917692048183964277)
      ·
        refine ⟨13453566929783629517246651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143504713917692048183964277 13453566929783629517246651)
        ·
          refine ⟨20180350394675444275869977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13453566929783629517246651 20180350394675444275869977)
          ·
            refine ⟨15135262796006583206902483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20180350394675444275869977 15135262796006583206902483)
            ·
              refine ⟨22702894194009874810353725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15135262796006583206902483 22702894194009874810353725)
              ·
                refine ⟨8513585322753703053882647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22702894194009874810353725 8513585322753703053882647)
                ·
                  refine ⟨12770377984130554580823971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513585322753703053882647 12770377984130554580823971)
                  ·
                    refine ⟨19155566976195831871235957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12770377984130554580823971 19155566976195831871235957)
                    ·
                      refine ⟨1795834404018359237928371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19155566976195831871235957 1795834404018359237928371)
                      ·
                        rfl

theorem cell23_3497375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3497375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497375 prefixEnd_3497375 := by exact prefixLift 3497375
  have htrace : WordTrace (prefixWord ++ tailWord_3497375) baseStart_3497375 baseEnd_3497375 := by
    simpa [prefixWord, tailWord_3497375, baseEnd_3497375] using wordTrace_append hprefix tailTrace_3497375
  have hstable : (prefixWord ++ tailWord_3497375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497375).length < 2 ^ (prefixWord ++ tailWord_3497375).sum := by decide
  have hdescent : baseEnd_3497375 < baseStart_3497375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497422 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3497422 : Nat := 118140960795 + 3497422 * 2 ^ 59
def prefixEnd_3497422 : Nat := 4983230072969 + 3 ^ 40 * 3497422 * 2
def baseEnd_3497422 : Nat := 1795858537609120554040655

theorem tailTrace_3497422 : CollatzResearch.WordTrace tailWord_3497422 prefixEnd_3497422 1795858537609120554040655 := by
  unfold tailWord_3497422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945182491930610121032815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85040973290296587312175013 15945182491930610121032815)
  ·
    refine ⟨23917773737895915181549223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15945182491930610121032815 23917773737895915181549223)
    ·
      refine ⟨35876660606843872772323835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23917773737895915181549223 35876660606843872772323835)
      ·
        refine ⟨53814990910265809158485753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35876660606843872772323835 53814990910265809158485753)
        ·
          refine ⟨40361243182699356868864315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53814990910265809158485753 40361243182699356868864315)
          ·
            refine ⟨60541864774049035303296473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40361243182699356868864315 60541864774049035303296473)
            ·
              refine ⟨45406398580536776477472355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60541864774049035303296473 45406398580536776477472355)
              ·
                refine ⟨68109597870805164716208533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45406398580536776477472355 68109597870805164716208533)
                ·
                  refine ⟨3192637400193992096072275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68109597870805164716208533 3192637400193992096072275)
                  ·
                    refine ⟨4788956100290988144108413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192637400193992096072275 4788956100290988144108413)
                    ·
                      refine ⟨1795858537609120554040655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788956100290988144108413 1795858537609120554040655)
                      ·
                        rfl

theorem cell23_3497422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3497422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497422 prefixEnd_3497422 := by exact prefixLift 3497422
  have htrace : WordTrace (prefixWord ++ tailWord_3497422) baseStart_3497422 baseEnd_3497422 := by
    simpa [prefixWord, tailWord_3497422, baseEnd_3497422] using wordTrace_append hprefix tailTrace_3497422
  have hstable : (prefixWord ++ tailWord_3497422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497422).length < 2 ^ (prefixWord ++ tailWord_3497422).sum := by decide
  have hdescent : baseEnd_3497422 < baseStart_3497422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497439 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_3497439 : Nat := 118140960795 + 3497439 * 2 ^ 59
def prefixEnd_3497439 : Nat := 4983230072969 + 3 ^ 40 * 3497439 * 2
def baseEnd_3497439 : Nat := 1795867266780246987528077

theorem tailTrace_3497439 : CollatzResearch.WordTrace tailWord_3497439 prefixEnd_3497439 1795867266780246987528077 := by
  unfold tailWord_3497439
  simp only [CollatzResearch.WordTrace]
  refine ⟨127562079976383292871631371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85041386650922195247754247 127562079976383292871631371)
  ·
    refine ⟨191343119964574939307447057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127562079976383292871631371 191343119964574939307447057)
    ·
      refine ⟨143507339973431204480585293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191343119964574939307447057 143507339973431204480585293)
      ·
        refine ⟨53815252490036701680219485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143507339973431204480585293 53815252490036701680219485)
        ·
          refine ⟨20180719683763763130082307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53815252490036701680219485 20180719683763763130082307)
          ·
            refine ⟨30271079525645644695123461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20180719683763763130082307 30271079525645644695123461)
            ·
              refine ⟨5675827411058558380335649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30271079525645644695123461 5675827411058558380335649)
              ·
                refine ⟨4256870558293918785251737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5675827411058558380335649 4256870558293918785251737)
                ·
                  refine ⟨3192652918720439088938803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4256870558293918785251737 3192652918720439088938803)
                  ·
                    refine ⟨4788979378080658633408205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192652918720439088938803 4788979378080658633408205)
                    ·
                      refine ⟨1795867266780246987528077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4788979378080658633408205 1795867266780246987528077)
                      ·
                        rfl

theorem cell23_3497439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_3497439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497439 prefixEnd_3497439 := by exact prefixLift 3497439
  have htrace : WordTrace (prefixWord ++ tailWord_3497439) baseStart_3497439 baseEnd_3497439 := by
    simpa [prefixWord, tailWord_3497439, baseEnd_3497439] using wordTrace_append hprefix tailTrace_3497439
  have hstable : (prefixWord ++ tailWord_3497439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497439).length < 2 ^ (prefixWord ++ tailWord_3497439).sum := by decide
  have hdescent : baseEnd_3497439 < baseStart_3497439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497465 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3497465 : Nat := 118140960795 + 3497465 * 2 ^ 59
def prefixEnd_3497465 : Nat := 4983230072969 + 3 ^ 40 * 3497465 * 2
def baseEnd_3497465 : Nat := 1795880617277263885802957

theorem tailTrace_3497465 : CollatzResearch.WordTrace tailWord_3497465 prefixEnd_3497465 1795880617277263885802957 := by
  unfold tailWord_3497465
  simp only [CollatzResearch.WordTrace]
  refine ⟨127563028274289099312077849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85042018849526066208051899 127563028274289099312077849)
  ·
    refine ⟨95672271205716824484058387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127563028274289099312077849 95672271205716824484058387)
    ·
      refine ⟨143508406808575236726087581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95672271205716824484058387 143508406808575236726087581)
      ·
        refine ⟨53815652553215713772282843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143508406808575236726087581 53815652553215713772282843)
        ·
          refine ⟨80723478829823570658424265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53815652553215713772282843 80723478829823570658424265)
          ·
            refine ⟨60542609122367677993818199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80723478829823570658424265 60542609122367677993818199)
            ·
              refine ⟨90813913683551516990727299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60542609122367677993818199 90813913683551516990727299)
              ·
                refine ⟨136220870525327275486090949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90813913683551516990727299 136220870525327275486090949)
                ·
                  refine ⟨25541413223498864153642053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136220870525327275486090949 25541413223498864153642053)
                  ·
                    refine ⟨4789014979406037028807885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25541413223498864153642053 4789014979406037028807885)
                    ·
                      refine ⟨1795880617277263885802957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4789014979406037028807885 1795880617277263885802957)
                      ·
                        rfl

theorem cell23_3497465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3497465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497465 prefixEnd_3497465 := by exact prefixLift 3497465
  have htrace : WordTrace (prefixWord ++ tailWord_3497465) baseStart_3497465 baseEnd_3497465 := by
    simpa [prefixWord, tailWord_3497465, baseEnd_3497465] using wordTrace_append hprefix tailTrace_3497465
  have hstable : (prefixWord ++ tailWord_3497465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497465).length < 2 ^ (prefixWord ++ tailWord_3497465).sum := by decide
  have hdescent : baseEnd_3497465 < baseStart_3497465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497479 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3497479 : Nat := 118140960795 + 3497479 * 2 ^ 59
def prefixEnd_3497479 : Nat := 4983230072969 + 3 ^ 40 * 3497479 * 2
def baseEnd_3497479 : Nat := 1795887806006426831027893

theorem tailTrace_3497479 : CollatzResearch.WordTrace tailWord_3497479 prefixEnd_3497479 1795887806006426831027893 := by
  unfold tailWord_3497479
  simp only [CollatzResearch.WordTrace]
  refine ⟨127563538896238379703087491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85042359264158919802058327 127563538896238379703087491)
  ·
    refine ⟨191345308344357569554631237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127563538896238379703087491 191345308344357569554631237)
    ·
      refine ⟨35877245314567044291493357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191345308344357569554631237 35877245314567044291493357)
      ·
        refine ⟨13453966992962641609310009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35877245314567044291493357 13453966992962641609310009)
        ·
          refine ⟨10090475244721981206982507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13453966992962641609310009 10090475244721981206982507)
          ·
            refine ⟨15135712867082971810473761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10090475244721981206982507 15135712867082971810473761)
            ·
              refine ⟨11351784650312228857855321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15135712867082971810473761 11351784650312228857855321)
              ·
                refine ⟨8513838487734171643391491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11351784650312228857855321 8513838487734171643391491)
                ·
                  refine ⟨12770757731601257465087237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8513838487734171643391491 12770757731601257465087237)
                  ·
                    refine ⟨2394517074675235774703857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12770757731601257465087237 2394517074675235774703857)
                    ·
                      refine ⟨1795887806006426831027893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394517074675235774703857 1795887806006426831027893)
                      ·
                        rfl

theorem cell23_3497479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3497479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497479 prefixEnd_3497479 := by exact prefixLift 3497479
  have htrace : WordTrace (prefixWord ++ tailWord_3497479) baseStart_3497479 baseEnd_3497479 := by
    simpa [prefixWord, tailWord_3497479, baseEnd_3497479] using wordTrace_append hprefix tailTrace_3497479
  have hstable : (prefixWord ++ tailWord_3497479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497479).length < 2 ^ (prefixWord ++ tailWord_3497479).sum := by decide
  have hdescent : baseEnd_3497479 < baseStart_3497479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497483 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 1, 3, 2]
def baseStart_3497483 : Nat := 118140960795 + 3497483 * 2 ^ 59
def prefixEnd_3497483 : Nat := 4983230072969 + 3 ^ 40 * 3497483 * 2
def baseEnd_3497483 : Nat := 1795889859929044815377875

theorem tailTrace_3497483 : CollatzResearch.WordTrace tailWord_3497483 prefixEnd_3497483 1795889859929044815377875 := by
  unfold tailWord_3497483
  simp only [CollatzResearch.WordTrace]
  refine ⟨127563684788223888386233103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85042456525482592257488735 127563684788223888386233103)
  ·
    refine ⟨191345527182335832579349655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127563684788223888386233103 191345527182335832579349655)
    ·
      refine ⟨287018290773503748869024483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191345527182335832579349655 287018290773503748869024483)
      ·
        refine ⟨430527436160255623303536725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287018290773503748869024483 430527436160255623303536725)
        ·
          refine ⟨5045243392502995585588321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 430527436160255623303536725 5045243392502995585588321)
          ·
            refine ⟨3783932544377246689191241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045243392502995585588321 3783932544377246689191241)
            ·
              refine ⟨2837949408282935016893431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783932544377246689191241 2837949408282935016893431)
              ·
                refine ⟨4256924112424402525340147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837949408282935016893431 4256924112424402525340147)
                ·
                  refine ⟨6385386168636603788010221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4256924112424402525340147 6385386168636603788010221)
                  ·
                    refine ⟨2394519813238726420503833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6385386168636603788010221 2394519813238726420503833)
                    ·
                      refine ⟨1795889859929044815377875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394519813238726420503833 1795889859929044815377875)
                      ·
                        rfl

theorem cell23_3497483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 3, 2].length) (baseStart_3497483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497483 prefixEnd_3497483 := by exact prefixLift 3497483
  have htrace : WordTrace (prefixWord ++ tailWord_3497483) baseStart_3497483 baseEnd_3497483 := by
    simpa [prefixWord, tailWord_3497483, baseEnd_3497483] using wordTrace_append hprefix tailTrace_3497483
  have hstable : (prefixWord ++ tailWord_3497483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497483).length < 2 ^ (prefixWord ++ tailWord_3497483).sum := by decide
  have hdescent : baseEnd_3497483 < baseStart_3497483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497496 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3497496 : Nat := 118140960795 + 3497496 * 2 ^ 59
def prefixEnd_3497496 : Nat := 4983230072969 + 3 ^ 40 * 3497496 * 2
def baseEnd_3497496 : Nat := 1795896535177553264515315

theorem tailTrace_3497496 : CollatzResearch.WordTrace tailWord_3497496 prefixEnd_3497496 1795896535177553264515315 := by
  unfold tailWord_3497496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63782079468588395803228171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85042772624784527737637561 63782079468588395803228171)
  ·
    refine ⟨95673119202882593704842257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63782079468588395803228171 95673119202882593704842257)
    ·
      refine ⟨71754839402161945278631693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95673119202882593704842257 71754839402161945278631693)
      ·
        refine ⟨26908064775810729479486885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71754839402161945278631693 26908064775810729479486885)
        ·
          refine ⟨5045262145464511777403791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26908064775810729479486885 5045262145464511777403791)
          ·
            refine ⟨7567893218196767666105687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045262145464511777403791 7567893218196767666105687)
            ·
              refine ⟨11351839827295151499158531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7567893218196767666105687 11351839827295151499158531)
              ·
                refine ⟨17027759740942727248737797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11351839827295151499158531 17027759740942727248737797)
                ·
                  refine ⟨3192704951426761359138337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17027759740942727248737797 3192704951426761359138337)
                  ·
                    refine ⟨2394528713570071019353753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3192704951426761359138337 2394528713570071019353753)
                    ·
                      refine ⟨1795896535177553264515315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394528713570071019353753 1795896535177553264515315)
                      ·
                        rfl

theorem cell23_3497496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3497496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497496 prefixEnd_3497496 := by exact prefixLift 3497496
  have htrace : WordTrace (prefixWord ++ tailWord_3497496) baseStart_3497496 baseEnd_3497496 := by
    simpa [prefixWord, tailWord_3497496, baseEnd_3497496] using wordTrace_append hprefix tailTrace_3497496
  have hstable : (prefixWord ++ tailWord_3497496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497496).length < 2 ^ (prefixWord ++ tailWord_3497496).sum := by decide
  have hdescent : baseEnd_3497496 < baseStart_3497496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497552 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_3497552 : Nat := 118140960795 + 3497552 * 2 ^ 59
def prefixEnd_3497552 : Nat := 4983230072969 + 3 ^ 40 * 3497552 * 2
def baseEnd_3497552 : Nat := 1795925290094205045415057

theorem tailTrace_3497552 : CollatzResearch.WordTrace tailWord_3497552 prefixEnd_3497552 1795925290094205045415057 := by
  unfold tailWord_3497552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63783100712486956585247455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85044134283315942113663273 63783100712486956585247455)
  ·
    refine ⟨95674651068730434877871183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63783100712486956585247455 95674651068730434877871183)
    ·
      refine ⟨143511976603095652316806775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95674651068730434877871183 143511976603095652316806775)
      ·
        refine ⟨215267964904643478475210163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143511976603095652316806775 215267964904643478475210163)
        ·
          refine ⟨322901947356965217712815245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215267964904643478475210163 322901947356965217712815245)
          ·
            refine ⟨121088230258861956642305717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322901947356965217712815245 121088230258861956642305717)
            ·
              refine ⟨11352021586768308435216161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121088230258861956642305717 11352021586768308435216161)
              ·
                refine ⟨8514016190076231326412121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11352021586768308435216161 8514016190076231326412121)
                ·
                  refine ⟨6385512142557173494809091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8514016190076231326412121 6385512142557173494809091)
                  ·
                    refine ⟨9578268213835760242213637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6385512142557173494809091 9578268213835760242213637)
                    ·
                      refine ⟨1795925290094205045415057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9578268213835760242213637 1795925290094205045415057)
                      ·
                        rfl

theorem cell23_3497552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_3497552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497552 prefixEnd_3497552 := by exact prefixLift 3497552
  have htrace : WordTrace (prefixWord ++ tailWord_3497552) baseStart_3497552 baseEnd_3497552 := by
    simpa [prefixWord, tailWord_3497552, baseEnd_3497552] using wordTrace_append hprefix tailTrace_3497552
  have hstable : (prefixWord ++ tailWord_3497552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497552).length < 2 ^ (prefixWord ++ tailWord_3497552).sum := by decide
  have hdescent : baseEnd_3497552 < baseStart_3497552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497615 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_3497615 : Nat := 118140960795 + 3497615 * 2 ^ 59
def prefixEnd_3497615 : Nat := 4983230072969 + 3 ^ 40 * 3497615 * 2
def baseEnd_3497615 : Nat := 1795957639375438298927267

theorem tailTrace_3497615 : CollatzResearch.WordTrace tailWord_3497615 prefixEnd_3497615 1795957639375438298927267 := by
  unfold tailWord_3497615
  simp only [CollatzResearch.WordTrace]
  refine ⟨127568499223745674930038299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85045666149163783286692199 127568499223745674930038299)
  ·
    refine ⟨191352748835618512395057449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127568499223745674930038299 191352748835618512395057449)
    ·
      refine ⟨143514561626713884296293087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191352748835618512395057449 143514561626713884296293087)
      ·
        refine ⟨215271842440070826444439631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143514561626713884296293087 215271842440070826444439631)
        ·
          refine ⟨322907763660106239666659447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215271842440070826444439631 322907763660106239666659447)
          ·
            refine ⟨484361645490159359499989171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322907763660106239666659447 484361645490159359499989171)
            ·
              refine ⟨726542468235239039249983757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484361645490159359499989171 726542468235239039249983757)
              ·
                refine ⟨272453425588214639718743909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726542468235239039249983757 272453425588214639718743909)
                ·
                  refine ⟨51085017297790244947264483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272453425588214639718743909 51085017297790244947264483)
                  ·
                    refine ⟨76627525946685367420896725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51085017297790244947264483 76627525946685367420896725)
                    ·
                      refine ⟨1795957639375438298927267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76627525946685367420896725 1795957639375438298927267)
                      ·
                        rfl

theorem cell23_3497615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_3497615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497615 prefixEnd_3497615 := by exact prefixLift 3497615
  have htrace : WordTrace (prefixWord ++ tailWord_3497615) baseStart_3497615 baseEnd_3497615 := by
    simpa [prefixWord, tailWord_3497615, baseEnd_3497615] using wordTrace_append hprefix tailTrace_3497615
  have hstable : (prefixWord ++ tailWord_3497615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497615).length < 2 ^ (prefixWord ++ tailWord_3497615).sum := by decide
  have hdescent : baseEnd_3497615 < baseStart_3497615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497629 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_3497629 : Nat := 118140960795 + 3497629 * 2 ^ 59
def prefixEnd_3497629 : Nat := 4983230072969 + 3 ^ 40 * 3497629 * 2
def baseEnd_3497629 : Nat := 1795964828104601244152203

theorem tailTrace_3497629 : CollatzResearch.WordTrace tailWord_3497629 prefixEnd_3497629 1795964828104601244152203 := by
  unfold tailWord_3497629
  simp only [CollatzResearch.WordTrace]
  refine ⟨127569009845694955321047941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85046006563796636880698627 127569009845694955321047941)
  ·
    refine ⟨23919189346067804122696489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127569009845694955321047941 23919189346067804122696489)
    ·
      refine ⟨17939392009550853092022367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23919189346067804122696489 17939392009550853092022367)
      ·
        refine ⟨26909088014326279638033551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17939392009550853092022367 26909088014326279638033551)
        ·
          refine ⟨40363632021489419457050327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26909088014326279638033551 40363632021489419457050327)
          ·
            refine ⟨60545448032234129185575491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40363632021489419457050327 60545448032234129185575491)
            ·
              refine ⟨90818172048351193778363237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60545448032234129185575491 90818172048351193778363237)
              ·
                refine ⟨17028407259065848833443107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90818172048351193778363237 17028407259065848833443107)
                ·
                  refine ⟨25542610888598773250164661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17028407259065848833443107 25542610888598773250164661)
                  ·
                    refine ⟨2394619770806134992202937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25542610888598773250164661 2394619770806134992202937)
                    ·
                      refine ⟨1795964828104601244152203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394619770806134992202937 1795964828104601244152203)
                      ·
                        rfl

theorem cell23_3497629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_3497629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497629 prefixEnd_3497629 := by exact prefixLift 3497629
  have htrace : WordTrace (prefixWord ++ tailWord_3497629) baseStart_3497629 baseEnd_3497629 := by
    simpa [prefixWord, tailWord_3497629, baseEnd_3497629] using wordTrace_append hprefix tailTrace_3497629
  have hstable : (prefixWord ++ tailWord_3497629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497629).length < 2 ^ (prefixWord ++ tailWord_3497629).sum := by decide
  have hdescent : baseEnd_3497629 < baseStart_3497629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497636 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_3497636 : Nat := 118140960795 + 3497636 * 2 ^ 59
def prefixEnd_3497636 : Nat := 4983230072969 + 3 ^ 40 * 3497636 * 2
def baseEnd_3497636 : Nat := 1795968422469182716764671

theorem tailTrace_3497636 : CollatzResearch.WordTrace tailWord_3497636 prefixEnd_3497636 1795968422469182716764671 := by
  unfold tailWord_3497636
  simp only [CollatzResearch.WordTrace]
  refine ⟨63784632578334797758276381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85046176771113063677701841 63784632578334797758276381)
  ·
    refine ⟨23919237216875549159353643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63784632578334797758276381 23919237216875549159353643)
    ·
      refine ⟨35878855825313323739030465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23919237216875549159353643 35878855825313323739030465)
      ·
        refine ⟨26909141868984992804272849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35878855825313323739030465 26909141868984992804272849)
        ·
          refine ⟨20181856401738744603204637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26909141868984992804272849 20181856401738744603204637)
          ·
            refine ⟨7568196150652029226201739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20181856401738744603204637 7568196150652029226201739)
            ·
              refine ⟨11352294225978043839302609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568196150652029226201739 11352294225978043839302609)
              ·
                refine ⟨8514220669483532879476957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11352294225978043839302609 8514220669483532879476957)
                ·
                  refine ⟨3192832751056324829803859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8514220669483532879476957 3192832751056324829803859)
                  ·
                    refine ⟨4789249126584487244705789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192832751056324829803859 4789249126584487244705789)
                    ·
                      refine ⟨1795968422469182716764671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4789249126584487244705789 1795968422469182716764671)
                      ·
                        rfl

theorem cell23_3497636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_3497636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497636 prefixEnd_3497636 := by exact prefixLift 3497636
  have htrace : WordTrace (prefixWord ++ tailWord_3497636) baseStart_3497636 baseEnd_3497636 := by
    simpa [prefixWord, tailWord_3497636, baseEnd_3497636] using wordTrace_append hprefix tailTrace_3497636
  have hstable : (prefixWord ++ tailWord_3497636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497636).length < 2 ^ (prefixWord ++ tailWord_3497636).sum := by decide
  have hdescent : baseEnd_3497636 < baseStart_3497636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497670 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3497670 : Nat := 118140960795 + 3497670 * 2 ^ 59
def prefixEnd_3497670 : Nat := 4983230072969 + 3 ^ 40 * 3497670 * 2
def baseEnd_3497670 : Nat := 1795985880811435583739515

theorem tailTrace_3497670 : CollatzResearch.WordTrace tailWord_3497670 prefixEnd_3497670 1795985880811435583739515 := by
  unfold tailWord_3497670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986578288704575603852827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85047003492364279548860309 3986578288704575603852827)
  ·
    refine ⟨5979867433056863405779241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3986578288704575603852827 5979867433056863405779241)
    ·
      refine ⟨4484900574792647554334431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5979867433056863405779241 4484900574792647554334431)
      ·
        refine ⟨6727350862188971331501647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484900574792647554334431 6727350862188971331501647)
        ·
          refine ⟨10091026293283456997252471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727350862188971331501647 10091026293283456997252471)
          ·
            refine ⟨15136539439925185495878707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10091026293283456997252471 15136539439925185495878707)
            ·
              refine ⟨22704809159887778243818061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15136539439925185495878707 22704809159887778243818061)
              ·
                refine ⟨8514303434957916841431773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22704809159887778243818061 8514303434957916841431773)
                ·
                  refine ⟨3192863788109218815536915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8514303434957916841431773 3192863788109218815536915)
                  ·
                    refine ⟨4789295682163828223305373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3192863788109218815536915 4789295682163828223305373)
                    ·
                      refine ⟨1795985880811435583739515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4789295682163828223305373 1795985880811435583739515)
                      ·
                        rfl

theorem cell23_3497670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3497670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497670 prefixEnd_3497670 := by exact prefixLift 3497670
  have htrace : WordTrace (prefixWord ++ tailWord_3497670) baseStart_3497670 baseEnd_3497670 := by
    simpa [prefixWord, tailWord_3497670, baseEnd_3497670] using wordTrace_append hprefix tailTrace_3497670
  have hstable : (prefixWord ++ tailWord_3497670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497670).length < 2 ^ (prefixWord ++ tailWord_3497670).sum := by decide
  have hdescent : baseEnd_3497670 < baseStart_3497670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497672 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3497672 : Nat := 118140960795 + 3497672 * 2 ^ 59
def prefixEnd_3497672 : Nat := 4983230072969 + 3 ^ 40 * 3497672 * 2
def baseEnd_3497672 : Nat := 1795986907772744575914505

theorem tailTrace_3497672 : CollatzResearch.WordTrace tailWord_3497672 prefixEnd_3497672 1795986907772744575914505 := by
  unfold tailWord_3497672
  simp only [CollatzResearch.WordTrace]
  refine ⟨63785289092269586832431635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85047052123026115776575513 63785289092269586832431635)
  ·
    refine ⟨95677933638404380248647453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63785289092269586832431635 95677933638404380248647453)
    ·
      refine ⟨35879225114401642593242795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95677933638404380248647453 35879225114401642593242795)
      ·
        refine ⟨53818837671602463889864193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35879225114401642593242795 53818837671602463889864193)
        ·
          refine ⟨40364128253701847917398145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53818837671602463889864193 40364128253701847917398145)
          ·
            refine ⟨30273096190276385938048609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40364128253701847917398145 30273096190276385938048609)
            ·
              refine ⟨22704822142707289453536457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30273096190276385938048609 22704822142707289453536457)
              ·
                refine ⟨17028616607030467090152343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22704822142707289453536457 17028616607030467090152343)
                ·
                  refine ⟨25542924910545700635228515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17028616607030467090152343 25542924910545700635228515)
                  ·
                    refine ⟨38314387365818550952842773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25542924910545700635228515 38314387365818550952842773)
                    ·
                      refine ⟨1795986907772744575914505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38314387365818550952842773 1795986907772744575914505)
                      ·
                        rfl

theorem cell23_3497672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3497672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497672 prefixEnd_3497672 := by exact prefixLift 3497672
  have htrace : WordTrace (prefixWord ++ tailWord_3497672) baseStart_3497672 baseEnd_3497672 := by
    simpa [prefixWord, tailWord_3497672, baseEnd_3497672] using wordTrace_append hprefix tailTrace_3497672
  have hstable : (prefixWord ++ tailWord_3497672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497672).length < 2 ^ (prefixWord ++ tailWord_3497672).sum := by decide
  have hdescent : baseEnd_3497672 < baseStart_3497672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497689 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3497689 : Nat := 118140960795 + 3497689 * 2 ^ 59
def prefixEnd_3497689 : Nat := 4983230072969 + 3 ^ 40 * 3497689 * 2
def baseEnd_3497689 : Nat := 1795995636943871009401927

theorem tailTrace_3497689 : CollatzResearch.WordTrace tailWord_3497689 prefixEnd_3497689 1795995636943871009401927 := by
  unfold tailWord_3497689
  simp only [CollatzResearch.WordTrace]
  refine ⟨127571198225477585568232121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85047465483651723712154747 127571198225477585568232121)
  ·
    refine ⟨95678398669108189176174091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127571198225477585568232121 95678398669108189176174091)
    ·
      refine ⟨143517598003662283764261137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95678398669108189176174091 143517598003662283764261137)
      ·
        refine ⟨107638198502746712823195853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143517598003662283764261137 107638198502746712823195853)
        ·
          refine ⟨40364324438530017308698445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107638198502746712823195853 40364324438530017308698445)
          ·
            refine ⟨15136621664448756490761917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40364324438530017308698445 15136621664448756490761917)
            ·
              refine ⟨5676233124168283684035719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15136621664448756490761917 5676233124168283684035719)
              ·
                refine ⟨8514349686252425526053579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676233124168283684035719 8514349686252425526053579)
                ·
                  refine ⟨12771524529378638289080369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8514349686252425526053579 12771524529378638289080369)
                  ·
                    refine ⟨9578643397033978716810277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12771524529378638289080369 9578643397033978716810277)
                    ·
                      refine ⟨1795995636943871009401927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9578643397033978716810277 1795995636943871009401927)
                      ·
                        rfl

theorem cell23_3497689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3497689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497689 prefixEnd_3497689 := by exact prefixLift 3497689
  have htrace : WordTrace (prefixWord ++ tailWord_3497689) baseStart_3497689 baseEnd_3497689 := by
    simpa [prefixWord, tailWord_3497689, baseEnd_3497689] using wordTrace_append hprefix tailTrace_3497689
  have hstable : (prefixWord ++ tailWord_3497689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497689).length < 2 ^ (prefixWord ++ tailWord_3497689).sum := by decide
  have hdescent : baseEnd_3497689 < baseStart_3497689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497699 : List Nat := [1, 1, 1, 7, 2, 1, 1, 9]
def baseStart_3497699 : Nat := 118140960795 + 3497699 * 2 ^ 59
def prefixEnd_3497699 : Nat := 4983230072969 + 3 ^ 40 * 3497699 * 2
def baseEnd_3497699 : Nat := 66518547101867258158403

theorem tailTrace_3497699 : CollatzResearch.WordTrace tailWord_3497699 prefixEnd_3497699 66518547101867258158403 := by
  unfold tailWord_3497699
  simp only [CollatzResearch.WordTrace]
  refine ⟨127571562955441357276096151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85047708636960904850730767 127571562955441357276096151)
  ·
    refine ⟨191357344433162035914144227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127571562955441357276096151 191357344433162035914144227)
    ·
      refine ⟨287036016649743053871216341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191357344433162035914144227 287036016649743053871216341)
      ·
        refine ⟨6727406640228352825106633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 287036016649743053871216341 6727406640228352825106633)
        ·
          refine ⟨5045554980171264618829975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727406640228352825106633 5045554980171264618829975)
          ·
            refine ⟨7568332470256896928244963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045554980171264618829975 7568332470256896928244963)
            ·
              refine ⟨11352498705385345392367445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7568332470256896928244963 11352498705385345392367445)
              ·
                refine ⟨66518547101867258158403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11352498705385345392367445 66518547101867258158403)
                ·
                  rfl

theorem cell23_3497699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 9].length) (baseStart_3497699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497699 prefixEnd_3497699 := by exact prefixLift 3497699
  have htrace : WordTrace (prefixWord ++ tailWord_3497699) baseStart_3497699 baseEnd_3497699 := by
    simpa [prefixWord, tailWord_3497699, baseEnd_3497699] using wordTrace_append hprefix tailTrace_3497699
  have hstable : (prefixWord ++ tailWord_3497699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497699).length < 2 ^ (prefixWord ++ tailWord_3497699).sum := by decide
  have hdescent : baseEnd_3497699 < baseStart_3497699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497716 : List Nat := [2, 6, 1, 1, 1, 1, 11]
def baseStart_3497716 : Nat := 118140960795 + 3497716 * 2 ^ 59
def prefixEnd_3497716 : Nat := 4983230072969 + 3 ^ 40 * 3497716 * 2
def baseEnd_3497716 : Nat := 22172956801500523503263

theorem tailTrace_3497716 : CollatzResearch.WordTrace tailWord_3497716 prefixEnd_3497716 22172956801500523503263 := by
  unfold tailWord_3497716
  simp only [CollatzResearch.WordTrace]
  refine ⟨63786091498189884589732501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85048121997586512786310001 63786091498189884589732501)
  ·
    refine ⟨2989973038977650840143711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63786091498189884589732501 2989973038977650840143711)
    ·
      refine ⟨4484959558466476260215567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989973038977650840143711 4484959558466476260215567)
      ·
        refine ⟨6727439337699714390323351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484959558466476260215567 6727439337699714390323351)
        ·
          refine ⟨10091159006549571585485027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727439337699714390323351 10091159006549571585485027)
          ·
            refine ⟨15136738509824357378227541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10091159006549571585485027 15136738509824357378227541)
            ·
              refine ⟨22172956801500523503263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15136738509824357378227541 22172956801500523503263)
              ·
                rfl

theorem cell23_3497716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 11].length) (baseStart_3497716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497716 prefixEnd_3497716 := by exact prefixLift 3497716
  have htrace : WordTrace (prefixWord ++ tailWord_3497716) baseStart_3497716 baseEnd_3497716 := by
    simpa [prefixWord, tailWord_3497716, baseEnd_3497716] using wordTrace_append hprefix tailTrace_3497716
  have hstable : (prefixWord ++ tailWord_3497716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497716).length < 2 ^ (prefixWord ++ tailWord_3497716).sum := by decide
  have hdescent : baseEnd_3497716 < baseStart_3497716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497722 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3497722 : Nat := 118140960795 + 3497722 * 2 ^ 59
def prefixEnd_3497722 : Nat := 4983230072969 + 3 ^ 40 * 3497722 * 2
def baseEnd_3497722 : Nat := 1796012581805469380289275

theorem tailTrace_3497722 : CollatzResearch.WordTrace tailWord_3497722 prefixEnd_3497722 1796012581805469380289275 := by
  unfold tailWord_3497722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31893100458589508051045855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85048267889572021469455613 31893100458589508051045855)
  ·
    refine ⟨47839650687884262076568783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31893100458589508051045855 47839650687884262076568783)
    ·
      refine ⟨71759476031826393114853175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47839650687884262076568783 71759476031826393114853175)
      ·
        refine ⟨107639214047739589672279763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71759476031826393114853175 107639214047739589672279763)
        ·
          refine ⟨161458821071609384508419645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107639214047739589672279763 161458821071609384508419645)
          ·
            refine ⟨60547057901853519190657367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161458821071609384508419645 60547057901853519190657367)
            ·
              refine ⟨90820586852780278785986051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60547057901853519190657367 90820586852780278785986051)
              ·
                refine ⟨136230880279170418178979077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90820586852780278785986051 136230880279170418178979077)
                ·
                  refine ⟨25543290052344453408558577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136230880279170418178979077 25543290052344453408558577)
                  ·
                    refine ⟨19157467539258340056418933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25543290052344453408558577 19157467539258340056418933)
                    ·
                      refine ⟨1796012581805469380289275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19157467539258340056418933 1796012581805469380289275)
                      ·
                        rfl

theorem cell23_3497722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3497722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497722 prefixEnd_3497722 := by exact prefixLift 3497722
  have htrace : WordTrace (prefixWord ++ tailWord_3497722) baseStart_3497722 baseEnd_3497722 := by
    simpa [prefixWord, tailWord_3497722, baseEnd_3497722] using wordTrace_append hprefix tailTrace_3497722
  have hstable : (prefixWord ++ tailWord_3497722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497722).length < 2 ^ (prefixWord ++ tailWord_3497722).sum := by decide
  have hdescent : baseEnd_3497722 < baseStart_3497722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497736 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_3497736 : Nat := 118140960795 + 3497736 * 2 ^ 59
def prefixEnd_3497736 : Nat := 4983230072969 + 3 ^ 40 * 3497736 * 2
def baseEnd_3497736 : Nat := 1796019770534632325514211

theorem tailTrace_3497736 : CollatzResearch.WordTrace tailWord_3497736 prefixEnd_3497736 1796019770534632325514211 := by
  unfold tailWord_3497736
  simp only [CollatzResearch.WordTrace]
  refine ⟨63786456228153656297596531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85048608304204875063462041 63786456228153656297596531)
  ·
    refine ⟨95679684342230484446394797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63786456228153656297596531 95679684342230484446394797)
    ·
      refine ⟨35879881628336431667398049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95679684342230484446394797 35879881628336431667398049)
      ·
        refine ⟨26909911221252323750548537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35879881628336431667398049 26909911221252323750548537)
        ·
          refine ⟨20182433415939242812911403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26909911221252323750548537 20182433415939242812911403)
          ·
            refine ⟨30273650123908864219367105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20182433415939242812911403 30273650123908864219367105)
            ·
              refine ⟨22705237592931648164525329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30273650123908864219367105 22705237592931648164525329)
              ·
                refine ⟨17028928194698736123393997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22705237592931648164525329 17028928194698736123393997)
                ·
                  refine ⟨6385848073012026046272749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17028928194698736123393997 6385848073012026046272749)
                  ·
                    refine ⟨2394693027379509767352281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6385848073012026046272749 2394693027379509767352281)
                    ·
                      refine ⟨1796019770534632325514211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394693027379509767352281 1796019770534632325514211)
                      ·
                        rfl

theorem cell23_3497736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_3497736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497736 prefixEnd_3497736 := by exact prefixLift 3497736
  have htrace : WordTrace (prefixWord ++ tailWord_3497736) baseStart_3497736 baseEnd_3497736 := by
    simpa [prefixWord, tailWord_3497736, baseEnd_3497736] using wordTrace_append hprefix tailTrace_3497736
  have hstable : (prefixWord ++ tailWord_3497736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497736).length < 2 ^ (prefixWord ++ tailWord_3497736).sum := by decide
  have hdescent : baseEnd_3497736 < baseStart_3497736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497792 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3497792 : Nat := 118140960795 + 3497792 * 2 ^ 59
def prefixEnd_3497792 : Nat := 4983230072969 + 3 ^ 40 * 3497792 * 2
def baseEnd_3497792 : Nat := 1796048525451284106413953

theorem tailTrace_3497792 : CollatzResearch.WordTrace tailWord_3497792 prefixEnd_3497792 1796048525451284106413953 := by
  unfold tailWord_3497792
  simp only [CollatzResearch.WordTrace]
  refine ⟨63787477472052217079615815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85049969962736289439487753 63787477472052217079615815)
  ·
    refine ⟨95681216208078325619423723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63787477472052217079615815 95681216208078325619423723)
    ·
      refine ⟨143521824312117488429135585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95681216208078325619423723 143521824312117488429135585)
      ·
        refine ⟨107641368234088116321851689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143521824312117488429135585 107641368234088116321851689)
        ·
          refine ⟨80731026175566087241388767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107641368234088116321851689 80731026175566087241388767)
          ·
            refine ⟨121096539263349130862083151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80731026175566087241388767 121096539263349130862083151)
            ·
              refine ⟨181644808895023696293124727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121096539263349130862083151 181644808895023696293124727)
              ·
                refine ⟨272467213342535544439687091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181644808895023696293124727 272467213342535544439687091)
                ·
                  refine ⟨408700820013803316659530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272467213342535544439687091 408700820013803316659530637)
                  ·
                    refine ⟨153262807505176243747323989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408700820013803316659530637 153262807505176243747323989)
                    ·
                      refine ⟨1796048525451284106413953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 153262807505176243747323989 1796048525451284106413953)
                      ·
                        rfl

theorem cell23_3497792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3497792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497792 prefixEnd_3497792 := by exact prefixLift 3497792
  have htrace : WordTrace (prefixWord ++ tailWord_3497792) baseStart_3497792 baseEnd_3497792 := by
    simpa [prefixWord, tailWord_3497792, baseEnd_3497792] using wordTrace_append hprefix tailTrace_3497792
  have hstable : (prefixWord ++ tailWord_3497792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497792).length < 2 ^ (prefixWord ++ tailWord_3497792).sum := by decide
  have hdescent : baseEnd_3497792 < baseStart_3497792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497799 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3497799 : Nat := 118140960795 + 3497799 * 2 ^ 59
def prefixEnd_3497799 : Nat := 4983230072969 + 3 ^ 40 * 3497799 * 2
def baseEnd_3497799 : Nat := 1796052119815865579026421

theorem tailTrace_3497799 : CollatzResearch.WordTrace tailWord_3497799 prefixEnd_3497799 1796052119815865579026421 := by
  unfold tailWord_3497799
  simp only [CollatzResearch.WordTrace]
  refine ⟨127575210255079074354736451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85050140170052716236490967 127575210255079074354736451)
  ·
    refine ⟨191362815382618611532104677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127575210255079074354736451 191362815382618611532104677)
    ·
      refine ⟨35880527884240989662269627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191362815382618611532104677 35880527884240989662269627)
      ·
        refine ⟨53820791826361484493404441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35880527884240989662269627 53820791826361484493404441)
        ·
          refine ⟨40365593869771113370053331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53820791826361484493404441 40365593869771113370053331)
          ·
            refine ⟨60548390804656670055079997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40365593869771113370053331 60548390804656670055079997)
            ·
              refine ⟨22705646551746251270654999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60548390804656670055079997 22705646551746251270654999)
              ·
                refine ⟨34058469827619376905982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22705646551746251270654999 34058469827619376905982499)
                ·
                  refine ⟨51087704741429065358973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34058469827619376905982499 51087704741429065358973749)
                  ·
                    refine ⟨4789472319508974877403789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51087704741429065358973749 4789472319508974877403789)
                    ·
                      refine ⟨1796052119815865579026421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4789472319508974877403789 1796052119815865579026421)
                      ·
                        rfl

theorem cell23_3497799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3497799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497799 prefixEnd_3497799 := by exact prefixLift 3497799
  have htrace : WordTrace (prefixWord ++ tailWord_3497799) baseStart_3497799 baseEnd_3497799 := by
    simpa [prefixWord, tailWord_3497799, baseEnd_3497799] using wordTrace_append hprefix tailTrace_3497799
  have hstable : (prefixWord ++ tailWord_3497799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497799).length < 2 ^ (prefixWord ++ tailWord_3497799).sum := by decide
  have hdescent : baseEnd_3497799 < baseStart_3497799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497834 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3497834 : Nat := 118140960795 + 3497834 * 2 ^ 59
def prefixEnd_3497834 : Nat := 4983230072969 + 3 ^ 40 * 3497834 * 2
def baseEnd_3497834 : Nat := 1796070091638772942088761

theorem tailTrace_3497834 : CollatzResearch.WordTrace tailWord_3497834 prefixEnd_3497834 1796070091638772942088761 := by
  unfold tailWord_3497834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31894121702488068833065139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85050991206634850221507037 31894121702488068833065139)
  ·
    refine ⟨47841182553732103249597709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31894121702488068833065139 47841182553732103249597709)
    ·
      refine ⟨17940443457649538718599141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47841182553732103249597709 17940443457649538718599141)
      ·
        refine ⟨3363833148309288509737339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17940443457649538718599141 3363833148309288509737339)
        ·
          refine ⟨5045749722463932764606009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363833148309288509737339 5045749722463932764606009)
          ·
            refine ⟨3784312291847949573454507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045749722463932764606009 3784312291847949573454507)
            ·
              refine ⟨5676468437771924360181761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784312291847949573454507 5676468437771924360181761)
              ·
                refine ⟨4257351328328943270136321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5676468437771924360181761 4257351328328943270136321)
                ·
                  refine ⟨3193013496246707452602241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257351328328943270136321 3193013496246707452602241)
                  ·
                    refine ⟨2394760122185030589451681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193013496246707452602241 2394760122185030589451681)
                    ·
                      refine ⟨1796070091638772942088761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394760122185030589451681 1796070091638772942088761)
                      ·
                        rfl

theorem cell23_3497834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3497834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497834 prefixEnd_3497834 := by exact prefixLift 3497834
  have htrace : WordTrace (prefixWord ++ tailWord_3497834) baseStart_3497834 baseEnd_3497834 := by
    simpa [prefixWord, tailWord_3497834, baseEnd_3497834] using wordTrace_append hprefix tailTrace_3497834
  have hstable : (prefixWord ++ tailWord_3497834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497834).length < 2 ^ (prefixWord ++ tailWord_3497834).sum := by decide
  have hdescent : baseEnd_3497834 < baseStart_3497834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497856 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2]
def baseStart_3497856 : Nat := 118140960795 + 3497856 * 2 ^ 59
def prefixEnd_3497856 : Nat := 4983230072969 + 3 ^ 40 * 3497856 * 2
def baseEnd_3497856 : Nat := 1796081388213171856013659

theorem tailTrace_3497856 : CollatzResearch.WordTrace tailWord_3497856 prefixEnd_3497856 1796081388213171856013659 := by
  unfold tailWord_3497856
  simp only [CollatzResearch.WordTrace]
  refine ⟨63788644607936286544780711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85051526143915048726374281 63788644607936286544780711)
  ·
    refine ⟨95682966911904429817171067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63788644607936286544780711 95682966911904429817171067)
    ·
      refine ⟨143524450367856644725756601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95682966911904429817171067 143524450367856644725756601)
      ·
        refine ⟨107643337775892483544317451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143524450367856644725756601 107643337775892483544317451)
        ·
          refine ⟨161465006663838725316476177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107643337775892483544317451 161465006663838725316476177)
          ·
            refine ⟨121098754997879043987357133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161465006663838725316476177 121098754997879043987357133)
            ·
              refine ⟨45412033124204641495258925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121098754997879043987357133 45412033124204641495258925)
              ·
                refine ⟨17029512421576740560722097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45412033124204641495258925 17029512421576740560722097)
                ·
                  refine ⟨12772134316182555420541573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17029512421576740560722097 12772134316182555420541573)
                  ·
                    refine ⟨2394775184284229141351545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12772134316182555420541573 2394775184284229141351545)
                    ·
                      refine ⟨1796081388213171856013659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394775184284229141351545 1796081388213171856013659)
                      ·
                        rfl

theorem cell23_3497856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_3497856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497856 prefixEnd_3497856 := by exact prefixLift 3497856
  have htrace : WordTrace (prefixWord ++ tailWord_3497856) baseStart_3497856 baseEnd_3497856 := by
    simpa [prefixWord, tailWord_3497856, baseEnd_3497856] using wordTrace_append hprefix tailTrace_3497856
  have hstable : (prefixWord ++ tailWord_3497856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497856).length < 2 ^ (prefixWord ++ tailWord_3497856).sum := by decide
  have hdescent : baseEnd_3497856 < baseStart_3497856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497879 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 8]
def baseStart_3497879 : Nat := 118140960795 + 3497879 * 2 ^ 59
def prefixEnd_3497879 : Nat := 4983230072969 + 3 ^ 40 * 3497879 * 2
def baseEnd_3497879 : Nat := 199565910918691696225117

theorem tailTrace_3497879 : CollatzResearch.WordTrace tailWord_3497879 prefixEnd_3497879 199565910918691696225117 := by
  unfold tailWord_3497879
  simp only [CollatzResearch.WordTrace]
  refine ⟨127578128094789248017648691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85052085396526165345099127 127578128094789248017648691)
  ·
    refine ⟨191367192142183872026473037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127578128094789248017648691 191367192142183872026473037)
    ·
      refine ⟨71762697053318952009927389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191367192142183872026473037 71762697053318952009927389)
      ·
        refine ⟨26911011394994607003722771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71762697053318952009927389 26911011394994607003722771)
        ·
          refine ⟨40366517092491910505584157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26911011394994607003722771 40366517092491910505584157)
          ·
            refine ⟨15137443909684466439594059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40366517092491910505584157 15137443909684466439594059)
            ·
              refine ⟨22706165864526699659391089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15137443909684466439594059 22706165864526699659391089)
              ·
                refine ⟨17029624398395024744543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22706165864526699659391089 17029624398395024744543317)
                ·
                  refine ⟨199565910918691696225117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17029624398395024744543317 199565910918691696225117)
                  ·
                    rfl

theorem cell23_3497879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 8].length) (baseStart_3497879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497879 prefixEnd_3497879 := by exact prefixLift 3497879
  have htrace : WordTrace (prefixWord ++ tailWord_3497879) baseStart_3497879 baseEnd_3497879 := by
    simpa [prefixWord, tailWord_3497879, baseEnd_3497879] using wordTrace_append hprefix tailTrace_3497879
  have hstable : (prefixWord ++ tailWord_3497879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497879).length < 2 ^ (prefixWord ++ tailWord_3497879).sum := by decide
  have hdescent : baseEnd_3497879 < baseStart_3497879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497929 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_3497929 : Nat := 118140960795 + 3497929 * 2 ^ 59
def prefixEnd_3497929 : Nat := 4983230072969 + 3 ^ 40 * 3497929 * 2
def baseEnd_3497929 : Nat := 1796118872300950070400823

theorem tailTrace_3497929 : CollatzResearch.WordTrace tailWord_3497929 prefixEnd_3497929 1796118872300950070400823 := by
  unfold tailWord_3497929
  simp only [CollatzResearch.WordTrace]
  refine ⟨127579951744608106556968841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85053301163072071037979227 127579951744608106556968841)
  ·
    refine ⟨95684963808456079917726631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127579951744608106556968841 95684963808456079917726631)
    ·
      refine ⟨143527445712684119876589947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95684963808456079917726631 143527445712684119876589947)
      ·
        refine ⟨215291168569026179814884921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143527445712684119876589947 215291168569026179814884921)
        ·
          refine ⟨161468376426769634861163691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215291168569026179814884921 161468376426769634861163691)
          ·
            refine ⟨242202564640154452291745537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161468376426769634861163691 242202564640154452291745537)
            ·
              refine ⟨181651923480115839218809153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242202564640154452291745537 181651923480115839218809153)
              ·
                refine ⟨136238942610086879414106865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181651923480115839218809153 136238942610086879414106865)
                ·
                  refine ⟨102179206957565159560580149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136238942610086879414106865 102179206957565159560580149)
                  ·
                    refine ⟨9579300652271733708804389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102179206957565159560580149 9579300652271733708804389)
                    ·
                      refine ⟨1796118872300950070400823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9579300652271733708804389 1796118872300950070400823)
                      ·
                        rfl

theorem cell23_3497929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_3497929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497929 prefixEnd_3497929 := by exact prefixLift 3497929
  have htrace : WordTrace (prefixWord ++ tailWord_3497929) baseStart_3497929 baseEnd_3497929 := by
    simpa [prefixWord, tailWord_3497929, baseEnd_3497929] using wordTrace_append hprefix tailTrace_3497929
  have hstable : (prefixWord ++ tailWord_3497929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497929).length < 2 ^ (prefixWord ++ tailWord_3497929).sum := by decide
  have hdescent : baseEnd_3497929 < baseStart_3497929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497943 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 1, 5]
def baseStart_3497943 : Nat := 118140960795 + 3497943 * 2 ^ 59
def prefixEnd_3497943 : Nat := 4983230072969 + 3 ^ 40 * 3497943 * 2
def baseEnd_3497943 : Nat := 598708687010037671875253

theorem tailTrace_3497943 : CollatzResearch.WordTrace tailWord_3497943 prefixEnd_3497943 598708687010037671875253 := by
  unfold tailWord_3497943
  simp only [CollatzResearch.WordTrace]
  refine ⟨127580462366557386947978483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85053641577704924631985655 127580462366557386947978483)
  ·
    refine ⟨191370693549836080421967725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127580462366557386947978483 191370693549836080421967725)
    ·
      refine ⟨71764010081188530158237897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191370693549836080421967725 71764010081188530158237897)
      ·
        refine ⟨53823007560891397618678423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71764010081188530158237897 53823007560891397618678423)
        ·
          refine ⟨80734511341337096428017635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53823007560891397618678423 80734511341337096428017635)
          ·
            refine ⟨121101767012005644642026453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80734511341337096428017635 121101767012005644642026453)
            ·
              refine ⟨2838322664343882296297495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121101767012005644642026453 2838322664343882296297495)
              ·
                refine ⟨4257483996515823444446243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838322664343882296297495 4257483996515823444446243)
                ·
                  refine ⟨6386225994773735166669365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4257483996515823444446243 6386225994773735166669365)
                  ·
                    refine ⟨598708687010037671875253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6386225994773735166669365 598708687010037671875253)
                    ·
                      rfl

theorem cell23_3497943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_3497943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497943 prefixEnd_3497943 := by exact prefixLift 3497943
  have htrace : WordTrace (prefixWord ++ tailWord_3497943) baseStart_3497943 baseEnd_3497943 := by
    simpa [prefixWord, tailWord_3497943, baseEnd_3497943] using wordTrace_append hprefix tailTrace_3497943
  have hstable : (prefixWord ++ tailWord_3497943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497943).length < 2 ^ (prefixWord ++ tailWord_3497943).sum := by decide
  have hdescent : baseEnd_3497943 < baseStart_3497943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497963 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 7, 2, 2]
def baseStart_3497963 : Nat := 118140960795 + 3497963 * 2 ^ 59
def prefixEnd_3497963 : Nat := 4983230072969 + 3 ^ 40 * 3497963 * 2
def baseEnd_3497963 : Nat := 1796136330643202937375667

theorem tailTrace_3497963 : CollatzResearch.WordTrace tailWord_3497963 prefixEnd_3497963 1796136330643202937375667 := by
  unfold tailWord_3497963
  simp only [CollatzResearch.WordTrace]
  refine ⟨127581191826484930363706543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85054127884323286909137695 127581191826484930363706543)
  ·
    refine ⟨191371787739727395545559815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127581191826484930363706543 191371787739727395545559815)
    ·
      refine ⟨287057681609591093318339723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191371787739727395545559815 287057681609591093318339723)
      ·
        refine ⟨430586522414386639977509585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287057681609591093318339723 430586522414386639977509585)
        ·
          refine ⟨322939891810789979983132189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430586522414386639977509585 322939891810789979983132189)
          ·
            refine ⟨121102459429046242493674571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322939891810789979983132189 121102459429046242493674571)
            ·
              refine ⟨181653689143569363740511857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121102459429046242493674571 181653689143569363740511857)
              ·
                refine ⟨136240266857677022805383893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181653689143569363740511857 136240266857677022805383893)
                ·
                  refine ⟨3193131254476805222001185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 136240266857677022805383893 3193131254476805222001185)
                  ·
                    refine ⟨2394848440857603916500889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193131254476805222001185 2394848440857603916500889)
                    ·
                      refine ⟨1796136330643202937375667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394848440857603916500889 1796136330643202937375667)
                      ·
                        rfl

theorem cell23_3497963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 7, 2, 2].length) (baseStart_3497963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497963 prefixEnd_3497963 := by exact prefixLift 3497963
  have htrace : WordTrace (prefixWord ++ tailWord_3497963) baseStart_3497963 baseEnd_3497963 := by
    simpa [prefixWord, tailWord_3497963, baseEnd_3497963] using wordTrace_append hprefix tailTrace_3497963
  have hstable : (prefixWord ++ tailWord_3497963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497963).length < 2 ^ (prefixWord ++ tailWord_3497963).sum := by decide
  have hdescent : baseEnd_3497963 < baseStart_3497963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497976 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_3497976 : Nat := 118140960795 + 3497976 * 2 ^ 59
def prefixEnd_3497976 : Nat := 4983230072969 + 3 ^ 40 * 3497976 * 2
def baseEnd_3497976 : Nat := 1796143005891711386513107

theorem tailTrace_3497976 : CollatzResearch.WordTrace tailWord_3497976 prefixEnd_3497976 1796143005891711386513107 := by
  unfold tailWord_3497976
  simp only [CollatzResearch.WordTrace]
  refine ⟨63790832987718916791964891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85054443983625222389286521 63790832987718916791964891)
  ·
    refine ⟨95686249481578375187947337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63790832987718916791964891 95686249481578375187947337)
    ·
      refine ⟨71764687111183781390960503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95686249481578375187947337 71764687111183781390960503)
      ·
        refine ⟨107647030666775672086440755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71764687111183781390960503 107647030666775672086440755)
        ·
          refine ⟨161470546000163508129661133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107647030666775672086440755 161470546000163508129661133)
          ·
            refine ⟨60551454750061315548622925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161470546000163508129661133 60551454750061315548622925)
            ·
              refine ⟨22706795531272993330733597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60551454750061315548622925 22706795531272993330733597)
              ·
                refine ⟨8515048324227372499025099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22706795531272993330733597 8515048324227372499025099)
                ·
                  refine ⟨12772572486341058748537649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515048324227372499025099 12772572486341058748537649)
                  ·
                    refine ⟨9579429364755794061403237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12772572486341058748537649 9579429364755794061403237)
                    ·
                      refine ⟨1796143005891711386513107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9579429364755794061403237 1796143005891711386513107)
                      ·
                        rfl

theorem cell23_3497976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_3497976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497976 prefixEnd_3497976 := by exact prefixLift 3497976
  have htrace : WordTrace (prefixWord ++ tailWord_3497976) baseStart_3497976 baseEnd_3497976 := by
    simpa [prefixWord, tailWord_3497976, baseEnd_3497976] using wordTrace_append hprefix tailTrace_3497976
  have hstable : (prefixWord ++ tailWord_3497976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497976).length < 2 ^ (prefixWord ++ tailWord_3497976).sum := by decide
  have hdescent : baseEnd_3497976 < baseStart_3497976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3497980 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_3497980 : Nat := 118140960795 + 3497980 * 2 ^ 59
def prefixEnd_3497980 : Nat := 4983230072969 + 3 ^ 40 * 3497980 * 2
def baseEnd_3497980 : Nat := 1796145059814329370863089

theorem tailTrace_3497980 : CollatzResearch.WordTrace tailWord_3497980 prefixEnd_3497980 1796145059814329370863089 := by
  unfold tailWord_3497980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63790905933711671133537697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85054541244948894844716929 63790905933711671133537697)
  ·
    refine ⟨47843179450283753350153273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63790905933711671133537697 47843179450283753350153273)
    ·
      refine ⟨35882384587712815012614955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47843179450283753350153273 35882384587712815012614955)
      ·
        refine ⟨53823576881569222518922433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35882384587712815012614955 53823576881569222518922433)
        ·
          refine ⟨40367682661176916889191825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53823576881569222518922433 40367682661176916889191825)
          ·
            refine ⟨30275761995882687666893869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40367682661176916889191825 30275761995882687666893869)
            ·
              refine ⟨11353410748456007875085201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30275761995882687666893869 11353410748456007875085201)
              ·
                refine ⟨8515058061342005906313901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11353410748456007875085201 8515058061342005906313901)
                ·
                  refine ⟨3193146773003252214867713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8515058061342005906313901 3193146773003252214867713)
                  ·
                    refine ⟨2394860079752439161150785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193146773003252214867713 2394860079752439161150785)
                    ·
                      refine ⟨1796145059814329370863089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394860079752439161150785 1796145059814329370863089)
                      ·
                        rfl

theorem cell23_3497980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_3497980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3497980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3497980 prefixEnd_3497980 := by exact prefixLift 3497980
  have htrace : WordTrace (prefixWord ++ tailWord_3497980) baseStart_3497980 baseEnd_3497980 := by
    simpa [prefixWord, tailWord_3497980, baseEnd_3497980] using wordTrace_append hprefix tailTrace_3497980
  have hstable : (prefixWord ++ tailWord_3497980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3497980).length < 2 ^ (prefixWord ++ tailWord_3497980).sum := by decide
  have hdescent : baseEnd_3497980 < baseStart_3497980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3497980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498007 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 2, 4]
def baseStart_3498007 : Nat := 118140960795 + 3498007 * 2 ^ 59
def prefixEnd_3498007 : Nat := 4983230072969 + 3 ^ 40 * 3498007 * 2
def baseEnd_3498007 : Nat := 598719641264000255075155

theorem tailTrace_3498007 : CollatzResearch.WordTrace tailWord_3498007 prefixEnd_3498007 598719641264000255075155 := by
  unfold tailWord_3498007
  simp only [CollatzResearch.WordTrace]
  refine ⟨127582796638325525878308275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85055197758883683918872183 127582796638325525878308275)
  ·
    refine ⟨191374194957488288817462413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127582796638325525878308275 191374194957488288817462413)
    ·
      refine ⟨71765323109058108306548405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191374194957488288817462413 71765323109058108306548405)
      ·
        refine ⟨6727999041474197653738913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71765323109058108306548405 6727999041474197653738913)
        ·
          refine ⟨5045999281105648240304185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6727999041474197653738913 5045999281105648240304185)
          ·
            refine ⟨3784499460829236180228139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045999281105648240304185 3784499460829236180228139)
            ·
              refine ⟨5676749191243854270342209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784499460829236180228139 5676749191243854270342209)
              ·
                refine ⟨4257561893432890702756657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5676749191243854270342209 4257561893432890702756657)
                ·
                  refine ⟨3193171420074668027067493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257561893432890702756657 3193171420074668027067493)
                  ·
                    refine ⟨598719641264000255075155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193171420074668027067493 598719641264000255075155)
                    ·
                      rfl

theorem cell23_3498007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_3498007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498007 prefixEnd_3498007 := by exact prefixLift 3498007
  have htrace : WordTrace (prefixWord ++ tailWord_3498007) baseStart_3498007 baseEnd_3498007 := by
    simpa [prefixWord, tailWord_3498007, baseEnd_3498007] using wordTrace_append hprefix tailTrace_3498007
  have hstable : (prefixWord ++ tailWord_3498007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498007).length < 2 ^ (prefixWord ++ tailWord_3498007).sum := by decide
  have hdescent : baseEnd_3498007 < baseStart_3498007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498024 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3498024 : Nat := 118140960795 + 3498024 * 2 ^ 59
def prefixEnd_3498024 : Nat := 4983230072969 + 3 ^ 40 * 3498024 * 2
def baseEnd_3498024 : Nat := 598722550987709066237629

theorem tailTrace_3498024 : CollatzResearch.WordTrace tailWord_3498024 prefixEnd_3498024 598722550987709066237629 := by
  unfold tailWord_3498024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63791708339631968890838563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85055611119509291854451417 63791708339631968890838563)
  ·
    refine ⟨95687562509447953336257845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63791708339631968890838563 95687562509447953336257845)
    ·
      refine ⟨8970708985260745625274173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95687562509447953336257845 8970708985260745625274173)
      ·
        refine ⟨3364015869472779609477815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8970708985260745625274173 3364015869472779609477815)
        ·
          refine ⟨5046023804209169414216723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364015869472779609477815 5046023804209169414216723)
          ·
            refine ⟨7569035706313754121325085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046023804209169414216723 7569035706313754121325085)
            ·
              refine ⟨2838388389867657795496907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7569035706313754121325085 2838388389867657795496907)
              ·
                refine ⟨4257582584801486693245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838388389867657795496907 4257582584801486693245361)
                ·
                  refine ⟨3193186938601115019934021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257582584801486693245361 3193186938601115019934021)
                  ·
                    refine ⟨598722550987709066237629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193186938601115019934021 598722550987709066237629)
                    ·
                      rfl

theorem cell23_3498024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3498024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498024 prefixEnd_3498024 := by exact prefixLift 3498024
  have htrace : WordTrace (prefixWord ++ tailWord_3498024) baseStart_3498024 baseEnd_3498024 := by
    simpa [prefixWord, tailWord_3498024, baseEnd_3498024] using wordTrace_append hprefix tailTrace_3498024
  have hstable : (prefixWord ++ tailWord_3498024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498024).length < 2 ^ (prefixWord ++ tailWord_3498024).sum := by decide
  have hdescent : baseEnd_3498024 < baseStart_3498024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498030 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3498030 : Nat := 118140960795 + 3498030 * 2 ^ 59
def prefixEnd_3498030 : Nat := 4983230072969 + 3 ^ 40 * 3498030 * 2
def baseEnd_3498030 : Nat := 1796170733847054175237859

theorem tailTrace_3498030 : CollatzResearch.WordTrace tailWord_3498030 prefixEnd_3498030 1796170733847054175237859 := by
  unfold tailWord_3498030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15947954439655275100799443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85055757011494800537597029 15947954439655275100799443)
  ·
    refine ⟨23921931659482912651199165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15947954439655275100799443 23921931659482912651199165)
    ·
      refine ⟨8970724372306092244199687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23921931659482912651199165 8970724372306092244199687)
      ·
        refine ⟨13456086558459138366299531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970724372306092244199687 13456086558459138366299531)
        ·
          refine ⟨20184129837688707549449297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13456086558459138366299531 20184129837688707549449297)
          ·
            refine ⟨15138097378266530662086973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20184129837688707549449297 15138097378266530662086973)
            ·
              refine ⟨5676786516849948998282615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15138097378266530662086973 5676786516849948998282615)
              ·
                refine ⟨8515179775274923497423923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676786516849948998282615 8515179775274923497423923)
                ·
                  refine ⟨12772769662912385246135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8515179775274923497423923 12772769662912385246135885)
                  ·
                    refine ⟨4789788623592144467300957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12772769662912385246135885 4789788623592144467300957)
                    ·
                      refine ⟨1796170733847054175237859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4789788623592144467300957 1796170733847054175237859)
                      ·
                        rfl

theorem cell23_3498030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3498030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498030 prefixEnd_3498030 := by exact prefixLift 3498030
  have htrace : WordTrace (prefixWord ++ tailWord_3498030) baseStart_3498030 baseEnd_3498030 := by
    simpa [prefixWord, tailWord_3498030, baseEnd_3498030] using wordTrace_append hprefix tailTrace_3498030
  have hstable : (prefixWord ++ tailWord_3498030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498030).length < 2 ^ (prefixWord ++ tailWord_3498030).sum := by decide
  have hdescent : baseEnd_3498030 < baseStart_3498030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498053 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_3498053 : Nat := 118140960795 + 3498053 * 2 ^ 59
def prefixEnd_3498053 : Nat := 4983230072969 + 3 ^ 40 * 3498053 * 2
def baseEnd_3498053 : Nat := 1796182543902107585250253

theorem tailTrace_3498053 : CollatzResearch.WordTrace tailWord_3498053 prefixEnd_3498053 1796182543902107585250253 := by
  unfold tailWord_3498053
  simp only [CollatzResearch.WordTrace]
  refine ⟨127584474396158875734482813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85056316264105917156321875 127584474396158875734482813)
  ·
    refine ⟨47844177898559578400431055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127584474396158875734482813 47844177898559578400431055)
    ·
      refine ⟨71766266847839367600646583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47844177898559578400431055 71766266847839367600646583)
      ·
        refine ⟨107649400271759051400969875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71766266847839367600646583 107649400271759051400969875)
        ·
          refine ⟨161474100407638577101454813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107649400271759051400969875 161474100407638577101454813)
          ·
            refine ⟨60552787652864466413045555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161474100407638577101454813 60552787652864466413045555)
            ·
              refine ⟨90829181479296699619568333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60552787652864466413045555 90829181479296699619568333)
              ·
                refine ⟨34060943054736262357338125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90829181479296699619568333 34060943054736262357338125)
                ·
                  refine ⟨12772853645526098384001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34060943054736262357338125 12772853645526098384001797)
                  ·
                    refine ⟨2394910058536143447000337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12772853645526098384001797 2394910058536143447000337)
                    ·
                      refine ⟨1796182543902107585250253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394910058536143447000337 1796182543902107585250253)
                      ·
                        rfl

theorem cell23_3498053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_3498053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498053 prefixEnd_3498053 := by exact prefixLift 3498053
  have htrace : WordTrace (prefixWord ++ tailWord_3498053) baseStart_3498053 baseEnd_3498053 := by
    simpa [prefixWord, tailWord_3498053, baseEnd_3498053] using wordTrace_append hprefix tailTrace_3498053
  have hstable : (prefixWord ++ tailWord_3498053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498053).length < 2 ^ (prefixWord ++ tailWord_3498053).sum := by decide
  have hdescent : baseEnd_3498053 < baseStart_3498053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498087 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_3498087 : Nat := 118140960795 + 3498087 * 2 ^ 59
def prefixEnd_3498087 : Nat := 4983230072969 + 3 ^ 40 * 3498087 * 2
def baseEnd_3498087 : Nat := 1796200002244360452225097

theorem tailTrace_3498087 : CollatzResearch.WordTrace tailWord_3498087 prefixEnd_3498087 1796200002244360452225097 := by
  unfold tailWord_3498087
  simp only [CollatzResearch.WordTrace]
  refine ⟨127585714478035699541220515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85057142985357133027480343 127585714478035699541220515)
  ·
    refine ⟨191378571717053549311830773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127585714478035699541220515 191378571717053549311830773)
    ·
      refine ⟨17941741098473770247984135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191378571717053549311830773 17941741098473770247984135)
      ·
        refine ⟨26912611647710655371976203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17941741098473770247984135 26912611647710655371976203)
        ·
          refine ⟨40368917471565983057964305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26912611647710655371976203 40368917471565983057964305)
          ·
            refine ⟨30276688103674487293473229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40368917471565983057964305 30276688103674487293473229)
            ·
              refine ⟨11353758038877932735052461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30276688103674487293473229 11353758038877932735052461)
              ·
                refine ⟨4257659264579224775644673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11353758038877932735052461 4257659264579224775644673)
                ·
                  refine ⟨3193244448434418581733505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4257659264579224775644673 3193244448434418581733505)
                  ·
                    refine ⟨2394933336325813936300129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193244448434418581733505 2394933336325813936300129)
                    ·
                      refine ⟨1796200002244360452225097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394933336325813936300129 1796200002244360452225097)
                      ·
                        rfl

theorem cell23_3498087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_3498087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498087 prefixEnd_3498087 := by exact prefixLift 3498087
  have htrace : WordTrace (prefixWord ++ tailWord_3498087) baseStart_3498087 baseEnd_3498087 := by
    simpa [prefixWord, tailWord_3498087, baseEnd_3498087] using wordTrace_append hprefix tailTrace_3498087
  have hstable : (prefixWord ++ tailWord_3498087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498087).length < 2 ^ (prefixWord ++ tailWord_3498087).sum := by decide
  have hdescent : baseEnd_3498087 < baseStart_3498087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498130 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3498130 : Nat := 118140960795 + 3498130 * 2 ^ 59
def prefixEnd_3498130 : Nat := 4983230072969 + 3 ^ 40 * 3498130 * 2
def baseEnd_3498130 : Nat := 1796222081912503783987399

theorem tailTrace_3498130 : CollatzResearch.WordTrace tailWord_3498130 prefixEnd_3498130 1796222081912503783987399 := by
  unfold tailWord_3498130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31896820704219979471258961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85058188544586611923357229 31896820704219979471258961)
  ·
    refine ⟨23922615528164984603444221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31896820704219979471258961 23922615528164984603444221)
    ·
      refine ⟨8970980823061869226291583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23922615528164984603444221 8970980823061869226291583)
      ·
        refine ⟨13456471234592803839437375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8970980823061869226291583 13456471234592803839437375)
        ·
          refine ⟨20184706851889205759156063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13456471234592803839437375 20184706851889205759156063)
          ·
            refine ⟨30277060277833808638734095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20184706851889205759156063 30277060277833808638734095)
            ·
              refine ⟨45415590416750712958101143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30277060277833808638734095 45415590416750712958101143)
              ·
                refine ⟨68123385625126069437151715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45415590416750712958101143 68123385625126069437151715)
                ·
                  refine ⟨102185078437689104155727573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68123385625126069437151715 102185078437689104155727573)
                  ·
                    refine ⟨2394962775883338378649865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102185078437689104155727573 2394962775883338378649865)
                    ·
                      refine ⟨1796222081912503783987399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2394962775883338378649865 1796222081912503783987399)
                      ·
                        rfl

theorem cell23_3498130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3498130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498130 prefixEnd_3498130 := by exact prefixLift 3498130
  have htrace : WordTrace (prefixWord ++ tailWord_3498130) baseStart_3498130 baseEnd_3498130 := by
    simpa [prefixWord, tailWord_3498130, baseEnd_3498130] using wordTrace_append hprefix tailTrace_3498130
  have hstable : (prefixWord ++ tailWord_3498130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498130).length < 2 ^ (prefixWord ++ tailWord_3498130).sum := by decide
  have hdescent : baseEnd_3498130 < baseStart_3498130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498157 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3498157 : Nat := 118140960795 + 3498157 * 2 ^ 59
def prefixEnd_3498157 : Nat := 4983230072969 + 3 ^ 40 * 3498157 * 2
def baseEnd_3498157 : Nat := 598745315296725059449925

theorem tailTrace_3498157 : CollatzResearch.WordTrace tailWord_3498157 prefixEnd_3498157 598745315296725059449925 := by
  unfold tailWord_3498157
  simp only [CollatzResearch.WordTrace]
  refine ⟨127588267587782101496268725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85058845058521400997512483 127588267587782101496268725)
  ·
    refine ⟨11961400086354572015275193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127588267587782101496268725 11961400086354572015275193)
    ·
      refine ⟨8971050064765929011456395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11961400086354572015275193 8971050064765929011456395)
      ·
        refine ⟨13456575097148893517184593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8971050064765929011456395 13456575097148893517184593)
        ·
          refine ⟨10092431322861670137888445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13456575097148893517184593 10092431322861670137888445)
          ·
            refine ⟨3784661746073126301708167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10092431322861670137888445 3784661746073126301708167)
            ·
              refine ⟨5676992619109689452562251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784661746073126301708167 5676992619109689452562251)
              ·
                refine ⟨8515488928664534178843377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5676992619109689452562251 8515488928664534178843377)
                ·
                  refine ⟨6386616696498400634132533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8515488928664534178843377 6386616696498400634132533)
                  ·
                    refine ⟨598745315296725059449925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6386616696498400634132533 598745315296725059449925)
                    ·
                      rfl

theorem cell23_3498157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3498157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498157 prefixEnd_3498157 := by exact prefixLift 3498157
  have htrace : WordTrace (prefixWord ++ tailWord_3498157) baseStart_3498157 baseEnd_3498157 := by
    simpa [prefixWord, tailWord_3498157, baseEnd_3498157] using wordTrace_append hprefix tailTrace_3498157
  have hstable : (prefixWord ++ tailWord_3498157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498157).length < 2 ^ (prefixWord ++ tailWord_3498157).sum := by decide
  have hdescent : baseEnd_3498157 < baseStart_3498157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498220 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_3498220 : Nat := 118140960795 + 3498220 * 2 ^ 59
def prefixEnd_3498220 : Nat := 4983230072969 + 3 ^ 40 * 3498220 * 2
def baseEnd_3498220 : Nat := 1796268295171408431861985

theorem tailTrace_3498220 : CollatzResearch.WordTrace tailWord_3498220 prefixEnd_3498220 1796268295171408431861985 := by
  unfold tailWord_3498220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63795282693276931627906057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85060376924369242170541409 63795282693276931627906057)
  ·
    refine ⟨47846462019957698720929543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63795282693276931627906057 47846462019957698720929543)
    ·
      refine ⟨71769693029936548081394315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47846462019957698720929543 71769693029936548081394315)
      ·
        refine ⟨107654539544904822122091473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71769693029936548081394315 107654539544904822122091473)
        ·
          refine ⟨80740904658678616591568605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107654539544904822122091473 80740904658678616591568605)
          ·
            refine ⟨30277839247004481221838227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80740904658678616591568605 30277839247004481221838227)
            ·
              refine ⟨45416758870506721832757341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30277839247004481221838227 45416758870506721832757341)
              ·
                refine ⟨17031284576440020687284003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45416758870506721832757341 17031284576440020687284003)
                ·
                  refine ⟨25546926864660031030926005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17031284576440020687284003 25546926864660031030926005)
                  ·
                    refine ⟨2395024393561877909149313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25546926864660031030926005 2395024393561877909149313)
                    ·
                      refine ⟨1796268295171408431861985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395024393561877909149313 1796268295171408431861985)
                      ·
                        rfl

theorem cell23_3498220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_3498220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498220 prefixEnd_3498220 := by exact prefixLift 3498220
  have htrace : WordTrace (prefixWord ++ tailWord_3498220) baseStart_3498220 baseEnd_3498220 := by
    simpa [prefixWord, tailWord_3498220, baseEnd_3498220] using wordTrace_append hprefix tailTrace_3498220
  have hstable : (prefixWord ++ tailWord_3498220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498220).length < 2 ^ (prefixWord ++ tailWord_3498220).sum := by decide
  have hdescent : baseEnd_3498220 < baseStart_3498220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498221 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_3498221 : Nat := 118140960795 + 3498221 * 2 ^ 59
def prefixEnd_3498221 : Nat := 4983230072969 + 3 ^ 40 * 3498221 * 2
def baseEnd_3498221 : Nat := 598756269550687642649827

theorem tailTrace_3498221 : CollatzResearch.WordTrace tailWord_3498221 prefixEnd_3498221 598756269550687642649827 := by
  unfold tailWord_3498221
  simp only [CollatzResearch.WordTrace]
  refine ⟨127590601859550240426598517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85060401239700160284399011 127590601859550240426598517)
  ·
    refine ⟨11961618924332835039993611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127590601859550240426598517 11961618924332835039993611)
    ·
      refine ⟨17942428386499252559990417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11961618924332835039993611 17942428386499252559990417)
      ·
        refine ⟨13456821289874439419992813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17942428386499252559990417 13456821289874439419992813)
        ·
          refine ⟨5046307983702914782497305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13456821289874439419992813 5046307983702914782497305)
          ·
            refine ⟨3784730987777186086872979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046307983702914782497305 3784730987777186086872979)
            ·
              refine ⟨5677096481665779130309469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784730987777186086872979 5677096481665779130309469)
              ·
                refine ⟨2128911180624667173866051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5677096481665779130309469 2128911180624667173866051)
                ·
                  refine ⟨3193366770937000760799077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128911180624667173866051 3193366770937000760799077)
                  ·
                    refine ⟨598756269550687642649827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193366770937000760799077 598756269550687642649827)
                    ·
                      rfl

theorem cell23_3498221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_3498221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498221 prefixEnd_3498221 := by exact prefixLift 3498221
  have htrace : WordTrace (prefixWord ++ tailWord_3498221) baseStart_3498221 baseEnd_3498221 := by
    simpa [prefixWord, tailWord_3498221, baseEnd_3498221] using wordTrace_append hprefix tailTrace_3498221
  have hstable : (prefixWord ++ tailWord_3498221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498221).length < 2 ^ (prefixWord ++ tailWord_3498221).sum := by decide
  have hdescent : baseEnd_3498221 < baseStart_3498221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498267 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 3, 2, 2]
def baseStart_3498267 : Nat := 118140960795 + 3498267 * 2 ^ 59
def prefixEnd_3498267 : Nat := 4983230072969 + 3 ^ 40 * 3498267 * 2
def baseEnd_3498267 : Nat := 1796292428762169747974269

theorem tailTrace_3498267 : CollatzResearch.WordTrace tailWord_3498267 prefixEnd_3498267 1796292428762169747974269 := by
  unfold tailWord_3498267
  simp only [CollatzResearch.WordTrace]
  refine ⟨127592279617383590282773055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85061519744922393521848703 127592279617383590282773055)
  ·
    refine ⟨191388419426075385424159583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127592279617383590282773055 191388419426075385424159583)
    ·
      refine ⟨287082629139113078136239375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191388419426075385424159583 287082629139113078136239375)
      ·
        refine ⟨430623943708669617204359063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287082629139113078136239375 430623943708669617204359063)
        ·
          refine ⟨645935915563004425806538595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430623943708669617204359063 645935915563004425806538595)
          ·
            refine ⟨968903873344506638709807893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645935915563004425806538595 968903873344506638709807893)
            ·
              refine ⟨45417369063023748689522245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 968903873344506638709807893 45417369063023748689522245)
              ·
                refine ⟨8515756699316952879285421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45417369063023748689522245 8515756699316952879285421)
                ·
                  refine ⟨3193408762243857329732033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8515756699316952879285421 3193408762243857329732033)
                  ·
                    refine ⟨2395056571682892997299025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193408762243857329732033 2395056571682892997299025)
                    ·
                      refine ⟨1796292428762169747974269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395056571682892997299025 1796292428762169747974269)
                      ·
                        rfl

theorem cell23_3498267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 3, 2, 2].length) (baseStart_3498267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498267 prefixEnd_3498267 := by exact prefixLift 3498267
  have htrace : WordTrace (prefixWord ++ tailWord_3498267) baseStart_3498267 baseEnd_3498267 := by
    simpa [prefixWord, tailWord_3498267, baseEnd_3498267] using wordTrace_append hprefix tailTrace_3498267
  have hstable : (prefixWord ++ tailWord_3498267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498267).length < 2 ^ (prefixWord ++ tailWord_3498267).sum := by decide
  have hdescent : baseEnd_3498267 < baseStart_3498267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498273 : List Nat := [1, 2, 3, 2, 1, 1, 4, 9]
def baseStart_3498273 : Nat := 118140960795 + 3498273 * 2 ^ 59
def prefixEnd_3498273 : Nat := 4983230072969 + 3 ^ 40 * 3498273 * 2
def baseEnd_3498273 : Nat := 66529463320225804611083

theorem tailTrace_3498273 : CollatzResearch.WordTrace tailWord_3498273 prefixEnd_3498273 66529463320225804611083 := by
  unfold tailWord_3498273
  simp only [CollatzResearch.WordTrace]
  refine ⟨127592498455361853307491473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85061665636907902204994315 127592498455361853307491473)
  ·
    refine ⟨95694373841521389980618605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127592498455361853307491473 95694373841521389980618605)
    ·
      refine ⟨35885390190570521242731977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95694373841521389980618605 35885390190570521242731977)
      ·
        refine ⟨26914042642927890932048983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35885390190570521242731977 26914042642927890932048983)
        ·
          refine ⟨40371063964391836398073475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914042642927890932048983 40371063964391836398073475)
          ·
            refine ⟨60556595946587754597110213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40371063964391836398073475 60556595946587754597110213)
            ·
              refine ⟨11354361739985203986958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60556595946587754597110213 11354361739985203986958165)
              ·
                refine ⟨66529463320225804611083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11354361739985203986958165 66529463320225804611083)
                ·
                  rfl

theorem cell23_3498273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 9].length) (baseStart_3498273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498273 prefixEnd_3498273 := by exact prefixLift 3498273
  have htrace : WordTrace (prefixWord ++ tailWord_3498273) baseStart_3498273 baseEnd_3498273 := by
    simpa [prefixWord, tailWord_3498273, baseEnd_3498273] using wordTrace_append hprefix tailTrace_3498273
  have hstable : (prefixWord ++ tailWord_3498273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498273).length < 2 ^ (prefixWord ++ tailWord_3498273).sum := by decide
  have hdescent : baseEnd_3498273 < baseStart_3498273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498290 : List Nat := [3, 2, 1, 1, 6, 10]
def baseStart_3498290 : Nat := 118140960795 + 3498290 * 2 ^ 59
def prefixEnd_3498290 : Nat := 4983230072969 + 3 ^ 40 * 3498290 * 2
def baseEnd_3498290 : Nat := 7392198513651124106941

theorem tailTrace_3498290 : CollatzResearch.WordTrace tailWord_3498290 prefixEnd_3498290 7392198513651124106941 := by
  unfold tailWord_3498290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898279624075066302715081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85062078997533510140573549 31898279624075066302715081)
  ·
    refine ⟨23923709718056299727036311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31898279624075066302715081 23923709718056299727036311)
    ·
      refine ⟨35885564577084449590554467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23923709718056299727036311 35885564577084449590554467)
      ·
        refine ⟨53828346865626674385831701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35885564577084449590554467 53828346865626674385831701)
        ·
          refine ⟨2523203759326250361835861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53828346865626674385831701 2523203759326250361835861)
          ·
            refine ⟨7392198513651124106941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2523203759326250361835861 7392198513651124106941)
            ·
              rfl

theorem cell23_3498290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 10].length) (baseStart_3498290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498290 prefixEnd_3498290 := by exact prefixLift 3498290
  have htrace : WordTrace (prefixWord ++ tailWord_3498290) baseStart_3498290 baseEnd_3498290 := by
    simpa [prefixWord, tailWord_3498290, baseEnd_3498290] using wordTrace_append hprefix tailTrace_3498290
  have hstable : (prefixWord ++ tailWord_3498290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498290).length < 2 ^ (prefixWord ++ tailWord_3498290).sum := by decide
  have hdescent : baseEnd_3498290 < baseStart_3498290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498300 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_3498300 : Nat := 118140960795 + 3498300 * 2 ^ 59
def prefixEnd_3498300 : Nat := 4983230072969 + 3 ^ 40 * 3498300 * 2
def baseEnd_3498300 : Nat := 1796309373623768118861617

theorem tailTrace_3498300 : CollatzResearch.WordTrace tailWord_3498300 prefixEnd_3498300 1796309373623768118861617 := by
  unfold tailWord_3498300
  simp only [CollatzResearch.WordTrace]
  refine ⟨63796741613132018459362177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85062322150842691279149569 63796741613132018459362177)
  ·
    refine ⟨47847556209849013844521633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63796741613132018459362177 47847556209849013844521633)
    ·
      refine ⟨35885667157386760383391225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47847556209849013844521633 35885667157386760383391225)
      ·
        refine ⟨26914250368040070287543419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35885667157386760383391225 26914250368040070287543419)
        ·
          refine ⟨40371375552060105431315129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26914250368040070287543419 40371375552060105431315129)
          ·
            refine ⟨30278531664045079073486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40371375552060105431315129 30278531664045079073486347)
            ·
              refine ⟨45417797496067618610229521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30278531664045079073486347 45417797496067618610229521)
              ·
                refine ⟨34063348122050713957672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45417797496067618610229521 34063348122050713957672141)
                ·
                  refine ⟨12773755545769017734127053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34063348122050713957672141 12773755545769017734127053)
                  ·
                    refine ⟨4790158329663381650297645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12773755545769017734127053 4790158329663381650297645)
                    ·
                      refine ⟨1796309373623768118861617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790158329663381650297645 1796309373623768118861617)
                      ·
                        rfl

theorem cell23_3498300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_3498300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498300 prefixEnd_3498300 := by exact prefixLift 3498300
  have htrace : WordTrace (prefixWord ++ tailWord_3498300) baseStart_3498300 baseEnd_3498300 := by
    simpa [prefixWord, tailWord_3498300, baseEnd_3498300] using wordTrace_append hprefix tailTrace_3498300
  have hstable : (prefixWord ++ tailWord_3498300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498300).length < 2 ^ (prefixWord ++ tailWord_3498300).sum := by decide
  have hdescent : baseEnd_3498300 < baseStart_3498300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498303 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 9]
def baseStart_3498303 : Nat := 118140960795 + 3498303 * 2 ^ 59
def prefixEnd_3498303 : Nat := 4983230072969 + 3 ^ 40 * 3498303 * 2
def baseEnd_3498303 : Nat := 598770304688577202374701

theorem tailTrace_3498303 : CollatzResearch.WordTrace tailWord_3498303 prefixEnd_3498303 598770304688577202374701 := by
  unfold tailWord_3498303
  simp only [CollatzResearch.WordTrace]
  refine ⟨127593592645253168431083563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85062395096835445620722375 127593592645253168431083563)
  ·
    refine ⟨191390388967879752646625345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127593592645253168431083563 191390388967879752646625345)
    ·
      refine ⟨143542791725909814484969009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191390388967879752646625345 143542791725909814484969009)
      ·
        refine ⟨107657093794432360863726757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143542791725909814484969009 107657093794432360863726757)
        ·
          refine ⟨20185705086456067661948767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107657093794432360863726757 20185705086456067661948767)
          ·
            refine ⟨30278557629684101492923151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185705086456067661948767 30278557629684101492923151)
            ·
              refine ⟨45417836444526152239384727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30278557629684101492923151 45417836444526152239384727)
              ·
                refine ⟨68126754666789228359077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45417836444526152239384727 68126754666789228359077091)
                ·
                  refine ⟨102190132000183842538615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68126754666789228359077091 102190132000183842538615637)
                  ·
                    refine ⟨598770304688577202374701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 102190132000183842538615637 598770304688577202374701)
                    ·
                      rfl

theorem cell23_3498303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_3498303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498303 prefixEnd_3498303 := by exact prefixLift 3498303
  have htrace : WordTrace (prefixWord ++ tailWord_3498303) baseStart_3498303 baseEnd_3498303 := by
    simpa [prefixWord, tailWord_3498303, baseEnd_3498303] using wordTrace_append hprefix tailTrace_3498303
  have hstable : (prefixWord ++ tailWord_3498303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498303).length < 2 ^ (prefixWord ++ tailWord_3498303).sum := by decide
  have hdescent : baseEnd_3498303 < baseStart_3498303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498313 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_3498313 : Nat := 118140960795 + 3498313 * 2 ^ 59
def prefixEnd_3498313 : Nat := 4983230072969 + 3 ^ 40 * 3498313 * 2
def baseEnd_3498313 : Nat := 1796316048872276567999057

theorem tailTrace_3498313 : CollatzResearch.WordTrace tailWord_3498313 prefixEnd_3498313 1796316048872276567999057 := by
  unfold tailWord_3498313
  simp only [CollatzResearch.WordTrace]
  refine ⟨127593957375216940138947593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85062638250144626759298395 127593957375216940138947593)
  ·
    refine ⟨95695468031412705104210695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127593957375216940138947593 95695468031412705104210695)
    ·
      refine ⟨143543202047119057656316043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95695468031412705104210695 143543202047119057656316043)
      ·
        refine ⟨215314803070678586484474065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143543202047119057656316043 215314803070678586484474065)
        ·
          refine ⟨161486102303008939863355549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215314803070678586484474065 161486102303008939863355549)
          ·
            refine ⟨60557288363628352448758331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161486102303008939863355549 60557288363628352448758331)
            ·
              refine ⟨90835932545442528673137497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60557288363628352448758331 90835932545442528673137497)
              ·
                refine ⟨68126949409081896504853123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90835932545442528673137497 68126949409081896504853123)
                ·
                  refine ⟨102190424113622844757279685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68126949409081896504853123 102190424113622844757279685)
                  ·
                    refine ⟨19160704521304283391989941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102190424113622844757279685 19160704521304283391989941)
                    ·
                      refine ⟨1796316048872276567999057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19160704521304283391989941 1796316048872276567999057)
                      ·
                        rfl

theorem cell23_3498313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_3498313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498313 prefixEnd_3498313 := by exact prefixLift 3498313
  have htrace : WordTrace (prefixWord ++ tailWord_3498313) baseStart_3498313 baseEnd_3498313 := by
    simpa [prefixWord, tailWord_3498313, baseEnd_3498313] using wordTrace_append hprefix tailTrace_3498313
  have hstable : (prefixWord ++ tailWord_3498313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498313).length < 2 ^ (prefixWord ++ tailWord_3498313).sum := by decide
  have hdescent : baseEnd_3498313 < baseStart_3498313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498327 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_3498327 : Nat := 118140960795 + 3498327 * 2 ^ 59
def prefixEnd_3498327 : Nat := 4983230072969 + 3 ^ 40 * 3498327 * 2
def baseEnd_3498327 : Nat := 1796323237601439513223993

theorem tailTrace_3498327 : CollatzResearch.WordTrace tailWord_3498327 prefixEnd_3498327 1796323237601439513223993 := by
  unfold tailWord_3498327
  simp only [CollatzResearch.WordTrace]
  refine ⟨127594467997166220529957235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85062978664777480353304823 127594467997166220529957235)
  ·
    refine ⟨191391701995749330794935853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127594467997166220529957235 191391701995749330794935853)
    ·
      refine ⟨71771888248405999048100945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191391701995749330794935853 71771888248405999048100945)
      ·
        refine ⟨53828916186304499286075709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71771888248405999048100945 53828916186304499286075709)
        ·
          refine ⟨20185843569864187232278391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53828916186304499286075709 20185843569864187232278391)
          ·
            refine ⟨30278765354796280848417587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185843569864187232278391 30278765354796280848417587)
            ·
              refine ⟨45418148032194421272626381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30278765354796280848417587 45418148032194421272626381)
              ·
                refine ⟨17031805512072907977234893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45418148032194421272626381 17031805512072907977234893)
                ·
                  refine ⟨6386927067027340491463085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17031805512072907977234893 6386927067027340491463085)
                  ·
                    refine ⟨2395097650135252684298657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6386927067027340491463085 2395097650135252684298657)
                    ·
                      refine ⟨1796323237601439513223993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395097650135252684298657 1796323237601439513223993)
                      ·
                        rfl

theorem cell23_3498327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_3498327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498327 prefixEnd_3498327 := by exact prefixLift 3498327
  have htrace : WordTrace (prefixWord ++ tailWord_3498327) baseStart_3498327 baseEnd_3498327 := by
    simpa [prefixWord, tailWord_3498327, baseEnd_3498327] using wordTrace_append hprefix tailTrace_3498327
  have hstable : (prefixWord ++ tailWord_3498327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498327).length < 2 ^ (prefixWord ++ tailWord_3498327).sum := by decide
  have hdescent : baseEnd_3498327 < baseStart_3498327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498378 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3498378 : Nat := 118140960795 + 3498378 * 2 ^ 59
def prefixEnd_3498378 : Nat := 4983230072969 + 3 ^ 40 * 3498378 * 2
def baseEnd_3498378 : Nat := 1796349425114818813686259

theorem tailTrace_3498378 : CollatzResearch.WordTrace tailWord_3498378 prefixEnd_3498378 1796349425114818813686259 := by
  unfold tailWord_3498378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31899082029995364060015947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85064218746654304160042525 31899082029995364060015947)
  ·
    refine ⟨47848623044993046090023921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31899082029995364060015947 47848623044993046090023921)
    ·
      refine ⟨35886467283744784567517941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47848623044993046090023921 35886467283744784567517941)
      ·
        refine ⟨3364356307851073553204807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35886467283744784567517941 3364356307851073553204807)
        ·
          refine ⟨5046534461776610329807211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364356307851073553204807 5046534461776610329807211)
          ·
            refine ⟨7569801692664915494710817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046534461776610329807211 7569801692664915494710817)
            ·
              refine ⟨5677351269498686621033113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7569801692664915494710817 5677351269498686621033113)
              ·
                refine ⟨4258013452124014965774835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677351269498686621033113 4258013452124014965774835)
                ·
                  refine ⟨6387020178186022448662253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258013452124014965774835 6387020178186022448662253)
                  ·
                    refine ⟨2395132566819758418248345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6387020178186022448662253 2395132566819758418248345)
                    ·
                      refine ⟨1796349425114818813686259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395132566819758418248345 1796349425114818813686259)
                      ·
                        rfl

theorem cell23_3498378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3498378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498378 prefixEnd_3498378 := by exact prefixLift 3498378
  have htrace : WordTrace (prefixWord ++ tailWord_3498378) baseStart_3498378 baseEnd_3498378 := by
    simpa [prefixWord, tailWord_3498378, baseEnd_3498378] using wordTrace_append hprefix tailTrace_3498378
  have hstable : (prefixWord ++ tailWord_3498378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498378).length < 2 ^ (prefixWord ++ tailWord_3498378).sum := by decide
  have hdescent : baseEnd_3498378 < baseStart_3498378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498380 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 7]
def baseStart_3498380 : Nat := 118140960795 + 3498380 * 2 ^ 59
def prefixEnd_3498380 : Nat := 4983230072969 + 3 ^ 40 * 3498380 * 2
def baseEnd_3498380 : Nat := 199594494675125311762361

theorem tailTrace_3498380 : CollatzResearch.WordTrace tailWord_3498380 prefixEnd_3498380 199594494675125311762361 := by
  unfold tailWord_3498380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63798200532987105290818297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85064267377316140387757729 63798200532987105290818297)
  ·
    refine ⟨47848650399740328968113723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63798200532987105290818297 47848650399740328968113723)
    ·
      refine ⟨71772975599610493452170585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47848650399740328968113723 71772975599610493452170585)
      ·
        refine ⟨53829731699707870089127939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71772975599610493452170585 53829731699707870089127939)
        ·
          refine ⟨80744597549561805133691909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53829731699707870089127939 80744597549561805133691909)
          ·
            refine ⟨15139612040542838462567233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80744597549561805133691909 15139612040542838462567233)
            ·
              refine ⟨11354709030407128846925425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15139612040542838462567233 11354709030407128846925425)
              ·
                refine ⟨8516031772805346635194069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11354709030407128846925425 8516031772805346635194069)
                ·
                  refine ⟨199594494675125311762361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8516031772805346635194069 199594494675125311762361)
                  ·
                    rfl

theorem cell23_3498380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_3498380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498380 prefixEnd_3498380 := by exact prefixLift 3498380
  have htrace : WordTrace (prefixWord ++ tailWord_3498380) baseStart_3498380 baseEnd_3498380 := by
    simpa [prefixWord, tailWord_3498380, baseEnd_3498380] using wordTrace_append hprefix tailTrace_3498380
  have hstable : (prefixWord ++ tailWord_3498380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498380).length < 2 ^ (prefixWord ++ tailWord_3498380).sum := by decide
  have hdescent : baseEnd_3498380 < baseStart_3498380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498444 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_3498444 : Nat := 118140960795 + 3498444 * 2 ^ 59
def prefixEnd_3498444 : Nat := 4983230072969 + 3 ^ 40 * 3498444 * 2
def baseEnd_3498444 : Nat := 598794438279338518486985

theorem tailTrace_3498444 : CollatzResearch.WordTrace tailWord_3498444 prefixEnd_3498444 598794438279338518486985 := by
  unfold tailWord_3498444
  simp only [CollatzResearch.WordTrace]
  refine ⟨63799367668871174755983193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85065823558494899674644257 63799367668871174755983193)
  ·
    refine ⟨47849525751653381066987395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63799367668871174755983193 47849525751653381066987395)
    ·
      refine ⟨71774288627480071600481093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47849525751653381066987395 71774288627480071600481093)
      ·
        refine ⟨13457679117652513425090205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71774288627480071600481093 13457679117652513425090205)
        ·
          refine ⟨5046629669119692534408827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13457679117652513425090205 5046629669119692534408827)
          ·
            refine ⟨7569944503679538801613241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046629669119692534408827 7569944503679538801613241)
            ·
              refine ⟨5677458377759654101209931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7569944503679538801613241 5677458377759654101209931)
              ·
                refine ⟨8516187566639481151814897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677458377759654101209931 8516187566639481151814897)
                ·
                  refine ⟨6387140674979610863861173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516187566639481151814897 6387140674979610863861173)
                  ·
                    refine ⟨598794438279338518486985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6387140674979610863861173 598794438279338518486985)
                    ·
                      rfl

theorem cell23_3498444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_3498444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498444 prefixEnd_3498444 := by exact prefixLift 3498444
  have htrace : WordTrace (prefixWord ++ tailWord_3498444) baseStart_3498444 baseEnd_3498444 := by
    simpa [prefixWord, tailWord_3498444, baseEnd_3498444] using wordTrace_append hprefix tailTrace_3498444
  have hstable : (prefixWord ++ tailWord_3498444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498444).length < 2 ^ (prefixWord ++ tailWord_3498444).sum := by decide
  have hdescent : baseEnd_3498444 < baseStart_3498444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 4, 2]
def baseStart_3498447 : Nat := 118140960795 + 3498447 * 2 ^ 59
def prefixEnd_3498447 : Nat := 4983230072969 + 3 ^ 40 * 3498447 * 2
def baseEnd_3498447 : Nat := 1796384855279979043723441

theorem tailTrace_3498447 : CollatzResearch.WordTrace tailWord_3498447 prefixEnd_3498447 1796384855279979043723441 := by
  unfold tailWord_3498447
  simp only [CollatzResearch.WordTrace]
  refine ⟨127598844756731481024325595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85065896504487654016217063 127598844756731481024325595)
  ·
    refine ⟨191398267135097221536488393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127598844756731481024325595 191398267135097221536488393)
    ·
      refine ⟨143548700351322916152366295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191398267135097221536488393 143548700351322916152366295)
      ·
        refine ⟨215323050526984374228549443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143548700351322916152366295 215323050526984374228549443)
        ·
          refine ⟨322984575790476561342824165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215323050526984374228549443 322984575790476561342824165)
          ·
            refine ⟨60559607960714355251779531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322984575790476561342824165 60559607960714355251779531)
            ·
              refine ⟨90839411941071532877669297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60559607960714355251779531 90839411941071532877669297)
              ·
                refine ⟨68129558955803649658251973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90839411941071532877669297 68129558955803649658251973)
                ·
                  refine ⟨12774292304213184310922245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68129558955803649658251973 12774292304213184310922245)
                  ·
                    refine ⟨2395179807039972058297921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12774292304213184310922245 2395179807039972058297921)
                    ·
                      refine ⟨1796384855279979043723441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395179807039972058297921 1796384855279979043723441)
                      ·
                        rfl

theorem cell23_3498447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4, 2].length) (baseStart_3498447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498447 prefixEnd_3498447 := by exact prefixLift 3498447
  have htrace : WordTrace (prefixWord ++ tailWord_3498447) baseStart_3498447 baseEnd_3498447 := by
    simpa [prefixWord, tailWord_3498447, baseEnd_3498447] using wordTrace_append hprefix tailTrace_3498447
  have hstable : (prefixWord ++ tailWord_3498447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498447).length < 2 ^ (prefixWord ++ tailWord_3498447).sum := by decide
  have hdescent : baseEnd_3498447 < baseStart_3498447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3498490 : Nat := 118140960795 + 3498490 * 2 ^ 59
def prefixEnd_3498490 : Nat := 4983230072969 + 3 ^ 40 * 3498490 * 2
def baseEnd_3498490 : Nat := 1796406934948122375485743

theorem tailTrace_3498490 : CollatzResearch.WordTrace tailWord_3498490 prefixEnd_3498490 1796406934948122375485743 := by
  unfold tailWord_3498490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900103273893924842035231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85066942063717132912093949 31900103273893924842035231)
  ·
    refine ⟨47850154910840887263052847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31900103273893924842035231 47850154910840887263052847)
    ·
      refine ⟨71775232366261330894579271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47850154910840887263052847 71775232366261330894579271)
      ·
        refine ⟨107662848549391996341868907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71775232366261330894579271 107662848549391996341868907)
        ·
          refine ⟨161494272824087994512803361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107662848549391996341868907 161494272824087994512803361)
          ·
            refine ⟨121120704618065995884602521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161494272824087994512803361 121120704618065995884602521)
            ·
              refine ⟨90840528463549496913451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121120704618065995884602521 90840528463549496913451891)
              ·
                refine ⟨136260792695324245370177837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90840528463549496913451891 136260792695324245370177837)
                ·
                  refine ⟨51097797260746592013816689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136260792695324245370177837 51097797260746592013816689)
                  ·
                    refine ⟨38323347945559944010362517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51097797260746592013816689 38323347945559944010362517)
                    ·
                      refine ⟨1796406934948122375485743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38323347945559944010362517 1796406934948122375485743)
                      ·
                        rfl

theorem cell23_3498490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3498490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498490 prefixEnd_3498490 := by exact prefixLift 3498490
  have htrace : WordTrace (prefixWord ++ tailWord_3498490) baseStart_3498490 baseEnd_3498490 := by
    simpa [prefixWord, tailWord_3498490, baseEnd_3498490] using wordTrace_append hprefix tailTrace_3498490
  have hstable : (prefixWord ++ tailWord_3498490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498490).length < 2 ^ (prefixWord ++ tailWord_3498490).sum := by decide
  have hdescent : baseEnd_3498490 < baseStart_3498490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498498 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3498498 : Nat := 118140960795 + 3498498 * 2 ^ 59
def prefixEnd_3498498 : Nat := 4983230072969 + 3 ^ 40 * 3498498 * 2
def baseEnd_3498498 : Nat := 1796411042793358344185707

theorem tailTrace_3498498 : CollatzResearch.WordTrace tailWord_3498498 prefixEnd_3498498 1796411042793358344185707 := by
  unfold tailWord_3498498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900176219886679183608037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85067136586364477822954765 31900176219886679183608037)
  ·
    refine ⟨5981283041228752346926507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31900176219886679183608037 5981283041228752346926507)
    ·
      refine ⟨8971924561843128520389761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981283041228752346926507 8971924561843128520389761)
      ·
        refine ⟨6728943421382346390292321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8971924561843128520389761 6728943421382346390292321)
        ·
          refine ⟨5046707566036759792719241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728943421382346390292321 5046707566036759792719241)
          ·
            refine ⟨3785030674527569844539431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046707566036759792719241 3785030674527569844539431)
            ·
              refine ⟨5677546011791354766809147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785030674527569844539431 5677546011791354766809147)
              ·
                refine ⟨8516319017687032150213721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677546011791354766809147 8516319017687032150213721)
                ·
                  refine ⟨6387239263265274112660291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516319017687032150213721 6387239263265274112660291)
                  ·
                    refine ⟨9580858894897911168990437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6387239263265274112660291 9580858894897911168990437)
                    ·
                      refine ⟨1796411042793358344185707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9580858894897911168990437 1796411042793358344185707)
                      ·
                        rfl

theorem cell23_3498498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3498498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498498 prefixEnd_3498498 := by exact prefixLift 3498498
  have htrace : WordTrace (prefixWord ++ tailWord_3498498) baseStart_3498498 baseEnd_3498498 := by
    simpa [prefixWord, tailWord_3498498, baseEnd_3498498] using wordTrace_append hprefix tailTrace_3498498
  have hstable : (prefixWord ++ tailWord_3498498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498498).length < 2 ^ (prefixWord ++ tailWord_3498498).sum := by decide
  have hdescent : baseEnd_3498498 < baseStart_3498498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498531 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 3]
def baseStart_3498531 : Nat := 118140960795 + 3498531 * 2 ^ 59
def prefixEnd_3498531 : Nat := 4983230072969 + 3 ^ 40 * 3498531 * 2
def baseEnd_3498531 : Nat := 1796427987654956715073055

theorem tailTrace_3498531 : CollatzResearch.WordTrace tailWord_3498531 prefixEnd_3498531 1796427987654956715073055 := by
  unfold tailWord_3498531
  simp only [CollatzResearch.WordTrace]
  refine ⟨127601908488427163370383447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85067938992284775580255631 127601908488427163370383447)
  ·
    refine ⟨191402862732640745055575171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127601908488427163370383447 191402862732640745055575171)
    ·
      refine ⟨287104294098961117583362757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191402862732640745055575171 287104294098961117583362757)
      ·
        refine ⟨53832055143555209546880517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287104294098961117583362757 53832055143555209546880517)
        ·
          refine ⟨10093510339416601790040097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53832055143555209546880517 10093510339416601790040097)
          ·
            refine ⟨7570132754562451342530073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10093510339416601790040097 7570132754562451342530073)
            ·
              refine ⟨5677599565921838506897555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7570132754562451342530073 5677599565921838506897555)
              ·
                refine ⟨8516399348882757760346333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677599565921838506897555 8516399348882757760346333)
                ·
                  refine ⟨3193649755831034160129875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8516399348882757760346333 3193649755831034160129875)
                  ·
                    refine ⟨4790474633746551240194813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3193649755831034160129875 4790474633746551240194813)
                    ·
                      refine ⟨1796427987654956715073055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790474633746551240194813 1796427987654956715073055)
                      ·
                        rfl

theorem cell23_3498531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_3498531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498531 prefixEnd_3498531 := by exact prefixLift 3498531
  have htrace : WordTrace (prefixWord ++ tailWord_3498531) baseStart_3498531 baseEnd_3498531 := by
    simpa [prefixWord, tailWord_3498531, baseEnd_3498531] using wordTrace_append hprefix tailTrace_3498531
  have hstable : (prefixWord ++ tailWord_3498531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498531).length < 2 ^ (prefixWord ++ tailWord_3498531).sum := by decide
  have hdescent : baseEnd_3498531 < baseStart_3498531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498554 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_3498554 : Nat := 118140960795 + 3498554 * 2 ^ 59
def prefixEnd_3498554 : Nat := 4983230072969 + 3 ^ 40 * 3498554 * 2
def baseEnd_3498554 : Nat := 1796439797710010125085449

theorem tailTrace_3498554 : CollatzResearch.WordTrace tailWord_3498554 prefixEnd_3498554 1796439797710010125085449 := by
  unfold tailWord_3498554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31900686841835959574617679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85068498244895892198980477 31900686841835959574617679)
  ·
    refine ⟨47851030262753939361926519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31900686841835959574617679 47851030262753939361926519)
    ·
      refine ⟨71776545394130909042889779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47851030262753939361926519 71776545394130909042889779)
      ·
        refine ⟨107664818091196363564334669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71776545394130909042889779 107664818091196363564334669)
        ·
          refine ⟨40374306784198636336625501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107664818091196363564334669 40374306784198636336625501)
          ·
            refine ⟨15140365044074488626234563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40374306784198636336625501 15140365044074488626234563)
            ·
              refine ⟨22710547566111732939351845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15140365044074488626234563 22710547566111732939351845)
              ·
                refine ⟨4258227668645949926128471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22710547566111732939351845 4258227668645949926128471)
                ·
                  refine ⟨6387341502968924889192707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258227668645949926128471 6387341502968924889192707)
                  ·
                    refine ⟨9581012254453387333789061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6387341502968924889192707 9581012254453387333789061)
                    ·
                      refine ⟨1796439797710010125085449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9581012254453387333789061 1796439797710010125085449)
                      ·
                        rfl

theorem cell23_3498554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_3498554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498554 prefixEnd_3498554 := by exact prefixLift 3498554
  have htrace : WordTrace (prefixWord ++ tailWord_3498554) baseStart_3498554 baseEnd_3498554 := by
    simpa [prefixWord, tailWord_3498554, baseEnd_3498554] using wordTrace_append hprefix tailTrace_3498554
  have hstable : (prefixWord ++ tailWord_3498554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498554).length < 2 ^ (prefixWord ++ tailWord_3498554).sum := by decide
  have hdescent : baseEnd_3498554 < baseStart_3498554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498577 : List Nat := [1, 2, 2, 1, 3, 5, 9]
def baseStart_3498577 : Nat := 118140960795 + 3498577 * 2 ^ 59
def prefixEnd_3498577 : Nat := 4983230072969 + 3 ^ 40 * 3498577 * 2
def baseEnd_3498577 : Nat := 22178414910679796729603

theorem tailTrace_3498577 : CollatzResearch.WordTrace tailWord_3498577 prefixEnd_3498577 22178414910679796729603 := by
  unfold tailWord_3498577
  simp only [CollatzResearch.WordTrace]
  refine ⟨127603586246260513226557985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85069057497507008817705323 127603586246260513226557985)
  ·
    refine ⟨95702689684695384919918489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127603586246260513226557985 95702689684695384919918489)
    ·
      refine ⟨71777017263521538689938867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95702689684695384919918489 71777017263521538689938867)
      ·
        refine ⟨107665525895282308034908301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71777017263521538689938867 107665525895282308034908301)
        ·
          refine ⟨40374572210730865513090613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107665525895282308034908301 40374572210730865513090613)
          ·
            refine ⟨3785116144756018641852245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40374572210730865513090613 3785116144756018641852245)
            ·
              refine ⟨22178414910679796729603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3785116144756018641852245 22178414910679796729603)
              ·
                rfl

theorem cell23_3498577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 9].length) (baseStart_3498577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498577 prefixEnd_3498577 := by exact prefixLift 3498577
  have htrace : WordTrace (prefixWord ++ tailWord_3498577) baseStart_3498577 baseEnd_3498577 := by
    simpa [prefixWord, tailWord_3498577, baseEnd_3498577] using wordTrace_append hprefix tailTrace_3498577
  have hstable : (prefixWord ++ tailWord_3498577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498577).length < 2 ^ (prefixWord ++ tailWord_3498577).sum := by decide
  have hdescent : baseEnd_3498577 < baseStart_3498577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498608 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_3498608 : Nat := 118140960795 + 3498608 * 2 ^ 59
def prefixEnd_3498608 : Nat := 4983230072969 + 3 ^ 40 * 3498608 * 2
def baseEnd_3498608 : Nat := 1796467525665352913810201

theorem tailTrace_3498608 : CollatzResearch.WordTrace tailWord_3498608 prefixEnd_3498608 1796467525665352913810201 := by
  unfold tailWord_3498608
  simp only [CollatzResearch.WordTrace]
  refine ⟨63802358454574102760468239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85069811272765470347290985 63802358454574102760468239)
  ·
    refine ⟨95703537681861154140702359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63802358454574102760468239 95703537681861154140702359)
    ·
      refine ⟨143555306522791731211053539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95703537681861154140702359 143555306522791731211053539)
      ·
        refine ⟨215332959784187596816580309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143555306522791731211053539 215332959784187596816580309)
        ·
          refine ⟨5046866244941896800388601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 215332959784187596816580309 5046866244941896800388601)
          ·
            refine ⟨3785149683706422600291451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5046866244941896800388601 3785149683706422600291451)
            ·
              refine ⟨5677724525559633900437177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785149683706422600291451 5677724525559633900437177)
              ·
                refine ⟨4258293394169725425327883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677724525559633900437177 4258293394169725425327883)
                ·
                  refine ⟨6387440091254588137991825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258293394169725425327883 6387440091254588137991825)
                  ·
                    refine ⟨4790580068440941103493869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6387440091254588137991825 4790580068440941103493869)
                    ·
                      refine ⟨1796467525665352913810201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790580068440941103493869 1796467525665352913810201)
                      ·
                        rfl

theorem cell23_3498608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_3498608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498608 prefixEnd_3498608 := by exact prefixLift 3498608
  have htrace : WordTrace (prefixWord ++ tailWord_3498608) baseStart_3498608 baseEnd_3498608 := by
    simpa [prefixWord, tailWord_3498608, baseEnd_3498608] using wordTrace_append hprefix tailTrace_3498608
  have hstable : (prefixWord ++ tailWord_3498608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498608).length < 2 ^ (prefixWord ++ tailWord_3498608).sum := by decide
  have hdescent : baseEnd_3498608 < baseStart_3498608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498621 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_3498621 : Nat := 118140960795 + 3498621 * 2 ^ 59
def prefixEnd_3498621 : Nat := 4983230072969 + 3 ^ 40 * 3498621 * 2
def baseEnd_3498621 : Nat := 1796474200913861362947641

theorem tailTrace_3498621 : CollatzResearch.WordTrace tailWord_3498621 prefixEnd_3498621 1796474200913861362947641 := by
  unfold tailWord_3498621
  simp only [CollatzResearch.WordTrace]
  refine ⟨127605191058101108741159717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85070127372067405827439811 127605191058101108741159717)
  ·
    refine ⟨23925973323393957888967447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127605191058101108741159717 23925973323393957888967447)
    ·
      refine ⟨35888959985090936833451171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23925973323393957888967447 35888959985090936833451171)
      ·
        refine ⟨53833439977636405250176757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35888959985090936833451171 53833439977636405250176757)
        ·
          refine ⟨5046884997903412992204071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53833439977636405250176757 5046884997903412992204071)
          ·
            refine ⟨7570327496855119488306107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046884997903412992204071 7570327496855119488306107)
            ·
              refine ⟨11355491245282679232459161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570327496855119488306107 11355491245282679232459161)
              ·
                refine ⟨8516618433962009424344371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11355491245282679232459161 8516618433962009424344371)
                ·
                  refine ⟨12774927650943014136516557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8516618433962009424344371 12774927650943014136516557)
                  ·
                    refine ⟨4790597869103630301193709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12774927650943014136516557 4790597869103630301193709)
                    ·
                      refine ⟨1796474200913861362947641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790597869103630301193709 1796474200913861362947641)
                      ·
                        rfl

theorem cell23_3498621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_3498621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498621 prefixEnd_3498621 := by exact prefixLift 3498621
  have htrace : WordTrace (prefixWord ++ tailWord_3498621) baseStart_3498621 baseEnd_3498621 := by
    simpa [prefixWord, tailWord_3498621, baseEnd_3498621] using wordTrace_append hprefix tailTrace_3498621
  have hstable : (prefixWord ++ tailWord_3498621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498621).length < 2 ^ (prefixWord ++ tailWord_3498621).sum := by decide
  have hdescent : baseEnd_3498621 < baseStart_3498621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498638 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3498638 : Nat := 118140960795 + 3498638 * 2 ^ 59
def prefixEnd_3498638 : Nat := 4983230072969 + 3 ^ 40 * 3498638 * 2
def baseEnd_3498638 : Nat := 1796482930084987796435063

theorem tailTrace_3498638 : CollatzResearch.WordTrace tailWord_3498638 prefixEnd_3498638 1796482930084987796435063 := by
  unfold tailWord_3498638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950726387379940080566071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85070540732693013763019045 15950726387379940080566071)
  ·
    refine ⟨23926089581069910120849107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950726387379940080566071 23926089581069910120849107)
    ·
      refine ⟨35889134371604865181273661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23926089581069910120849107 35889134371604865181273661)
      ·
        refine ⟨13458425389351824442977623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35889134371604865181273661 13458425389351824442977623)
        ·
          refine ⟨20187638084027736664466435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13458425389351824442977623 20187638084027736664466435)
          ·
            refine ⟨30281457126041604996699653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20187638084027736664466435 30281457126041604996699653)
            ·
              refine ⟨5677773211132800936881185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30281457126041604996699653 5677773211132800936881185)
              ·
                refine ⟨4258329908349600702660889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677773211132800936881185 4258329908349600702660889)
                ·
                  refine ⟨3193747431262200526995667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258329908349600702660889 3193747431262200526995667)
                  ·
                    refine ⟨4790621146893300790493501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3193747431262200526995667 4790621146893300790493501)
                    ·
                      refine ⟨1796482930084987796435063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790621146893300790493501 1796482930084987796435063)
                      ·
                        rfl

theorem cell23_3498638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3498638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498638 prefixEnd_3498638 := by exact prefixLift 3498638
  have htrace : WordTrace (prefixWord ++ tailWord_3498638) baseStart_3498638 baseEnd_3498638 := by
    simpa [prefixWord, tailWord_3498638, baseEnd_3498638] using wordTrace_append hprefix tailTrace_3498638
  have hstable : (prefixWord ++ tailWord_3498638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498638).length < 2 ^ (prefixWord ++ tailWord_3498638).sum := by decide
  have hdescent : baseEnd_3498638 < baseStart_3498638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498661 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_3498661 : Nat := 118140960795 + 3498661 * 2 ^ 59
def prefixEnd_3498661 : Nat := 4983230072969 + 3 ^ 40 * 3498661 * 2
def baseEnd_3498661 : Nat := 1796494740140041206447457

theorem tailTrace_3498661 : CollatzResearch.WordTrace tailWord_3498661 prefixEnd_3498661 1796494740140041206447457 := by
  unfold tailWord_3498661
  simp only [CollatzResearch.WordTrace]
  refine ⟨127606649977956195572615837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85071099985304130381743891 127606649977956195572615837)
  ·
    refine ⟨47852493741733573339730939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127606649977956195572615837 47852493741733573339730939)
    ·
      refine ⟨71778740612600360009596409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47852493741733573339730939 71778740612600360009596409)
      ·
        refine ⟨53834055459450270007197307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71778740612600360009596409 53834055459450270007197307)
        ·
          refine ⟨80751083189175405010795961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53834055459450270007197307 80751083189175405010795961)
          ·
            refine ⟨60563312391881553758096971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80751083189175405010795961 60563312391881553758096971)
            ·
              refine ⟨90844968587822330637145457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60563312391881553758096971 90844968587822330637145457)
              ·
                refine ⟨68133726440866747977859093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90844968587822330637145457 68133726440866747977859093)
                ·
                  refine ⟨3193768426915628811462145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68133726440866747977859093 3193768426915628811462145)
                  ·
                    refine ⟨2395326320186721608596609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3193768426915628811462145 2395326320186721608596609)
                    ·
                      refine ⟨1796494740140041206447457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395326320186721608596609 1796494740140041206447457)
                      ·
                        rfl

theorem cell23_3498661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_3498661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498661 prefixEnd_3498661 := by exact prefixLift 3498661
  have htrace : WordTrace (prefixWord ++ tailWord_3498661) baseStart_3498661 baseEnd_3498661 := by
    simpa [prefixWord, tailWord_3498661, baseEnd_3498661] using wordTrace_append hprefix tailTrace_3498661
  have hstable : (prefixWord ++ tailWord_3498661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498661).length < 2 ^ (prefixWord ++ tailWord_3498661).sum := by decide
  have hdescent : baseEnd_3498661 < baseStart_3498661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498689 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3498689 : Nat := 118140960795 + 3498689 * 2 ^ 59
def prefixEnd_3498689 : Nat := 4983230072969 + 3 ^ 40 * 3498689 * 2
def baseEnd_3498689 : Nat := 1796509117598367096897329

theorem tailTrace_3498689 : CollatzResearch.WordTrace tailWord_3498689 prefixEnd_3498689 1796509117598367096897329 := by
  unfold tailWord_3498689
  simp only [CollatzResearch.WordTrace]
  refine ⟨127607671221854756354635121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85071780814569837569756747 127607671221854756354635121)
  ·
    refine ⟨95705753416391067265976341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127607671221854756354635121 95705753416391067265976341)
    ·
      refine ⟨4486207191393331278092641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95705753416391067265976341 4486207191393331278092641)
      ·
        refine ⟨3364655393544998458569481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486207191393331278092641 3364655393544998458569481)
        ·
          refine ⟨2523491545158748843927111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364655393544998458569481 2523491545158748843927111)
          ·
            refine ⟨3785237317738123265890667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523491545158748843927111 3785237317738123265890667)
            ·
              refine ⟨5677855976607184898836001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785237317738123265890667 5677855976607184898836001)
              ·
                refine ⟨4258391982455388674127001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5677855976607184898836001 4258391982455388674127001)
                ·
                  refine ⟨3193793986841541505595251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258391982455388674127001 3193793986841541505595251)
                  ·
                    refine ⟨4790690980262312258392877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3193793986841541505595251 4790690980262312258392877)
                    ·
                      refine ⟨1796509117598367096897329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790690980262312258392877 1796509117598367096897329)
                      ·
                        rfl

theorem cell23_3498689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3498689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498689 prefixEnd_3498689 := by exact prefixLift 3498689
  have htrace : WordTrace (prefixWord ++ tailWord_3498689) baseStart_3498689 baseEnd_3498689 := by
    simpa [prefixWord, tailWord_3498689, baseEnd_3498689] using wordTrace_append hprefix tailTrace_3498689
  have hstable : (prefixWord ++ tailWord_3498689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498689).length < 2 ^ (prefixWord ++ tailWord_3498689).sum := by decide
  have hdescent : baseEnd_3498689 < baseStart_3498689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498761 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_3498761 : Nat := 118140960795 + 3498761 * 2 ^ 59
def prefixEnd_3498761 : Nat := 4983230072969 + 3 ^ 40 * 3498761 * 2
def baseEnd_3498761 : Nat := 598848696068496938398999

theorem tailTrace_3498761 : CollatzResearch.WordTrace tailWord_3498761 prefixEnd_3498761 598848696068496938398999 := by
  unfold tailWord_3498761
  simp only [CollatzResearch.WordTrace]
  refine ⟨127610297277593912651256137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85073531518395941767504091 127610297277593912651256137)
  ·
    refine ⟨95707722958195434488442103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127610297277593912651256137 95707722958195434488442103)
    ·
      refine ⟨143561584437293151732663155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95707722958195434488442103 143561584437293151732663155)
      ·
        refine ⟨215342376655939727598994733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143561584437293151732663155 215342376655939727598994733)
        ·
          refine ⟨80753391245977397849623025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215342376655939727598994733 80753391245977397849623025)
          ·
            refine ⟨60565043434483048387217269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80753391245977397849623025 60565043434483048387217269)
            ·
              refine ⟨5677972821982785786301619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60565043434483048387217269 5677972821982785786301619)
              ·
                refine ⟨8516959232974178679452429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677972821982785786301619 8516959232974178679452429)
                ·
                  refine ⟨3193859712365317004794661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8516959232974178679452429 3193859712365317004794661)
                  ·
                    refine ⟨598848696068496938398999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193859712365317004794661 598848696068496938398999)
                    ·
                      rfl

theorem cell23_3498761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_3498761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498761 prefixEnd_3498761 := by exact prefixLift 3498761
  have htrace : WordTrace (prefixWord ++ tailWord_3498761) baseStart_3498761 baseEnd_3498761 := by
    simpa [prefixWord, tailWord_3498761, baseEnd_3498761] using wordTrace_append hprefix tailTrace_3498761
  have hstable : (prefixWord ++ tailWord_3498761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498761).length < 2 ^ (prefixWord ++ tailWord_3498761).sum := by decide
  have hdescent : baseEnd_3498761 < baseStart_3498761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498841 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3498841 : Nat := 118140960795 + 3498841 * 2 ^ 59
def prefixEnd_3498841 : Nat := 4983230072969 + 3 ^ 40 * 3498841 * 2
def baseEnd_3498841 : Nat := 1796587166657850502196629

theorem tailTrace_3498841 : CollatzResearch.WordTrace tailWord_3498841 prefixEnd_3498841 1796587166657850502196629 := by
  unfold tailWord_3498841
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613215117304086314168377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85075476744869390876112251 127613215117304086314168377)
  ·
    refine ⟨95709911337978064735626283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127613215117304086314168377 95709911337978064735626283)
    ·
      refine ⟨143564867006967097103439425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95709911337978064735626283 143564867006967097103439425)
      ·
        refine ⟨107673650255225322827579569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143564867006967097103439425 107673650255225322827579569)
        ·
          refine ⟨80755237691418992120684677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107673650255225322827579569 80755237691418992120684677)
          ·
            refine ⟨15141607067141061022628377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80755237691418992120684677 15141607067141061022628377)
            ·
              refine ⟨11356205300355795766971283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141607067141061022628377 11356205300355795766971283)
              ·
                refine ⟨17034307950533693650456925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356205300355795766971283 17034307950533693650456925)
                ·
                  refine ⟨6387865481450135118921347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17034307950533693650456925 6387865481450135118921347)
                  ·
                    refine ⟨9581798222175202678382021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6387865481450135118921347 9581798222175202678382021)
                    ·
                      refine ⟨1796587166657850502196629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9581798222175202678382021 1796587166657850502196629)
                      ·
                        rfl

theorem cell23_3498841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3498841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498841 prefixEnd_3498841 := by exact prefixLift 3498841
  have htrace : WordTrace (prefixWord ++ tailWord_3498841) baseStart_3498841 baseEnd_3498841 := by
    simpa [prefixWord, tailWord_3498841, baseEnd_3498841] using wordTrace_append hprefix tailTrace_3498841
  have hstable : (prefixWord ++ tailWord_3498841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498841).length < 2 ^ (prefixWord ++ tailWord_3498841).sum := by decide
  have hdescent : baseEnd_3498841 < baseStart_3498841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498851 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 1, 6]
def baseStart_3498851 : Nat := 118140960795 + 3498851 * 2 ^ 59
def prefixEnd_3498851 : Nat := 4983230072969 + 3 ^ 40 * 3498851 * 2
def baseEnd_3498851 : Nat := 598864100488131821023861

theorem tailTrace_3498851 : CollatzResearch.WordTrace tailWord_3498851 prefixEnd_3498851 598864100488131821023861 := by
  unfold tailWord_3498851
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613579847267858022032407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85075719898178572014688271 127613579847267858022032407)
  ·
    refine ⟨191420369770901787033048611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127613579847267858022032407 191420369770901787033048611)
    ·
      refine ⟨287130554656352680549572917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191420369770901787033048611 287130554656352680549572917)
      ·
        refine ⟨26918489499033063801522461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287130554656352680549572917 26918489499033063801522461)
        ·
          refine ⟨10094433562137398925570923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26918489499033063801522461 10094433562137398925570923)
          ·
            refine ⟨15141650343206098388356385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094433562137398925570923 15141650343206098388356385)
            ·
              refine ⟨11356237757404573791267289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15141650343206098388356385 11356237757404573791267289)
              ·
                refine ⟨8517178318053430343450467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11356237757404573791267289 8517178318053430343450467)
                ·
                  refine ⟨12775767477080145515175701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517178318053430343450467 12775767477080145515175701)
                  ·
                    refine ⟨598864100488131821023861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12775767477080145515175701 598864100488131821023861)
                    ·
                      rfl

theorem cell23_3498851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_3498851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498851 prefixEnd_3498851 := by exact prefixLift 3498851
  have htrace : WordTrace (prefixWord ++ tailWord_3498851) baseStart_3498851 baseEnd_3498851 := by
    simpa [prefixWord, tailWord_3498851, baseEnd_3498851] using wordTrace_append hprefix tailTrace_3498851
  have hstable : (prefixWord ++ tailWord_3498851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498851).length < 2 ^ (prefixWord ++ tailWord_3498851).sum := by decide
  have hdescent : baseEnd_3498851 < baseStart_3498851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498852 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_3498852 : Nat := 118140960795 + 3498852 * 2 ^ 59
def prefixEnd_3498852 : Nat := 4983230072969 + 3 ^ 40 * 3498852 * 2
def baseEnd_3498852 : Nat := 1796592814945049959159079

theorem tailTrace_3498852 : CollatzResearch.WordTrace tailWord_3498852 prefixEnd_3498852 1796592814945049959159079 := by
  unfold tailWord_3498852
  simp only [CollatzResearch.WordTrace]
  refine ⟨63806808160132117596409405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85075744213509490128545873 63806808160132117596409405)
  ·
    refine ⟨23927553060049544098653527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63806808160132117596409405 23927553060049544098653527)
    ·
      refine ⟨35891329590074316147980291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23927553060049544098653527 35891329590074316147980291)
      ·
        refine ⟨53836994385111474221970437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35891329590074316147980291 53836994385111474221970437)
        ·
          refine ⟨10094436447208401416619457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53836994385111474221970437 10094436447208401416619457)
          ·
            refine ⟨7570827335406301062464593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10094436447208401416619457 7570827335406301062464593)
            ·
              refine ⟨5678120501554725796848445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7570827335406301062464593 5678120501554725796848445)
              ·
                refine ⟨2129295188083022173818167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5678120501554725796848445 2129295188083022173818167)
                ·
                  refine ⟨3193942782124533260727251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129295188083022173818167 3193942782124533260727251)
                  ·
                    refine ⟨4790914173186799891090877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3193942782124533260727251 4790914173186799891090877)
                    ·
                      refine ⟨1796592814945049959159079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4790914173186799891090877 1796592814945049959159079)
                      ·
                        rfl

theorem cell23_3498852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_3498852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498852 prefixEnd_3498852 := by exact prefixLift 3498852
  have htrace : WordTrace (prefixWord ++ tailWord_3498852) baseStart_3498852 baseEnd_3498852 := by
    simpa [prefixWord, tailWord_3498852, baseEnd_3498852] using wordTrace_append hprefix tailTrace_3498852
  have hstable : (prefixWord ++ tailWord_3498852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498852).length < 2 ^ (prefixWord ++ tailWord_3498852).sum := by decide
  have hdescent : baseEnd_3498852 < baseStart_3498852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498855 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3498855 : Nat := 118140960795 + 3498855 * 2 ^ 59
def prefixEnd_3498855 : Nat := 4983230072969 + 3 ^ 40 * 3498855 * 2
def baseEnd_3498855 : Nat := 598864785129004482473855

theorem tailTrace_3498855 : CollatzResearch.WordTrace tailWord_3498855 prefixEnd_3498855 598864785129004482473855 := by
  unfold tailWord_3498855
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613725739253366705178019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85075817159502244470118679 127613725739253366705178019)
  ·
    refine ⟨191420588608880050057767029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127613725739253366705178019 191420588608880050057767029)
    ·
      refine ⟨17945680182082504692915659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191420588608880050057767029 17945680182082504692915659)
      ·
        refine ⟨26918520273123757039373489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17945680182082504692915659 26918520273123757039373489)
        ·
          refine ⟨20188890204842817779530117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26918520273123757039373489 20188890204842817779530117)
          ·
            refine ⟨3785416913408028333661897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20188890204842817779530117 3785416913408028333661897)
            ·
              refine ⟨2839062685056021250246423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785416913408028333661897 2839062685056021250246423)
              ·
                refine ⟨4258594027584031875369635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839062685056021250246423 4258594027584031875369635)
                ·
                  refine ⟨6387891041376047813054453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4258594027584031875369635 6387891041376047813054453)
                  ·
                    refine ⟨598864785129004482473855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6387891041376047813054453 598864785129004482473855)
                    ·
                      rfl

theorem cell23_3498855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3498855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498855 prefixEnd_3498855 := by exact prefixLift 3498855
  have htrace : WordTrace (prefixWord ++ tailWord_3498855) baseStart_3498855 baseEnd_3498855 := by
    simpa [prefixWord, tailWord_3498855, baseEnd_3498855] using wordTrace_append hprefix tailTrace_3498855
  have hstable : (prefixWord ++ tailWord_3498855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498855).length < 2 ^ (prefixWord ++ tailWord_3498855).sum := by decide
  have hdescent : baseEnd_3498855 < baseStart_3498855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498861 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3498861 : Nat := 118140960795 + 3498861 * 2 ^ 59
def prefixEnd_3498861 : Nat := 4983230072969 + 3 ^ 40 * 3498861 * 2
def baseEnd_3498861 : Nat := 1796597436270940423946537

theorem tailTrace_3498861 : CollatzResearch.WordTrace tailWord_3498861 prefixEnd_3498861 1796597436270940423946537 := by
  unfold tailWord_3498861
  simp only [CollatzResearch.WordTrace]
  refine ⟨127613944577231629729896437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85075963051487753153264291 127613944577231629729896437)
  ·
    refine ⟨11963807304115465287177791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127613944577231629729896437 11963807304115465287177791)
    ·
      refine ⟨17945710956173197930766687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11963807304115465287177791 17945710956173197930766687)
      ·
        refine ⟨26918566434259796896150031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17945710956173197930766687 26918566434259796896150031)
        ·
          refine ⟨40377849651389695344225047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26918566434259796896150031 40377849651389695344225047)
          ·
            refine ⟨60566774477084543016337571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40377849651389695344225047 60566774477084543016337571)
            ·
              refine ⟨90850161715626814524506357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60566774477084543016337571 90850161715626814524506357)
              ·
                refine ⟨8517202660840013861672471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90850161715626814524506357 8517202660840013861672471)
                ·
                  refine ⟨12775803991260020792508707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517202660840013861672471 12775803991260020792508707)
                  ·
                    refine ⟨19163705986890031188763061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12775803991260020792508707 19163705986890031188763061)
                    ·
                      refine ⟨1796597436270940423946537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19163705986890031188763061 1796597436270940423946537)
                      ·
                        rfl

theorem cell23_3498861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3498861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498861 prefixEnd_3498861 := by exact prefixLift 3498861
  have htrace : WordTrace (prefixWord ++ tailWord_3498861) baseStart_3498861 baseEnd_3498861 := by
    simpa [prefixWord, tailWord_3498861, baseEnd_3498861] using wordTrace_append hprefix tailTrace_3498861
  have hstable : (prefixWord ++ tailWord_3498861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498861).length < 2 ^ (prefixWord ++ tailWord_3498861).sum := by decide
  have hdescent : baseEnd_3498861 < baseStart_3498861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3498874 : Nat := 118140960795 + 3498874 * 2 ^ 59
def prefixEnd_3498874 : Nat := 4983230072969 + 3 ^ 40 * 3498874 * 2
def baseEnd_3498874 : Nat := 1796604111519448873083977

theorem tailTrace_3498874 : CollatzResearch.WordTrace tailWord_3498874 prefixEnd_3498874 1796604111519448873083977 := by
  unfold tailWord_3498874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903604681546133237529919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85076279150789688633413117 31903604681546133237529919)
  ·
    refine ⟨47855407022319199856294879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31903604681546133237529919 47855407022319199856294879)
    ·
      refine ⟨71783110533478799784442319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47855407022319199856294879 71783110533478799784442319)
      ·
        refine ⟨107674665800218199676663479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71783110533478799784442319 107674665800218199676663479)
        ·
          refine ⟨161511998700327299514995219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107674665800218199676663479 161511998700327299514995219)
          ·
            refine ⟨242267998050490949272492829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161511998700327299514995219 242267998050490949272492829)
            ·
              refine ⟨90850499268934105977184811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242267998050490949272492829 90850499268934105977184811)
              ·
                refine ⟨136275748903401158965777217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90850499268934105977184811 136275748903401158965777217)
                ·
                  refine ⟨102206811677550869224332913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136275748903401158965777217 102206811677550869224332913)
                  ·
                    refine ⟨76655108758163151918249685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102206811677550869224332913 76655108758163151918249685)
                    ·
                      refine ⟨1796604111519448873083977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76655108758163151918249685 1796604111519448873083977)
                      ·
                        rfl

theorem cell23_3498874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3498874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498874 prefixEnd_3498874 := by exact prefixLift 3498874
  have htrace : WordTrace (prefixWord ++ tailWord_3498874) baseStart_3498874 baseEnd_3498874 := by
    simpa [prefixWord, tailWord_3498874, baseEnd_3498874] using wordTrace_append hprefix tailTrace_3498874
  have hstable : (prefixWord ++ tailWord_3498874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498874).length < 2 ^ (prefixWord ++ tailWord_3498874).sum := by decide
  have hdescent : baseEnd_3498874 < baseStart_3498874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498885 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_3498885 : Nat := 118140960795 + 3498885 * 2 ^ 59
def prefixEnd_3498885 : Nat := 4983230072969 + 3 ^ 40 * 3498885 * 2
def baseEnd_3498885 : Nat := 598869919935549443348809

theorem tailTrace_3498885 : CollatzResearch.WordTrace tailWord_3498885 prefixEnd_3498885 598869919935549443348809 := by
  unfold tailWord_3498885
  simp only [CollatzResearch.WordTrace]
  refine ⟨127614819929144681828770109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85076546619429787885846739 127614819929144681828770109)
  ·
    refine ⟨47855557473429255685788791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127614819929144681828770109 47855557473429255685788791)
    ·
      refine ⟨71783336210143883528683187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47855557473429255685788791 71783336210143883528683187)
      ·
        refine ⟨107675004315215825293024781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71783336210143883528683187 107675004315215825293024781)
        ·
          refine ⟨40378126618205934484884293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107675004315215825293024781 40378126618205934484884293)
          ·
            refine ⟨7570898740913612715915805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40378126618205934484884293 7570898740913612715915805)
            ·
              refine ⟨2839087027842604768468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7570898740913612715915805 2839087027842604768468427)
              ·
                refine ⟨4258630541763907152702641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839087027842604768468427 4258630541763907152702641)
                ·
                  refine ⟨3193972906322930364526981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258630541763907152702641 3193972906322930364526981)
                  ·
                    refine ⟨598869919935549443348809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193972906322930364526981 598869919935549443348809)
                    ·
                      rfl

theorem cell23_3498885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_3498885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498885 prefixEnd_3498885 := by exact prefixLift 3498885
  have htrace : WordTrace (prefixWord ++ tailWord_3498885) baseStart_3498885 baseEnd_3498885 := by
    simpa [prefixWord, tailWord_3498885, baseEnd_3498885] using wordTrace_append hprefix tailTrace_3498885
  have hstable : (prefixWord ++ tailWord_3498885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498885).length < 2 ^ (prefixWord ++ tailWord_3498885).sum := by decide
  have hdescent : baseEnd_3498885 < baseStart_3498885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498888 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3498888 : Nat := 118140960795 + 3498888 * 2 ^ 59
def prefixEnd_3498888 : Nat := 4983230072969 + 3 ^ 40 * 3498888 * 2
def baseEnd_3498888 : Nat := 1796611300248611818308913

theorem tailTrace_3498888 : CollatzResearch.WordTrace tailWord_3498888 prefixEnd_3498888 1796611300248611818308913 := by
  unfold tailWord_3498888
  simp only [CollatzResearch.WordTrace]
  refine ⟨63807464674066906670564659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85076619565422542227419545 63807464674066906670564659)
  ·
    refine ⟨95711197011100360005846989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63807464674066906670564659 95711197011100360005846989)
    ·
      refine ⟨35891698879162635002192621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95711197011100360005846989 35891698879162635002192621)
      ·
        refine ⟨13459387079685988125822233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35891698879162635002192621 13459387079685988125822233)
        ·
          refine ⟨10094540309764491094366675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13459387079685988125822233 10094540309764491094366675)
          ·
            refine ⟨15141810464646736641550013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094540309764491094366675 15141810464646736641550013)
            ·
              refine ⟨5678178924242526240581255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15141810464646736641550013 5678178924242526240581255)
              ·
                refine ⟨8517268386363789360871883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678178924242526240581255 8517268386363789360871883)
                ·
                  refine ⟨12775902579545684041307825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8517268386363789360871883 12775902579545684041307825)
                  ·
                    refine ⟨9581926934659263030980869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12775902579545684041307825 9581926934659263030980869)
                    ·
                      refine ⟨1796611300248611818308913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9581926934659263030980869 1796611300248611818308913)
                      ·
                        rfl

theorem cell23_3498888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3498888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498888 prefixEnd_3498888 := by exact prefixLift 3498888
  have htrace : WordTrace (prefixWord ++ tailWord_3498888) baseStart_3498888 baseEnd_3498888 := by
    simpa [prefixWord, tailWord_3498888, baseEnd_3498888] using wordTrace_append hprefix tailTrace_3498888
  have hstable : (prefixWord ++ tailWord_3498888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498888).length < 2 ^ (prefixWord ++ tailWord_3498888).sum := by decide
  have hdescent : baseEnd_3498888 < baseStart_3498888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498898 : List Nat := [3, 2, 3, 2, 2, 1, 1, 9]
def baseStart_3498898 : Nat := 118140960795 + 3498898 * 2 ^ 59
def prefixEnd_3498898 : Nat := 4983230072969 + 3 ^ 40 * 3498898 * 2
def baseEnd_3498898 : Nat := 66541349446487288117921

theorem tailTrace_3498898 : CollatzResearch.WordTrace tailWord_3498898 prefixEnd_3498898 66541349446487288117921 := by
  unfold tailWord_3498898
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903823519524396262248337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85076862718731723365995565 31903823519524396262248337)
  ·
    refine ⟨23927867639643297196686253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31903823519524396262248337 23927867639643297196686253)
    ·
      refine ⟨8972950364866236448757345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23927867639643297196686253 8972950364866236448757345)
      ·
        refine ⟨6729712773649677336568009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8972950364866236448757345 6729712773649677336568009)
        ·
          refine ⟨5047284580237258002426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6729712773649677336568009 5047284580237258002426007)
          ·
            refine ⟨7570926870355887003639011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047284580237258002426007 7570926870355887003639011)
            ·
              refine ⟨11356390305533830505458517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7570926870355887003639011 11356390305533830505458517)
              ·
                refine ⟨66541349446487288117921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11356390305533830505458517 66541349446487288117921)
                ·
                  rfl

theorem cell23_3498898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_3498898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498898 prefixEnd_3498898 := by exact prefixLift 3498898
  have htrace : WordTrace (prefixWord ++ tailWord_3498898) baseStart_3498898 baseEnd_3498898 := by
    simpa [prefixWord, tailWord_3498898, baseEnd_3498898] using wordTrace_append hprefix tailTrace_3498898
  have hstable : (prefixWord ++ tailWord_3498898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498898).length < 2 ^ (prefixWord ++ tailWord_3498898).sum := by decide
  have hdescent : baseEnd_3498898 < baseStart_3498898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498902 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3498902 : Nat := 118140960795 + 3498902 * 2 ^ 59
def prefixEnd_3498902 : Nat := 4983230072969 + 3 ^ 40 * 3498902 * 2
def baseEnd_3498902 : Nat := 598872829659258254511283

theorem tailTrace_3498902 : CollatzResearch.WordTrace tailWord_3498902 prefixEnd_3498902 598872829659258254511283 := by
  unfold tailWord_3498902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975964998130193358258685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85076959980055395821425973 7975964998130193358258685)
  ·
    refine ⟨2990986874298822509347007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7975964998130193358258685 2990986874298822509347007)
    ·
      refine ⟨4486480311448233764020511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990986874298822509347007 4486480311448233764020511)
      ·
        refine ⟨6729720467172350646030767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486480311448233764020511 6729720467172350646030767)
        ·
          refine ⟨10094580700758525969046151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729720467172350646030767 10094580700758525969046151)
          ·
            refine ⟨15141871051137788953569227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10094580700758525969046151 15141871051137788953569227)
            ·
              refine ⟨22712806576706683430353841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15141871051137788953569227 22712806576706683430353841)
              ·
                refine ⟨17034604932530012572765381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22712806576706683430353841 17034604932530012572765381)
                ·
                  refine ⟨3193988424849377357393509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17034604932530012572765381 3193988424849377357393509)
                  ·
                    refine ⟨598872829659258254511283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3193988424849377357393509 598872829659258254511283)
                    ·
                      rfl

theorem cell23_3498902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3498902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498902 prefixEnd_3498902 := by exact prefixLift 3498902
  have htrace : WordTrace (prefixWord ++ tailWord_3498902) baseStart_3498902 baseEnd_3498902 := by
    simpa [prefixWord, tailWord_3498902, baseEnd_3498902] using wordTrace_append hprefix tailTrace_3498902
  have hstable : (prefixWord ++ tailWord_3498902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498902).length < 2 ^ (prefixWord ++ tailWord_3498902).sum := by decide
  have hdescent : baseEnd_3498902 < baseStart_3498902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3498951 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3498951 : Nat := 118140960795 + 3498951 * 2 ^ 59
def prefixEnd_3498951 : Nat := 4983230072969 + 3 ^ 40 * 3498951 * 2
def baseEnd_3498951 : Nat := 1796643649529845071821123

theorem tailTrace_3498951 : CollatzResearch.WordTrace tailWord_3498951 prefixEnd_3498951 1796643649529845071821123 := by
  unfold tailWord_3498951
  simp only [CollatzResearch.WordTrace]
  refine ⟨127617227146905575100672707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85078151431270383400448471 127617227146905575100672707)
  ·
    refine ⟨191425840720358362651009061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127617227146905575100672707 191425840720358362651009061)
    ·
      refine ⟨35892345135067192997064199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191425840720358362651009061 35892345135067192997064199)
      ·
        refine ⟨53838517702600789495596299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35892345135067192997064199 53838517702600789495596299)
        ·
          refine ⟨80757776553901184243394449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53838517702600789495596299 80757776553901184243394449)
          ·
            refine ⟨60568332415425888182545837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80757776553901184243394449 60568332415425888182545837)
            ·
              refine ⟨22713124655784708068454689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60568332415425888182545837 22713124655784708068454689)
              ·
                refine ⟨17034843491838531051341017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22713124655784708068454689 17034843491838531051341017)
                ·
                  refine ⟨12776132618878898288505763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17034843491838531051341017 12776132618878898288505763)
                  ·
                    refine ⟨19164198928318347432758645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12776132618878898288505763 19164198928318347432758645)
                    ·
                      refine ⟨1796643649529845071821123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19164198928318347432758645 1796643649529845071821123)
                      ·
                        rfl

theorem cell23_3498951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3498951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3498951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3498951 prefixEnd_3498951 := by exact prefixLift 3498951
  have htrace : WordTrace (prefixWord ++ tailWord_3498951) baseStart_3498951 baseEnd_3498951 := by
    simpa [prefixWord, tailWord_3498951, baseEnd_3498951] using wordTrace_append hprefix tailTrace_3498951
  have hstable : (prefixWord ++ tailWord_3498951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3498951).length < 2 ^ (prefixWord ++ tailWord_3498951).sum := by decide
  have hdescent : baseEnd_3498951 < baseStart_3498951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3498951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499001 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_3499001 : Nat := 118140960795 + 3499001 * 2 ^ 59
def prefixEnd_3499001 : Nat := 4983230072969 + 3 ^ 40 * 3499001 * 2
def baseEnd_3499001 : Nat := 598889774520856625398631

theorem tailTrace_3499001 : CollatzResearch.WordTrace tailWord_3499001 prefixEnd_3499001 598889774520856625398631 := by
  unfold tailWord_3499001
  simp only [CollatzResearch.WordTrace]
  refine ⟨127619050796724433639992857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85079367197816289093328571 127619050796724433639992857)
  ·
    refine ⟨95714288097543325229994643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127619050796724433639992857 95714288097543325229994643)
    ·
      refine ⟨143571432146314987844991965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95714288097543325229994643 143571432146314987844991965)
      ·
        refine ⟨53839287054868120441871987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143571432146314987844991965 53839287054868120441871987)
        ·
          refine ⟨80758930582302180662807981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53839287054868120441871987 80758930582302180662807981)
          ·
            refine ⟨30284598968363317748552993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80758930582302180662807981 30284598968363317748552993)
            ·
              refine ⟨22713449226272488311414745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30284598968363317748552993 22713449226272488311414745)
              ·
                refine ⟨17035086919704366233561059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22713449226272488311414745 17035086919704366233561059)
                ·
                  refine ⟨25552630379556549350341589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17035086919704366233561059 25552630379556549350341589)
                  ·
                    refine ⟨598889774520856625398631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25552630379556549350341589 598889774520856625398631)
                    ·
                      rfl

theorem cell23_3499001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_3499001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499001 prefixEnd_3499001 := by exact prefixLift 3499001
  have htrace : WordTrace (prefixWord ++ tailWord_3499001) baseStart_3499001 baseEnd_3499001 := by
    simpa [prefixWord, tailWord_3499001, baseEnd_3499001] using wordTrace_append hprefix tailTrace_3499001
  have hstable : (prefixWord ++ tailWord_3499001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499001).length < 2 ^ (prefixWord ++ tailWord_3499001).sum := by decide
  have hdescent : baseEnd_3499001 < baseStart_3499001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499018 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3499018 : Nat := 118140960795 + 3499018 * 2 ^ 59
def prefixEnd_3499018 : Nat := 4983230072969 + 3 ^ 40 * 3499018 * 2
def baseEnd_3499018 : Nat := 598892684244565436561105

theorem tailTrace_3499018 : CollatzResearch.WordTrace tailWord_3499018 prefixEnd_3499018 598892684244565436561105 := by
  unfold tailWord_3499018
  simp only [CollatzResearch.WordTrace]
  refine ⟨31904917709415711385840427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85079780558441897028907805 31904917709415711385840427)
  ·
    refine ⟨47857376564123567078760641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31904917709415711385840427 47857376564123567078760641)
    ·
      refine ⟨35893032423092675309070481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47857376564123567078760641 35893032423092675309070481)
      ·
        refine ⟨26919774317319506481802861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35893032423092675309070481 26919774317319506481802861)
        ·
          refine ⟨10094915368994814930676073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26919774317319506481802861 10094915368994814930676073)
          ·
            refine ⟨7571186526746111198007055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10094915368994814930676073 7571186526746111198007055)
            ·
              refine ⟨11356779790119166797010583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571186526746111198007055 11356779790119166797010583)
              ·
                refine ⟨17035169685178750195515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11356779790119166797010583 17035169685178750195515875)
                ·
                  refine ⟨25552754527768125293273813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17035169685178750195515875 25552754527768125293273813)
                  ·
                    refine ⟨598892684244565436561105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25552754527768125293273813 598892684244565436561105)
                    ·
                      rfl

theorem cell23_3499018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3499018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499018 prefixEnd_3499018 := by exact prefixLift 3499018
  have htrace : WordTrace (prefixWord ++ tailWord_3499018) baseStart_3499018 baseEnd_3499018 := by
    simpa [prefixWord, tailWord_3499018, baseEnd_3499018] using wordTrace_append hprefix tailTrace_3499018
  have hstable : (prefixWord ++ tailWord_3499018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499018).length < 2 ^ (prefixWord ++ tailWord_3499018).sum := by decide
  have hdescent : baseEnd_3499018 < baseStart_3499018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499051 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_3499051 : Nat := 118140960795 + 3499051 * 2 ^ 59
def prefixEnd_3499051 : Nat := 4983230072969 + 3 ^ 40 * 3499051 * 2
def baseEnd_3499051 : Nat := 1796694997595294680570663

theorem tailTrace_3499051 : CollatzResearch.WordTrace tailWord_3499051 prefixEnd_3499051 1796694997595294680570663 := by
  unfold tailWord_3499051
  simp only [CollatzResearch.WordTrace]
  refine ⟨127620874446543292179313007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85080582964362194786208671 127620874446543292179313007)
  ·
    refine ⟨191431311669814938268969511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127620874446543292179313007 191431311669814938268969511)
    ·
      refine ⟨287146967504722407403454267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191431311669814938268969511 287146967504722407403454267)
      ·
        refine ⟨430720451257083611105181401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287146967504722407403454267 430720451257083611105181401)
        ·
          refine ⟨323040338442812708328886051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430720451257083611105181401 323040338442812708328886051)
          ·
            refine ⟨484560507664219062493329077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323040338442812708328886051 484560507664219062493329077)
            ·
              refine ⟨45427547593520537108749601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 484560507664219062493329077 45427547593520537108749601)
              ·
                refine ⟨34070660695140402831562201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45427547593520537108749601 34070660695140402831562201)
                ·
                  refine ⟨25552995521355302123671651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34070660695140402831562201 25552995521355302123671651)
                  ·
                    refine ⟨38329493282032953185507477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25552995521355302123671651 38329493282032953185507477)
                    ·
                      refine ⟨1796694997595294680570663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38329493282032953185507477 1796694997595294680570663)
                      ·
                        rfl

theorem cell23_3499051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_3499051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499051 prefixEnd_3499051 := by exact prefixLift 3499051
  have htrace : WordTrace (prefixWord ++ tailWord_3499051) baseStart_3499051 baseEnd_3499051 := by
    simpa [prefixWord, tailWord_3499051, baseEnd_3499051] using wordTrace_append hprefix tailTrace_3499051
  have hstable : (prefixWord ++ tailWord_3499051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499051).length < 2 ^ (prefixWord ++ tailWord_3499051).sum := by decide
  have hdescent : baseEnd_3499051 < baseStart_3499051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499058 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3499058 : Nat := 118140960795 + 3499058 * 2 ^ 59
def prefixEnd_3499058 : Nat := 4983230072969 + 3 ^ 40 * 3499058 * 2
def baseEnd_3499058 : Nat := 1796698591959876153183131

theorem tailTrace_3499058 : CollatzResearch.WordTrace tailWord_3499058 prefixEnd_3499058 1796698591959876153183131 := by
  unfold tailWord_3499058
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905282439379483093704457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85080753171678621583211885 31905282439379483093704457)
  ·
    refine ⟨23928961829534612320278343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31905282439379483093704457 23928961829534612320278343)
    ·
      refine ⟨35893442744301918480417515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23928961829534612320278343 35893442744301918480417515)
      ·
        refine ⟨53840164116452877720626273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35893442744301918480417515 53840164116452877720626273)
        ·
          refine ⟨40380123087339658290469705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53840164116452877720626273 40380123087339658290469705)
          ·
            refine ⟨30285092315504743717852279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40380123087339658290469705 30285092315504743717852279)
            ·
              refine ⟨45427638473257115576778419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30285092315504743717852279 45427638473257115576778419)
              ·
                refine ⟨68141457709885673365167629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45427638473257115576778419 68141457709885673365167629)
                ·
                  refine ⟨25553046641207127511937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68141457709885673365167629 25553046641207127511937861)
                  ·
                    refine ⟨4791196245226336408488349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25553046641207127511937861 4791196245226336408488349)
                    ·
                      refine ⟨1796698591959876153183131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4791196245226336408488349 1796698591959876153183131)
                      ·
                        rfl

theorem cell23_3499058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3499058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499058 prefixEnd_3499058 := by exact prefixLift 3499058
  have htrace : WordTrace (prefixWord ++ tailWord_3499058) baseStart_3499058 baseEnd_3499058 := by
    simpa [prefixWord, tailWord_3499058, baseEnd_3499058] using wordTrace_append hprefix tailTrace_3499058
  have hstable : (prefixWord ++ tailWord_3499058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499058).length < 2 ^ (prefixWord ++ tailWord_3499058).sum := by decide
  have hdescent : baseEnd_3499058 < baseStart_3499058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499065 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_3499065 : Nat := 118140960795 + 3499065 * 2 ^ 59
def prefixEnd_3499065 : Nat := 4983230072969 + 3 ^ 40 * 3499065 * 2
def baseEnd_3499065 : Nat := 598900728774819208598533

theorem tailTrace_3499065 : CollatzResearch.WordTrace tailWord_3499065 prefixEnd_3499065 598900728774819208598533 := by
  unfold tailWord_3499065
  simp only [CollatzResearch.WordTrace]
  refine ⟨127621385068492572570322649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85080923378995048380215099 127621385068492572570322649)
  ·
    refine ⟨95716038801369429427741987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127621385068492572570322649 95716038801369429427741987)
    ·
      refine ⟨143574058202054144141612981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95716038801369429427741987 143574058202054144141612981)
      ·
        refine ⟨13460067956442576013276217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143574058202054144141612981 13460067956442576013276217)
        ·
          refine ⟨10095050967331932009957163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13460067956442576013276217 10095050967331932009957163)
          ·
            refine ⟨15142576450997898014935745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095050967331932009957163 15142576450997898014935745)
            ·
              refine ⟨11356932338248423511201809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15142576450997898014935745 11356932338248423511201809)
              ·
                refine ⟨8517699253686317633401357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11356932338248423511201809 8517699253686317633401357)
                ·
                  refine ⟨3194137220132369112525509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8517699253686317633401357 3194137220132369112525509)
                  ·
                    refine ⟨598900728774819208598533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194137220132369112525509 598900728774819208598533)
                    ·
                      rfl

theorem cell23_3499065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_3499065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499065 prefixEnd_3499065 := by exact prefixLift 3499065
  have htrace : WordTrace (prefixWord ++ tailWord_3499065) baseStart_3499065 baseEnd_3499065 := by
    simpa [prefixWord, tailWord_3499065, baseEnd_3499065] using wordTrace_append hprefix tailTrace_3499065
  have hstable : (prefixWord ++ tailWord_3499065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499065).length < 2 ^ (prefixWord ++ tailWord_3499065).sum := by decide
  have hdescent : baseEnd_3499065 < baseStart_3499065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499081 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_3499081 : Nat := 118140960795 + 3499081 * 2 ^ 59
def prefixEnd_3499081 : Nat := 4983230072969 + 3 ^ 40 * 3499081 * 2
def baseEnd_3499081 : Nat := 1796710402014929563195525

theorem tailTrace_3499081 : CollatzResearch.WordTrace tailWord_3499081 prefixEnd_3499081 1796710402014929563195525 := by
  unfold tailWord_3499081
  simp only [CollatzResearch.WordTrace]
  refine ⟨127621968636434607302905097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85081312424289738201936731 127621968636434607302905097)
  ·
    refine ⟨95716476477325955477178823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127621968636434607302905097 95716476477325955477178823)
    ·
      refine ⟨143574714715988933215768235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95716476477325955477178823 143574714715988933215768235)
      ·
        refine ⟨215362072073983399823652353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143574714715988933215768235 215362072073983399823652353)
        ·
          refine ⟨161521554055487549867739265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215362072073983399823652353 161521554055487549867739265)
          ·
            refine ⟨121141165541615662400804449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161521554055487549867739265 121141165541615662400804449)
            ·
              refine ⟨90855874156211746800603337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121141165541615662400804449 90855874156211746800603337)
              ·
                refine ⟨68141905617158810100452503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90855874156211746800603337 68141905617158810100452503)
                ·
                  refine ⟨102212858425738215150678755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68141905617158810100452503 102212858425738215150678755)
                  ·
                    refine ⟨153319287638607322726018133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102212858425738215150678755 153319287638607322726018133)
                    ·
                      refine ⟨1796710402014929563195525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 153319287638607322726018133 1796710402014929563195525)
                      ·
                        rfl

theorem cell23_3499081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_3499081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499081 prefixEnd_3499081 := by exact prefixLift 3499081
  have htrace : WordTrace (prefixWord ++ tailWord_3499081) baseStart_3499081 baseEnd_3499081 := by
    simpa [prefixWord, tailWord_3499081, baseEnd_3499081] using wordTrace_append hprefix tailTrace_3499081
  have hstable : (prefixWord ++ tailWord_3499081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499081).length < 2 ^ (prefixWord ++ tailWord_3499081).sum := by decide
  have hdescent : baseEnd_3499081 < baseStart_3499081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499082 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_3499082 : Nat := 118140960795 + 3499082 * 2 ^ 59
def prefixEnd_3499082 : Nat := 4983230072969 + 3 ^ 40 * 3499082 * 2
def baseEnd_3499082 : Nat := 598903638498528019761007

theorem tailTrace_3499082 : CollatzResearch.WordTrace tailWord_3499082 prefixEnd_3499082 598903638498528019761007 := by
  unfold tailWord_3499082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31905501277357746118422875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85081336739620656315794333 31905501277357746118422875)
  ·
    refine ⟨47858251916036619177634313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31905501277357746118422875 47858251916036619177634313)
    ·
      refine ⟨35893688937027464383225735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47858251916036619177634313 35893688937027464383225735)
      ·
        refine ⟨53840533405541196574838603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35893688937027464383225735 53840533405541196574838603)
        ·
          refine ⟨80760800108311794862257905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53840533405541196574838603 80760800108311794862257905)
          ·
            refine ⟨60570600081233846146693429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80760800108311794862257905 60570600081233846146693429)
            ·
              refine ⟨5678493757615673076252509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60570600081233846146693429 5678493757615673076252509)
              ·
                refine ⟨2129435159105877403594691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5678493757615673076252509 2129435159105877403594691)
                ·
                  refine ⟨3194152738658816105392037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129435159105877403594691 3194152738658816105392037)
                  ·
                    refine ⟨598903638498528019761007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194152738658816105392037 598903638498528019761007)
                    ·
                      rfl

theorem cell23_3499082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_3499082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499082 prefixEnd_3499082 := by exact prefixLift 3499082
  have htrace : WordTrace (prefixWord ++ tailWord_3499082) baseStart_3499082 baseEnd_3499082 := by
    simpa [prefixWord, tailWord_3499082, baseEnd_3499082] using wordTrace_append hprefix tailTrace_3499082
  have hstable : (prefixWord ++ tailWord_3499082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499082).length < 2 ^ (prefixWord ++ tailWord_3499082).sum := by decide
  have hdescent : baseEnd_3499082 < baseStart_3499082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499108 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3499108 : Nat := 118140960795 + 3499108 * 2 ^ 59
def prefixEnd_3499108 : Nat := 4983230072969 + 3 ^ 40 * 3499108 * 2
def baseEnd_3499108 : Nat := 598908088664200319185967

theorem tailTrace_3499108 : CollatzResearch.WordTrace tailWord_3499108 prefixEnd_3499108 598908088664200319185967 := by
  unfold tailWord_3499108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811476703668395457068989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85081968938224527276091985 63811476703668395457068989)
  ·
    refine ⟨23929303763875648296400871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63811476703668395457068989 23929303763875648296400871)
    ·
      refine ⟨35893955645813472444601307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23929303763875648296400871 35893955645813472444601307)
      ·
        refine ⟨53840933468720208666901961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35893955645813472444601307 53840933468720208666901961)
        ·
          refine ⟨40380700101540156500176471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53840933468720208666901961 40380700101540156500176471)
          ·
            refine ⟨60571050152310234750264707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40380700101540156500176471 60571050152310234750264707)
            ·
              refine ⟨90856575228465352125397061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60571050152310234750264707 90856575228465352125397061)
              ·
                refine ⟨17035607855337253523511949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90856575228465352125397061 17035607855337253523511949)
                ·
                  refine ⟨6388352945751470071316981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17035607855337253523511949 6388352945751470071316981)
                  ·
                    refine ⟨598908088664200319185967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6388352945751470071316981 598908088664200319185967)
                    ·
                      rfl

theorem cell23_3499108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3499108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499108 prefixEnd_3499108 := by exact prefixLift 3499108
  have htrace : WordTrace (prefixWord ++ tailWord_3499108) baseStart_3499108 baseEnd_3499108 := by
    simpa [prefixWord, tailWord_3499108, baseEnd_3499108] using wordTrace_append hprefix tailTrace_3499108
  have hstable : (prefixWord ++ tailWord_3499108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499108).length < 2 ^ (prefixWord ++ tailWord_3499108).sum := by decide
  have hdescent : baseEnd_3499108 < baseStart_3499108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499112 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 6]
def baseStart_3499112 : Nat := 118140960795 + 3499112 * 2 ^ 59
def prefixEnd_3499112 : Nat := 4983230072969 + 3 ^ 40 * 3499112 * 2
def baseEnd_3499112 : Nat := 199636257768357660211987

theorem tailTrace_3499112 : CollatzResearch.WordTrace tailWord_3499112 prefixEnd_3499112 199636257768357660211987 := by
  unfold tailWord_3499112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811549649661149798641795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85082066199548199731522393 63811549649661149798641795)
  ·
    refine ⟨95717324474491724697962693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63811549649661149798641795 95717324474491724697962693)
    ·
      refine ⟨17946998338967198380868005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95717324474491724697962693 17946998338967198380868005)
      ·
        refine ⟨3365062188556349696412751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17946998338967198380868005 3365062188556349696412751)
        ·
          refine ⟨5047593282834524544619127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365062188556349696412751 5047593282834524544619127)
          ·
            refine ⟨7571389924251786816928691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047593282834524544619127 7571389924251786816928691)
            ·
              refine ⟨11357084886377680225393037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7571389924251786816928691 11357084886377680225393037)
              ·
                refine ⟨4258906832391630084522389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357084886377680225393037 4258906832391630084522389)
                ·
                  refine ⟨199636257768357660211987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4258906832391630084522389 199636257768357660211987)
                  ·
                    rfl

theorem cell23_3499112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_3499112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499112 prefixEnd_3499112 := by exact prefixLift 3499112
  have htrace : WordTrace (prefixWord ++ tailWord_3499112) baseStart_3499112 baseEnd_3499112 := by
    simpa [prefixWord, tailWord_3499112, baseEnd_3499112] using wordTrace_append hprefix tailTrace_3499112
  have hstable : (prefixWord ++ tailWord_3499112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499112).length < 2 ^ (prefixWord ++ tailWord_3499112).sum := by decide
  have hdescent : baseEnd_3499112 < baseStart_3499112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499132 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_3499132 : Nat := 118140960795 + 3499132 * 2 ^ 59
def prefixEnd_3499132 : Nat := 4983230072969 + 3 ^ 40 * 3499132 * 2
def baseEnd_3499132 : Nat := 1796736589528308863657791

theorem tailTrace_3499132 : CollatzResearch.WordTrace tailWord_3499132 prefixEnd_3499132 1796736589528308863657791 := by
  unfold tailWord_3499132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63811914379624921506505825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85082552506166562008674433 63811914379624921506505825)
  ·
    refine ⟨47858935784718691129879369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63811914379624921506505825 47858935784718691129879369)
    ·
      refine ⟨35894201838539018347409527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47858935784718691129879369 35894201838539018347409527)
      ·
        refine ⟨53841302757808527521114291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35894201838539018347409527 53841302757808527521114291)
        ·
          refine ⟨80761954136712791281671437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53841302757808527521114291 80761954136712791281671437)
          ·
            refine ⟨30285732801267296730626789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80761954136712791281671437 30285732801267296730626789)
            ·
              refine ⟨5678574900237618136992523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30285732801267296730626789 5678574900237618136992523)
              ·
                refine ⟨8517862350356427205488785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678574900237618136992523 8517862350356427205488785)
                ·
                  refine ⟨6388396762767320404116589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8517862350356427205488785 6388396762767320404116589)
                  ·
                    refine ⟨2395648786037745151543721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6388396762767320404116589 2395648786037745151543721)
                    ·
                      refine ⟨1796736589528308863657791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395648786037745151543721 1796736589528308863657791)
                      ·
                        rfl

theorem cell23_3499132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_3499132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499132 prefixEnd_3499132 := by exact prefixLift 3499132
  have htrace : WordTrace (prefixWord ++ tailWord_3499132) baseStart_3499132 baseEnd_3499132 := by
    simpa [prefixWord, tailWord_3499132, baseEnd_3499132] using wordTrace_append hprefix tailTrace_3499132
  have hstable : (prefixWord ++ tailWord_3499132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499132).length < 2 ^ (prefixWord ++ tailWord_3499132).sum := by decide
  have hdescent : baseEnd_3499132 < baseStart_3499132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499155 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 2, 4]
def baseStart_3499155 : Nat := 118140960795 + 3499155 * 2 ^ 59
def prefixEnd_3499155 : Nat := 4983230072969 + 3 ^ 40 * 3499155 * 2
def baseEnd_3499155 : Nat := 598916133194454091223395

theorem tailTrace_3499155 : CollatzResearch.WordTrace tailWord_3499155 prefixEnd_3499155 598916133194454091223395 := by
  unfold tailWord_3499155
  simp only [CollatzResearch.WordTrace]
  refine ⟨127624667638166517941098919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85083111758777678627399279 127624667638166517941098919)
  ·
    refine ⟨191437001457249776911648379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127624667638166517941098919 191437001457249776911648379)
    ·
      refine ⟨287155502185874665367472569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191437001457249776911648379 287155502185874665367472569)
      ·
        refine ⟨215366626639405999025604427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287155502185874665367472569 215366626639405999025604427)
        ·
          refine ⟨323049939959108998538406641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215366626639405999025604427 323049939959108998538406641)
          ·
            refine ⟨242287454969331748903804981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323049939959108998538406641 242287454969331748903804981)
            ·
              refine ⟨22714448903374851459731717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242287454969331748903804981 22714448903374851459731717)
              ·
                refine ⟨4258959169382784648699697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22714448903374851459731717 4258959169382784648699697)
                ·
                  refine ⟨3194219377037088486524773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258959169382784648699697 3194219377037088486524773)
                  ·
                    refine ⟨598916133194454091223395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194219377037088486524773 598916133194454091223395)
                    ·
                      rfl

theorem cell23_3499155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 4].length) (baseStart_3499155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499155 prefixEnd_3499155 := by exact prefixLift 3499155
  have htrace : WordTrace (prefixWord ++ tailWord_3499155) baseStart_3499155 baseEnd_3499155 := by
    simpa [prefixWord, tailWord_3499155, baseEnd_3499155] using wordTrace_append hprefix tailTrace_3499155
  have hstable : (prefixWord ++ tailWord_3499155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499155).length < 2 ^ (prefixWord ++ tailWord_3499155).sum := by decide
  have hdescent : baseEnd_3499155 < baseStart_3499155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499165 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3499165 : Nat := 118140960795 + 3499165 * 2 ^ 59
def prefixEnd_3499165 : Nat := 4983230072969 + 3 ^ 40 * 3499165 * 2
def baseEnd_3499165 : Nat := 1796753534389907234545139

theorem tailTrace_3499165 : CollatzResearch.WordTrace tailWord_3499165 prefixEnd_3499165 1796753534389907234545139 := by
  unfold tailWord_3499165
  simp only [CollatzResearch.WordTrace]
  refine ⟨127625032368130289648962949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85083354912086859765975299 127625032368130289648962949)
  ·
    refine ⟨23929693569024429309180553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127625032368130289648962949 23929693569024429309180553)
    ·
      refine ⟨17947270176768321981885415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23929693569024429309180553 17947270176768321981885415)
      ·
        refine ⟨26920905265152482972828123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17947270176768321981885415 26920905265152482972828123)
        ·
          refine ⟨40381357897728724459242185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26920905265152482972828123 40381357897728724459242185)
          ·
            refine ⟨30286018423296543344431639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40381357897728724459242185 30286018423296543344431639)
            ·
              refine ⟨45429027634944815016647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30286018423296543344431639 45429027634944815016647459)
              ·
                refine ⟨68143541452417222524971189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45429027634944815016647459 68143541452417222524971189)
                ·
                  refine ⟨6388457011164114611716049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68143541452417222524971189 6388457011164114611716049)
                  ·
                    refine ⟨4791342758373085958787037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6388457011164114611716049 4791342758373085958787037)
                    ·
                      refine ⟨1796753534389907234545139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4791342758373085958787037 1796753534389907234545139)
                      ·
                        rfl

theorem cell23_3499165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3499165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499165 prefixEnd_3499165 := by exact prefixLift 3499165
  have htrace : WordTrace (prefixWord ++ tailWord_3499165) baseStart_3499165 baseEnd_3499165 := by
    simpa [prefixWord, tailWord_3499165, baseEnd_3499165] using wordTrace_append hprefix tailTrace_3499165
  have hstable : (prefixWord ++ tailWord_3499165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499165).length < 2 ^ (prefixWord ++ tailWord_3499165).sum := by decide
  have hdescent : baseEnd_3499165 < baseStart_3499165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499172 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_3499172 : Nat := 118140960795 + 3499172 * 2 ^ 59
def prefixEnd_3499172 : Nat := 4983230072969 + 3 ^ 40 * 3499172 * 2
def baseEnd_3499172 : Nat := 598919042918162902385869

theorem tailTrace_3499172 : CollatzResearch.WordTrace tailWord_3499172 prefixEnd_3499172 598919042918162902385869 := by
  unfold tailWord_3499172
  simp only [CollatzResearch.WordTrace]
  refine ⟨63812643839552464922233885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85083525119403286562978513 63812643839552464922233885)
  ·
    refine ⟨23929741439832174345837707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63812643839552464922233885 23929741439832174345837707)
    ·
      refine ⟨35894612159748261518756561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23929741439832174345837707 35894612159748261518756561)
      ·
        refine ⟨26920959119811196139067421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35894612159748261518756561 26920959119811196139067421)
        ·
          refine ⟨10095359669929198552150283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26920959119811196139067421 10095359669929198552150283)
          ·
            refine ⟨15143039504893797828225425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095359669929198552150283 15143039504893797828225425)
            ·
              refine ⟨11357279628670348371169069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15143039504893797828225425 11357279628670348371169069)
              ·
                refine ⟨4258979860751380639188401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11357279628670348371169069 4258979860751380639188401)
                ·
                  refine ⟨3194234895563535479391301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4258979860751380639188401 3194234895563535479391301)
                  ·
                    refine ⟨598919042918162902385869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194234895563535479391301 598919042918162902385869)
                    ·
                      rfl

theorem cell23_3499172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_3499172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499172 prefixEnd_3499172 := by exact prefixLift 3499172
  have htrace : WordTrace (prefixWord ++ tailWord_3499172) baseStart_3499172 baseEnd_3499172 := by
    simpa [prefixWord, tailWord_3499172, baseEnd_3499172] using wordTrace_append hprefix tailTrace_3499172
  have hstable : (prefixWord ++ tailWord_3499172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499172).length < 2 ^ (prefixWord ++ tailWord_3499172).sum := by decide
  have hdescent : baseEnd_3499172 < baseStart_3499172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499190 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3499190 : Nat := 118140960795 + 3499190 * 2 ^ 59
def prefixEnd_3499190 : Nat := 4983230072969 + 3 ^ 40 * 3499190 * 2
def baseEnd_3499190 : Nat := 1796766371406269636732525

theorem tailTrace_3499190 : CollatzResearch.WordTrace tailWord_3499190 prefixEnd_3499190 1796766371406269636732525 := by
  unfold tailWord_3499190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976621512064982432413939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85083962795359812612415349 7976621512064982432413939)
  ·
    refine ⟨11964932268097473648620909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7976621512064982432413939 11964932268097473648620909)
    ·
      refine ⟨4486849600536552618232841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11964932268097473648620909 4486849600536552618232841)
      ·
        refine ⟨3365137200402414463674631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486849600536552618232841 3365137200402414463674631)
        ·
          refine ⟨5047705800603621695511947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365137200402414463674631 5047705800603621695511947)
          ·
            refine ⟨7571558700905432543267921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5047705800603621695511947 7571558700905432543267921)
            ·
              refine ⟨5678669025679074407450941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7571558700905432543267921 5678669025679074407450941)
              ·
                refine ⟨2129500884629652902794103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5678669025679074407450941 2129500884629652902794103)
                ·
                  refine ⟨3194251326944479354191155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129500884629652902794103 3194251326944479354191155)
                  ·
                    refine ⟨4791376990416719031286733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194251326944479354191155 4791376990416719031286733)
                    ·
                      refine ⟨1796766371406269636732525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4791376990416719031286733 1796766371406269636732525)
                      ·
                        rfl

theorem cell23_3499190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3499190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499190 prefixEnd_3499190 := by exact prefixLift 3499190
  have htrace : WordTrace (prefixWord ++ tailWord_3499190) baseStart_3499190 baseEnd_3499190 := by
    simpa [prefixWord, tailWord_3499190, baseEnd_3499190] using wordTrace_append hprefix tailTrace_3499190
  have hstable : (prefixWord ++ tailWord_3499190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499190).length < 2 ^ (prefixWord ++ tailWord_3499190).sum := by decide
  have hdescent : baseEnd_3499190 < baseStart_3499190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499196 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_3499196 : Nat := 118140960795 + 3499196 * 2 ^ 59
def prefixEnd_3499196 : Nat := 4983230072969 + 3 ^ 40 * 3499196 * 2
def baseEnd_3499196 : Nat := 1796769452290196613257497

theorem tailTrace_3499196 : CollatzResearch.WordTrace tailWord_3499196 prefixEnd_3499196 1796769452290196613257497 := by
  unfold tailWord_3499196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63813081515508990971670721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85084108687345321295560961 63813081515508990971670721)
  ·
    refine ⟨47859811136631743228753041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63813081515508990971670721 47859811136631743228753041)
    ·
      refine ⟨35894858352473807421564781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47859811136631743228753041 35894858352473807421564781)
      ·
        refine ⟨13460571882177677783086793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35894858352473807421564781 13460571882177677783086793)
        ·
          refine ⟨10095428911633258337315095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13460571882177677783086793 10095428911633258337315095)
          ·
            refine ⟨15143143367449887505972643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095428911633258337315095 15143143367449887505972643)
            ·
              refine ⟨22714715051174831258958965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15143143367449887505972643 22714715051174831258958965)
              ·
                refine ⟨2129504536047640430527403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22714715051174831258958965 2129504536047640430527403)
                ·
                  refine ⟨3194256804071460645791105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129504536047640430527403 3194256804071460645791105)
                  ·
                    refine ⟨2395692603053595484343329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194256804071460645791105 2395692603053595484343329)
                    ·
                      refine ⟨1796769452290196613257497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395692603053595484343329 1796769452290196613257497)
                      ·
                        rfl

theorem cell23_3499196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_3499196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499196 prefixEnd_3499196 := by exact prefixLift 3499196
  have htrace : WordTrace (prefixWord ++ tailWord_3499196) baseStart_3499196 baseEnd_3499196 := by
    simpa [prefixWord, tailWord_3499196, baseEnd_3499196] using wordTrace_append hprefix tailTrace_3499196
  have hstable : (prefixWord ++ tailWord_3499196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499196).length < 2 ^ (prefixWord ++ tailWord_3499196).sum := by decide
  have hdescent : baseEnd_3499196 < baseStart_3499196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499269 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_3499269 : Nat := 118140960795 + 3499269 * 2 ^ 59
def prefixEnd_3499269 : Nat := 4983230072969 + 3 ^ 40 * 3499269 * 2
def baseEnd_3499269 : Nat := 1796806936377974827644661

theorem tailTrace_3499269 : CollatzResearch.WordTrace tailWord_3499269 prefixEnd_3499269 1796806936377974827644661 := by
  unfold tailWord_3499269
  simp only [CollatzResearch.WordTrace]
  refine ⟨127628825559753515410748861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85085883706502343607165907 127628825559753515410748861)
  ·
    refine ⟨47860809584907568279030823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127628825559753515410748861 47860809584907568279030823)
    ·
      refine ⟨71791214377361352418546235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47860809584907568279030823 71791214377361352418546235)
      ·
        refine ⟨107686821566042028627819353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71791214377361352418546235 107686821566042028627819353)
        ·
          refine ⟨80765116174531521470864515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107686821566042028627819353 80765116174531521470864515)
          ·
            refine ⟨121147674261797282206296773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80765116174531521470864515 121147674261797282206296773)
            ·
              refine ⟨22715188924086990413680645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121147674261797282206296773 22715188924086990413680645)
              ·
                refine ⟨4259097923266310702565121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22715188924086990413680645 4259097923266310702565121)
                ·
                  refine ⟨3194323442449733026923841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259097923266310702565121 3194323442449733026923841)
                  ·
                    refine ⟨2395742581837299770192881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194323442449733026923841 2395742581837299770192881)
                    ·
                      refine ⟨1796806936377974827644661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395742581837299770192881 1796806936377974827644661)
                      ·
                        rfl

theorem cell23_3499269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_3499269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499269 prefixEnd_3499269 := by exact prefixLift 3499269
  have htrace : WordTrace (prefixWord ++ tailWord_3499269) baseStart_3499269 baseEnd_3499269 := by
    simpa [prefixWord, tailWord_3499269, baseEnd_3499269] using wordTrace_append hprefix tailTrace_3499269
  have hstable : (prefixWord ++ tailWord_3499269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499269).length < 2 ^ (prefixWord ++ tailWord_3499269).sum := by decide
  have hdescent : baseEnd_3499269 < baseStart_3499269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499275 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 7]
def baseStart_3499275 : Nat := 118140960795 + 3499275 * 2 ^ 59
def prefixEnd_3499275 : Nat := 4983230072969 + 3 ^ 40 * 3499275 * 2
def baseEnd_3499275 : Nat := 199645557473544644907737

theorem tailTrace_3499275 : CollatzResearch.WordTrace tailWord_3499275 prefixEnd_3499275 199645557473544644907737 := by
  unfold tailWord_3499275
  simp only [CollatzResearch.WordTrace]
  refine ⟨127629044397731778435467279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85086029598487852290311519 127629044397731778435467279)
  ·
    refine ⟨191443566596597667653200919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127629044397731778435467279 191443566596597667653200919)
    ·
      refine ⟨287165349894896501479801379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191443566596597667653200919 287165349894896501479801379)
      ·
        refine ⟨430748024842344752219702069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287165349894896501479801379 430748024842344752219702069)
        ·
          refine ⟨40382627328969820520597069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430748024842344752219702069 40382627328969820520597069)
          ·
            refine ⟨15143485248363682695223901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40382627328969820520597069 15143485248363682695223901)
            ·
              refine ⟨5678806968136381010708963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15143485248363682695223901 5678806968136381010708963)
              ·
                refine ⟨8518210452204571516063445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678806968136381010708963 8518210452204571516063445)
                ·
                  refine ⟨199645557473544644907737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8518210452204571516063445 199645557473544644907737)
                  ·
                    rfl

theorem cell23_3499275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 7].length) (baseStart_3499275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499275 prefixEnd_3499275 := by exact prefixLift 3499275
  have htrace : WordTrace (prefixWord ++ tailWord_3499275) baseStart_3499275 baseEnd_3499275 := by
    simpa [prefixWord, tailWord_3499275, baseEnd_3499275] using wordTrace_append hprefix tailTrace_3499275
  have hstable : (prefixWord ++ tailWord_3499275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499275).length < 2 ^ (prefixWord ++ tailWord_3499275).sum := by decide
  have hdescent : baseEnd_3499275 < baseStart_3499275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499285 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_3499285 : Nat := 118140960795 + 3499285 * 2 ^ 59
def prefixEnd_3499285 : Nat := 4983230072969 + 3 ^ 40 * 3499285 * 2
def baseEnd_3499285 : Nat := 1796815152068446765044587

theorem tailTrace_3499285 : CollatzResearch.WordTrace tailWord_3499285 prefixEnd_3499285 1796815152068446765044587 := by
  unfold tailWord_3499285
  simp only [CollatzResearch.WordTrace]
  refine ⟨127629409127695550143331309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85086272751797033428887539 127629409127695550143331309)
  ·
    refine ⟨47861028422885831303749241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127629409127695550143331309 47861028422885831303749241)
    ·
      refine ⟨35895771317164373477811931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47861028422885831303749241 35895771317164373477811931)
      ·
        refine ⟨53843656975746560216717897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35895771317164373477811931 53843656975746560216717897)
        ·
          refine ⟨40382742731809920162538423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53843656975746560216717897 40382742731809920162538423)
          ·
            refine ⟨60574114097714880243807635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40382742731809920162538423 60574114097714880243807635)
            ·
              refine ⟨90861171146572320365711453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60574114097714880243807635 90861171146572320365711453)
              ·
                refine ⟨34072939179964620137141795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90861171146572320365711453 34072939179964620137141795)
                ·
                  refine ⟨51109408769946930205712693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34072939179964620137141795 51109408769946930205712693)
                  ·
                    refine ⟨4791507072182524706785565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51109408769946930205712693 4791507072182524706785565)
                    ·
                      refine ⟨1796815152068446765044587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4791507072182524706785565 1796815152068446765044587)
                      ·
                        rfl

theorem cell23_3499285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_3499285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499285 prefixEnd_3499285 := by exact prefixLift 3499285
  have htrace : WordTrace (prefixWord ++ tailWord_3499285) baseStart_3499285 baseEnd_3499285 := by
    simpa [prefixWord, tailWord_3499285, baseEnd_3499285] using wordTrace_append hprefix tailTrace_3499285
  have hstable : (prefixWord ++ tailWord_3499285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499285).length < 2 ^ (prefixWord ++ tailWord_3499285).sum := by decide
  have hdescent : baseEnd_3499285 < baseStart_3499285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499315 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_3499315 : Nat := 118140960795 + 3499315 * 2 ^ 59
def prefixEnd_3499315 : Nat := 4983230072969 + 3 ^ 40 * 3499315 * 2
def baseEnd_3499315 : Nat := 1796830556488081647669449

theorem tailTrace_3499315 : CollatzResearch.WordTrace tailWord_3499315 prefixEnd_3499315 1796830556488081647669449 := by
  unfold tailWord_3499315
  simp only [CollatzResearch.WordTrace]
  refine ⟨127630503317586865266923399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85087002211724576844615599 127630503317586865266923399)
  ·
    refine ⟨191445754976380297900385099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127630503317586865266923399 191445754976380297900385099)
    ·
      refine ⟨287168632464570446850577649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191445754976380297900385099 287168632464570446850577649)
      ·
        refine ⟨215376474348427835137933237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287168632464570446850577649 215376474348427835137933237)
        ·
          refine ⟨20191544470165109544181241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215376474348427835137933237 20191544470165109544181241)
          ·
            refine ⟨15143658352623832158135931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20191544470165109544181241 15143658352623832158135931)
            ·
              refine ⟨22715487528935748237203897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15143658352623832158135931 22715487528935748237203897)
              ·
                refine ⟨17036615646701811177902923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22715487528935748237203897 17036615646701811177902923)
                ·
                  refine ⟨25554923470052716766854385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17036615646701811177902923 25554923470052716766854385)
                  ·
                    refine ⟨19166192602539537575140789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25554923470052716766854385 19166192602539537575140789)
                    ·
                      refine ⟨1796830556488081647669449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19166192602539537575140789 1796830556488081647669449)
                      ·
                        rfl

theorem cell23_3499315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_3499315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499315 prefixEnd_3499315 := by exact prefixLift 3499315
  have htrace : WordTrace (prefixWord ++ tailWord_3499315) baseStart_3499315 baseEnd_3499315 := by
    simpa [prefixWord, tailWord_3499315, baseEnd_3499315] using wordTrace_append hprefix tailTrace_3499315
  have hstable : (prefixWord ++ tailWord_3499315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499315).length < 2 ^ (prefixWord ++ tailWord_3499315).sum := by decide
  have hdescent : baseEnd_3499315 < baseStart_3499315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499329 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3499329 : Nat := 118140960795 + 3499329 * 2 ^ 59
def prefixEnd_3499329 : Nat := 4983230072969 + 3 ^ 40 * 3499329 * 2
def baseEnd_3499329 : Nat := 1796837745217244592894385

theorem tailTrace_3499329 : CollatzResearch.WordTrace tailWord_3499329 prefixEnd_3499329 1796837745217244592894385 := by
  unfold tailWord_3499329
  simp only [CollatzResearch.WordTrace]
  refine ⟨127631013939536145657933041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85087342626357430438622027 127631013939536145657933041)
  ·
    refine ⟨95723260454652109243449781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127631013939536145657933041 95723260454652109243449781)
    ·
      refine ⟨8974055667623635241573417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95723260454652109243449781 8974055667623635241573417)
      ·
        refine ⟨6730541750717726431180063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8974055667623635241573417 6730541750717726431180063)
        ·
          refine ⟨10095812626076589646770095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730541750717726431180063 10095812626076589646770095)
          ·
            refine ⟨15143718939114884470155143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10095812626076589646770095 15143718939114884470155143)
            ·
              refine ⟨22715578408672326705232715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15143718939114884470155143 22715578408672326705232715)
              ·
                refine ⟨34073367613008490057849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22715578408672326705232715 34073367613008490057849073)
                ·
                  refine ⟨25555025709756367543386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34073367613008490057849073 25555025709756367543386805)
                  ·
                    refine ⟨2395783660289659457192513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25555025709756367543386805 2395783660289659457192513)
                    ·
                      refine ⟨1796837745217244592894385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395783660289659457192513 1796837745217244592894385)
                      ·
                        rfl

theorem cell23_3499329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3499329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499329 prefixEnd_3499329 := by exact prefixLift 3499329
  have htrace : WordTrace (prefixWord ++ tailWord_3499329) baseStart_3499329 baseEnd_3499329 := by
    simpa [prefixWord, tailWord_3499329, baseEnd_3499329] using wordTrace_append hprefix tailTrace_3499329
  have hstable : (prefixWord ++ tailWord_3499329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499329).length < 2 ^ (prefixWord ++ tailWord_3499329).sum := by decide
  have hdescent : baseEnd_3499329 < baseStart_3499329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499352 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_3499352 : Nat := 118140960795 + 3499352 * 2 ^ 59
def prefixEnd_3499352 : Nat := 4983230072969 + 3 ^ 40 * 3499352 * 2
def baseEnd_3499352 : Nat := 598949851757432667635593

theorem tailTrace_3499352 : CollatzResearch.WordTrace tailWord_3499352 prefixEnd_3499352 598949851757432667635593 := by
  unfold tailWord_3499352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63815926409226410293010155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85087901878968547057346873 63815926409226410293010155)
  ·
    refine ⟨95723889613839615439515233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63815926409226410293010155 95723889613839615439515233)
    ·
      refine ⟨71792917210379711579636425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95723889613839615439515233 71792917210379711579636425)
      ·
        refine ⟨53844687907784783684727319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71792917210379711579636425 53844687907784783684727319)
        ·
          refine ⟨80767031861677175527090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53844687907784783684727319 80767031861677175527090979)
          ·
            refine ⟨121150547792515763290636469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80767031861677175527090979 121150547792515763290636469)
            ·
              refine ⟨11357863855548352808497169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121150547792515763290636469 11357863855548352808497169)
              ·
                refine ⟨8518397891661264606372877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11357863855548352808497169 8518397891661264606372877)
                ·
                  refine ⟨3194399209372974227389829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8518397891661264606372877 3194399209372974227389829)
                  ·
                    refine ⟨598949851757432667635593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194399209372974227389829 598949851757432667635593)
                    ·
                      rfl

theorem cell23_3499352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_3499352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499352 prefixEnd_3499352 := by exact prefixLift 3499352
  have htrace : WordTrace (prefixWord ++ tailWord_3499352) baseStart_3499352 baseEnd_3499352 := by
    simpa [prefixWord, tailWord_3499352, baseEnd_3499352] using wordTrace_append hprefix tailTrace_3499352
  have hstable : (prefixWord ++ tailWord_3499352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499352).length < 2 ^ (prefixWord ++ tailWord_3499352).sum := by decide
  have hdescent : baseEnd_3499352 < baseStart_3499352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499365 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 8]
def baseStart_3499365 : Nat := 118140960795 + 3499365 * 2 ^ 59
def prefixEnd_3499365 : Nat := 4983230072969 + 3 ^ 40 * 3499365 * 2
def baseEnd_3499365 : Nat := 199650692280089605782691

theorem tailTrace_3499365 : CollatzResearch.WordTrace tailWord_3499365 prefixEnd_3499365 199650692280089605782691 := by
  unfold tailWord_3499365
  simp only [CollatzResearch.WordTrace]
  refine ⟨127632326967405723806243549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85088217978270482537495699 127632326967405723806243549)
  ·
    refine ⟨47862122612777146427341331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127632326967405723806243549 47862122612777146427341331)
    ·
      refine ⟨71793183919165719641011997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47862122612777146427341331 71793183919165719641011997)
      ·
        refine ⟨26922443969687144865379499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71793183919165719641011997 26922443969687144865379499)
        ·
          refine ⟨40383665954530717298069249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26922443969687144865379499 40383665954530717298069249)
          ·
            refine ⟨30287749465898037973551937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40383665954530717298069249 30287749465898037973551937)
            ·
              refine ⟨22715812099423528480163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30287749465898037973551937 22715812099423528480163953)
              ·
                refine ⟨17036859074567646360122965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22715812099423528480163953 17036859074567646360122965)
                ·
                  refine ⟨199650692280089605782691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17036859074567646360122965 199650692280089605782691)
                  ·
                    rfl

theorem cell23_3499365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_3499365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499365 prefixEnd_3499365 := by exact prefixLift 3499365
  have htrace : WordTrace (prefixWord ++ tailWord_3499365) baseStart_3499365 baseEnd_3499365 := by
    simpa [prefixWord, tailWord_3499365, baseEnd_3499365] using wordTrace_append hprefix tailTrace_3499365
  have hstable : (prefixWord ++ tailWord_3499365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499365).length < 2 ^ (prefixWord ++ tailWord_3499365).sum := by decide
  have hdescent : baseEnd_3499365 < baseStart_3499365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499385 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3499385 : Nat := 118140960795 + 3499385 * 2 ^ 59
def prefixEnd_3499385 : Nat := 4983230072969 + 3 ^ 40 * 3499385 * 2
def baseEnd_3499385 : Nat := 1796866500133896373794127

theorem tailTrace_3499385 : CollatzResearch.WordTrace tailWord_3499385 prefixEnd_3499385 1796866500133896373794127 := by
  unfold tailWord_3499385
  simp only [CollatzResearch.WordTrace]
  refine ⟨127633056427333267221971609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85088704284888844814647739 127633056427333267221971609)
  ·
    refine ⟨95724792320499950416478707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127633056427333267221971609 95724792320499950416478707)
    ·
      refine ⟨143587188480749925624718061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95724792320499950416478707 143587188480749925624718061)
      ·
        refine ⟨53845195680281222109269273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143587188480749925624718061 53845195680281222109269273)
        ·
          refine ⟨40383896760210916581951955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53845195680281222109269273 40383896760210916581951955)
          ·
            refine ⟨60575845140316374872927933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40383896760210916581951955 60575845140316374872927933)
            ·
              refine ⟨22715941927618640577347975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60575845140316374872927933 22715941927618640577347975)
              ·
                refine ⟨34073912891427960866021963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22715941927618640577347975 34073912891427960866021963)
                ·
                  refine ⟨51110869337141941299032945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34073912891427960866021963 51110869337141941299032945)
                  ·
                    refine ⟨38333152002856455974274709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51110869337141941299032945 38333152002856455974274709)
                    ·
                      refine ⟨1796866500133896373794127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38333152002856455974274709 1796866500133896373794127)
                      ·
                        rfl

theorem cell23_3499385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3499385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499385 prefixEnd_3499385 := by exact prefixLift 3499385
  have htrace : WordTrace (prefixWord ++ tailWord_3499385) baseStart_3499385 baseEnd_3499385 := by
    simpa [prefixWord, tailWord_3499385, baseEnd_3499385] using wordTrace_append hprefix tailTrace_3499385
  have hstable : (prefixWord ++ tailWord_3499385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499385).length < 2 ^ (prefixWord ++ tailWord_3499385).sum := by decide
  have hdescent : baseEnd_3499385 < baseStart_3499385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499399 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 6]
def baseStart_3499399 : Nat := 118140960795 + 3499399 * 2 ^ 59
def prefixEnd_3499399 : Nat := 4983230072969 + 3 ^ 40 * 3499399 * 2
def baseEnd_3499399 : Nat := 199652632095895479891007

theorem tailTrace_3499399 : CollatzResearch.WordTrace tailWord_3499399 prefixEnd_3499399 199652632095895479891007 := by
  unfold tailWord_3499399
  simp only [CollatzResearch.WordTrace]
  refine ⟨127633567049282547612981251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85089044699521698408654167 127633567049282547612981251)
  ·
    refine ⟨191450350573923821419471877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127633567049282547612981251 191450350573923821419471877)
    ·
      refine ⟨35896940732610716516150977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191450350573923821419471877 35896940732610716516150977)
      ·
        refine ⟨26922705549458037387113233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35896940732610716516150977 26922705549458037387113233)
        ·
          refine ⟨20192029162093528040334925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26922705549458037387113233 20192029162093528040334925)
          ·
            refine ⟨7572010935785073015125597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20192029162093528040334925 7572010935785073015125597)
            ·
              refine ⟨2839504100919402380672099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7572010935785073015125597 2839504100919402380672099)
              ·
                refine ⟨4259256151379103571008149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2839504100919402380672099 4259256151379103571008149)
                ·
                  refine ⟨199652632095895479891007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4259256151379103571008149 199652632095895479891007)
                  ·
                    rfl

theorem cell23_3499399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 6].length) (baseStart_3499399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499399 prefixEnd_3499399 := by exact prefixLift 3499399
  have htrace : WordTrace (prefixWord ++ tailWord_3499399) baseStart_3499399 baseEnd_3499399 := by
    simpa [prefixWord, tailWord_3499399, baseEnd_3499399] using wordTrace_append hprefix tailTrace_3499399
  have hstable : (prefixWord ++ tailWord_3499399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499399).length < 2 ^ (prefixWord ++ tailWord_3499399).sum := by decide
  have hdescent : baseEnd_3499399 < baseStart_3499399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499420 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_3499420 : Nat := 118140960795 + 3499420 * 2 ^ 59
def prefixEnd_3499420 : Nat := 4983230072969 + 3 ^ 40 * 3499420 * 2
def baseEnd_3499420 : Nat := 598961490652267912285489

theorem tailTrace_3499420 : CollatzResearch.WordTrace tailWord_3499420 prefixEnd_3499420 598961490652267912285489 := by
  unfold tailWord_3499420
  simp only [CollatzResearch.WordTrace]
  refine ⟨63817166491103234099747857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85089555321470978799663809 63817166491103234099747857)
  ·
    refine ⟨47862874868327425574810893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63817166491103234099747857 47862874868327425574810893)
    ·
      refine ⟨17948578075622784590554085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47862874868327425574810893 17948578075622784590554085)
      ·
        refine ⟨3365358389179272110728891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17948578075622784590554085 3365358389179272110728891)
        ·
          refine ⟨5048037583768908166093337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365358389179272110728891 5048037583768908166093337)
          ·
            refine ⟨3786028187826681124570003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048037583768908166093337 3786028187826681124570003)
            ·
              refine ⟨5679042281740021686855005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786028187826681124570003 5679042281740021686855005)
              ·
                refine ⟨2129640855652508132570627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5679042281740021686855005 2129640855652508132570627)
                ·
                  refine ⟨3194461283478762198855941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2129640855652508132570627 3194461283478762198855941)
                  ·
                    refine ⟨598961490652267912285489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194461283478762198855941 598961490652267912285489)
                    ·
                      rfl

theorem cell23_3499420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_3499420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499420 prefixEnd_3499420 := by exact prefixLift 3499420
  have htrace : WordTrace (prefixWord ++ tailWord_3499420) baseStart_3499420 baseEnd_3499420 := by
    simpa [prefixWord, tailWord_3499420, baseEnd_3499420] using wordTrace_append hprefix tailTrace_3499420
  have hstable : (prefixWord ++ tailWord_3499420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499420).length < 2 ^ (prefixWord ++ tailWord_3499420).sum := by decide
  have hdescent : baseEnd_3499420 < baseStart_3499420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499466 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3499466 : Nat := 118140960795 + 3499466 * 2 ^ 59
def prefixEnd_3499466 : Nat := 4983230072969 + 3 ^ 40 * 3499466 * 2
def baseEnd_3499466 : Nat := 1796908092066910556881255

theorem tailTrace_3499466 : CollatzResearch.WordTrace tailWord_3499466 prefixEnd_3499466 1796908092066910556881255 := by
  unfold tailWord_3499466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31909002685009954513917563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85090673826693212037113501 31909002685009954513917563)
  ·
    refine ⟨47863504027514931770876345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31909002685009954513917563 47863504027514931770876345)
    ·
      refine ⟨35897628020636198828157259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47863504027514931770876345 35897628020636198828157259)
      ·
        refine ⟨53846442030954298242235889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35897628020636198828157259 53846442030954298242235889)
        ·
          refine ⟨40384831523215723681676917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53846442030954298242235889 40384831523215723681676917)
          ·
            refine ⟨3786077955301474095157211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40384831523215723681676917 3786077955301474095157211)
            ·
              refine ⟨5679116932952211142735817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786077955301474095157211 5679116932952211142735817)
              ·
                refine ⟨4259337699714158357051863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679116932952211142735817 4259337699714158357051863)
                ·
                  refine ⟨6389006549571237535577795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4259337699714158357051863 6389006549571237535577795)
                  ·
                    refine ⟨9583509824356856303366693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6389006549571237535577795 9583509824356856303366693)
                    ·
                      refine ⟨1796908092066910556881255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9583509824356856303366693 1796908092066910556881255)
                      ·
                        rfl

theorem cell23_3499466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3499466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499466 prefixEnd_3499466 := by exact prefixLift 3499466
  have htrace : WordTrace (prefixWord ++ tailWord_3499466) baseStart_3499466 baseEnd_3499466 := by
    simpa [prefixWord, tailWord_3499466, baseEnd_3499466] using wordTrace_append hprefix tailTrace_3499466
  have hstable : (prefixWord ++ tailWord_3499466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499466).length < 2 ^ (prefixWord ++ tailWord_3499466).sum := by decide
  have hdescent : baseEnd_3499466 < baseStart_3499466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499502 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3499502 : Nat := 118140960795 + 3499502 * 2 ^ 59
def prefixEnd_3499502 : Nat := 4983230072969 + 3 ^ 40 * 3499502 * 2
def baseEnd_3499502 : Nat := 598975525790157472010363

theorem tailTrace_3499502 : CollatzResearch.WordTrace tailWord_3499502 prefixEnd_3499502 598975525790157472010363 := by
  unfold tailWord_3499502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15954665470988674525497595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85091549178606264135987173 15954665470988674525497595)
  ·
    refine ⟨23931998206483011788246393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15954665470988674525497595 23931998206483011788246393)
    ·
      refine ⟨17948998654862258841184795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23931998206483011788246393 17948998654862258841184795)
      ·
        refine ⟨26923497982293388261777193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17948998654862258841184795 26923497982293388261777193)
        ·
          refine ⟨20192623486720041196332895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26923497982293388261777193 20192623486720041196332895)
          ·
            refine ⟨30288935230080061794499343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20192623486720041196332895 30288935230080061794499343)
            ·
              refine ⟨45433402845120092691749015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30288935230080061794499343 45433402845120092691749015)
              ·
                refine ⟨68150104267680139037623523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45433402845120092691749015 68150104267680139037623523)
                ·
                  refine ⟨102225156401520208556435285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68150104267680139037623523 102225156401520208556435285)
                  ·
                    refine ⟨598975525790157472010363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 102225156401520208556435285 598975525790157472010363)
                    ·
                      rfl

theorem cell23_3499502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3499502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499502 prefixEnd_3499502 := by exact prefixLift 3499502
  have htrace : WordTrace (prefixWord ++ tailWord_3499502) baseStart_3499502 baseEnd_3499502 := by
    simpa [prefixWord, tailWord_3499502, baseEnd_3499502] using wordTrace_append hprefix tailTrace_3499502
  have hstable : (prefixWord ++ tailWord_3499502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499502).length < 2 ^ (prefixWord ++ tailWord_3499502).sum := by decide
  have hdescent : baseEnd_3499502 < baseStart_3499502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499516 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_3499516 : Nat := 118140960795 + 3499516 * 2 ^ 59
def prefixEnd_3499516 : Nat := 4983230072969 + 3 ^ 40 * 3499516 * 2
def baseEnd_3499516 : Nat := 1796933766099635361256025

theorem tailTrace_3499516 : CollatzResearch.WordTrace tailWord_3499516 prefixEnd_3499516 1796933766099635361256025 := by
  unfold tailWord_3499516
  simp only [CollatzResearch.WordTrace]
  refine ⟨63818917194929338297495201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85091889593239117729993601 63818917194929338297495201)
  ·
    refine ⟨47864187896197003723121401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63818917194929338297495201 47864187896197003723121401)
    ·
      refine ⟨35898140922147752792341051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47864187896197003723121401 35898140922147752792341051)
      ·
        refine ⟨53847211383221629188511577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35898140922147752792341051 53847211383221629188511577)
        ·
          refine ⟨40385408537416221891383683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53847211383221629188511577 40385408537416221891383683)
          ·
            refine ⟨60578112806124332837075525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40385408537416221891383683 60578112806124332837075525)
            ·
              refine ⟨11358396151148312406951661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60578112806124332837075525 11358396151148312406951661)
              ·
                refine ⟨4259398556680617152606873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11358396151148312406951661 4259398556680617152606873)
                ·
                  refine ⟨3194548917510462864455155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259398556680617152606873 3194548917510462864455155)
                  ·
                    refine ⟨4791823376265694296682733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194548917510462864455155 4791823376265694296682733)
                    ·
                      refine ⟨1796933766099635361256025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4791823376265694296682733 1796933766099635361256025)
                      ·
                        rfl

theorem cell23_3499516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_3499516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499516 prefixEnd_3499516 := by exact prefixLift 3499516
  have htrace : WordTrace (prefixWord ++ tailWord_3499516) baseStart_3499516 baseEnd_3499516 := by
    simpa [prefixWord, tailWord_3499516, baseEnd_3499516] using wordTrace_append hprefix tailTrace_3499516
  have hstable : (prefixWord ++ tailWord_3499516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499516).length < 2 ^ (prefixWord ++ tailWord_3499516).sum := by decide
  have hdescent : baseEnd_3499516 < baseStart_3499516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499573 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_3499573 : Nat := 118140960795 + 3499573 * 2 ^ 59
def prefixEnd_3499573 : Nat := 4983230072969 + 3 ^ 40 * 3499573 * 2
def baseEnd_3499573 : Nat := 1796963034496941638243263

theorem tailTrace_3499573 : CollatzResearch.WordTrace tailWord_3499573 prefixEnd_3499573 1796963034496941638243263 := by
  unfold tailWord_3499573
  simp only [CollatzResearch.WordTrace]
  refine ⟨127639913350652175329815373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85093275567101450219876915 127639913350652175329815373)
  ·
    refine ⟨47864967506494565748680765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127639913350652175329815373 47864967506494565748680765)
    ·
      refine ⟨17949362814935462155755287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47864967506494565748680765 17949362814935462155755287)
      ·
        refine ⟨26924044222403193233632931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17949362814935462155755287 26924044222403193233632931)
        ·
          refine ⟨40386066333604789850449397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26924044222403193233632931 40386066333604789850449397)
          ·
            refine ⟨3786193718775449048479631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40386066333604789850449397 3786193718775449048479631)
            ·
              refine ⟨5679290578163173572719447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786193718775449048479631 5679290578163173572719447)
              ·
                refine ⟨8518935867244760359079171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679290578163173572719447 8518935867244760359079171)
                ·
                  refine ⟨12778403800867140538618757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518935867244760359079171 12778403800867140538618757)
                  ·
                    refine ⟨2395950712662588850991017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12778403800867140538618757 2395950712662588850991017)
                    ·
                      refine ⟨1796963034496941638243263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395950712662588850991017 1796963034496941638243263)
                      ·
                        rfl

theorem cell23_3499573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_3499573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499573 prefixEnd_3499573 := by exact prefixLift 3499573
  have htrace : WordTrace (prefixWord ++ tailWord_3499573) baseStart_3499573 baseEnd_3499573 := by
    simpa [prefixWord, tailWord_3499573, baseEnd_3499573] using wordTrace_append hprefix tailTrace_3499573
  have hstable : (prefixWord ++ tailWord_3499573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499573).length < 2 ^ (prefixWord ++ tailWord_3499573).sum := by decide
  have hdescent : baseEnd_3499573 < baseStart_3499573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499596 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 5]
def baseStart_3499596 : Nat := 118140960795 + 3499596 * 2 ^ 59
def prefixEnd_3499596 : Nat := 4983230072969 + 3 ^ 40 * 3499596 * 2
def baseEnd_3499596 : Nat := 199663871616888338695073

theorem tailTrace_3499596 : CollatzResearch.WordTrace tailWord_3499596 prefixEnd_3499596 199663871616888338695073 := by
  unfold tailWord_3499596
  simp only [CollatzResearch.WordTrace]
  refine ⟨63820376114784425128951321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85093834819712566838601761 63820376114784425128951321)
  ·
    refine ⟨47865282086088318846713491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63820376114784425128951321 47865282086088318846713491)
    ·
      refine ⟨71797923129132478270070237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47865282086088318846713491 71797923129132478270070237)
      ·
        refine ⟨26924221173424679351276339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71797923129132478270070237 26924221173424679351276339)
        ·
          refine ⟨40386331760137019026914509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26924221173424679351276339 40386331760137019026914509)
          ·
            refine ⟨15144874410051382135092941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40386331760137019026914509 15144874410051382135092941)
            ·
              refine ⟨5679327903769268300659853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15144874410051382135092941 5679327903769268300659853)
              ·
                refine ⟨2129747963913475612747445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5679327903769268300659853 2129747963913475612747445)
                ·
                  refine ⟨199663871616888338695073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2129747963913475612747445 199663871616888338695073)
                  ·
                    rfl

theorem cell23_3499596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_3499596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499596 prefixEnd_3499596 := by exact prefixLift 3499596
  have htrace : WordTrace (prefixWord ++ tailWord_3499596) baseStart_3499596 baseEnd_3499596 := by
    simpa [prefixWord, tailWord_3499596, baseEnd_3499596] using wordTrace_append hprefix tailTrace_3499596
  have hstable : (prefixWord ++ tailWord_3499596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499596).length < 2 ^ (prefixWord ++ tailWord_3499596).sum := by decide
  have hdescent : baseEnd_3499596 < baseStart_3499596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499599 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 7, 2]
def baseStart_3499599 : Nat := 118140960795 + 3499599 * 2 ^ 59
def prefixEnd_3499599 : Nat := 4983230072969 + 3 ^ 40 * 3499599 * 2
def baseEnd_3499599 : Nat := 1796976384993958536518143

theorem tailTrace_3499599 : CollatzResearch.WordTrace tailWord_3499599 prefixEnd_3499599 1796976384993958536518143 := by
  unfold tailWord_3499599
  simp only [CollatzResearch.WordTrace]
  refine ⟨127640861648557981770261851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85093907765705321180174567 127640861648557981770261851)
  ·
    refine ⟨191461292472836972655392777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127640861648557981770261851 191461292472836972655392777)
    ·
      refine ⟨143595969354627729491544583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191461292472836972655392777 143595969354627729491544583)
      ·
        refine ⟨215393954031941594237316875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143595969354627729491544583 215393954031941594237316875)
        ·
          refine ⟨323090931047912391355975313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215393954031941594237316875 323090931047912391355975313)
          ·
            refine ⟨242318198285934293516981485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323090931047912391355975313 242318198285934293516981485)
            ·
              refine ⟨90869324357225360068868057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242318198285934293516981485 90869324357225360068868057)
              ·
                refine ⟨68151993267919020051651043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90869324357225360068868057 68151993267919020051651043)
                ·
                  refine ⟨102227989901878530077476565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68151993267919020051651043 102227989901878530077476565)
                  ·
                    refine ⟨2395968513325278048690857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102227989901878530077476565 2395968513325278048690857)
                    ·
                      refine ⟨1796976384993958536518143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2395968513325278048690857 1796976384993958536518143)
                      ·
                        rfl

theorem cell23_3499599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7, 2].length) (baseStart_3499599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499599 prefixEnd_3499599 := by exact prefixLift 3499599
  have htrace : WordTrace (prefixWord ++ tailWord_3499599) baseStart_3499599 baseEnd_3499599 := by
    simpa [prefixWord, tailWord_3499599, baseEnd_3499599] using wordTrace_append hprefix tailTrace_3499599
  have hstable : (prefixWord ++ tailWord_3499599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499599).length < 2 ^ (prefixWord ++ tailWord_3499599).sum := by decide
  have hdescent : baseEnd_3499599 < baseStart_3499599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499619 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3499619 : Nat := 118140960795 + 3499619 * 2 ^ 59
def prefixEnd_3499619 : Nat := 4983230072969 + 3 ^ 40 * 3499619 * 2
def baseEnd_3499619 : Nat := 1796986654607048458268051

theorem tailTrace_3499619 : CollatzResearch.WordTrace tailWord_3499619 prefixEnd_3499619 1796986654607048458268051 := by
  unfold tailWord_3499619
  simp only [CollatzResearch.WordTrace]
  refine ⟨127641591108485525185989911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85094394072323683457326607 127641591108485525185989911)
  ·
    refine ⟨191462386662728287778984867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127641591108485525185989911 191462386662728287778984867)
    ·
      refine ⟨287193579994092431668477301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191462386662728287778984867 287193579994092431668477301)
      ·
        refine ⟨26924398124446165468919747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287193579994092431668477301 26924398124446165468919747)
        ·
          refine ⟨40386597186669248203379621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26924398124446165468919747 40386597186669248203379621)
          ·
            refine ⟨7572486972500484038133679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40386597186669248203379621 7572486972500484038133679)
            ·
              refine ⟨11358730458750726057200519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572486972500484038133679 11358730458750726057200519)
              ·
                refine ⟨17038095688126089085800779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11358730458750726057200519 17038095688126089085800779)
                ·
                  refine ⟨25557143532189133628701169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17038095688126089085800779 25557143532189133628701169)
                  ·
                    refine ⟨19167857649141850221525877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25557143532189133628701169 19167857649141850221525877)
                    ·
                      refine ⟨1796986654607048458268051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19167857649141850221525877 1796986654607048458268051)
                      ·
                        rfl

theorem cell23_3499619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3499619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499619 prefixEnd_3499619 := by exact prefixLift 3499619
  have htrace : WordTrace (prefixWord ++ tailWord_3499619) baseStart_3499619 baseEnd_3499619 := by
    simpa [prefixWord, tailWord_3499619, baseEnd_3499619] using wordTrace_append hprefix tailTrace_3499619
  have hstable : (prefixWord ++ tailWord_3499619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499619).length < 2 ^ (prefixWord ++ tailWord_3499619).sum := by decide
  have hdescent : baseEnd_3499619 < baseStart_3499619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499639 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 5, 4]
def baseStart_3499639 : Nat := 118140960795 + 3499639 * 2 ^ 59
def prefixEnd_3499639 : Nat := 4983230072969 + 3 ^ 40 * 3499639 * 2
def baseEnd_3499639 : Nat := 598998974740046126672653

theorem tailTrace_3499639 : CollatzResearch.WordTrace tailWord_3499639 prefixEnd_3499639 598998974740046126672653 := by
  unfold tailWord_3499639
  simp only [CollatzResearch.WordTrace]
  refine ⟨127642320568413068601717971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85094880378942045734478647 127642320568413068601717971)
  ·
    refine ⟨191463480852619602902576957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127642320568413068601717971 191463480852619602902576957)
    ·
      refine ⟨71798805319732351088466359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191463480852619602902576957 71798805319732351088466359)
      ·
        refine ⟨107698207979598526632699539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71798805319732351088466359 107698207979598526632699539)
        ·
          refine ⟨161547311969397789949049309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107698207979598526632699539 161547311969397789949049309)
          ·
            refine ⟨60580241988524171230893491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161547311969397789949049309 60580241988524171230893491)
            ·
              refine ⟨90870362982786256846340237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60580241988524171230893491 90870362982786256846340237)
              ·
                refine ⟨34076386118544846317377589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90870362982786256846340237 34076386118544846317377589)
                ·
                  refine ⟨3194661198613579342254149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34076386118544846317377589 3194661198613579342254149)
                  ·
                    refine ⟨598998974740046126672653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3194661198613579342254149 598998974740046126672653)
                    ·
                      rfl

theorem cell23_3499639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_3499639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499639 prefixEnd_3499639 := by exact prefixLift 3499639
  have htrace : WordTrace (prefixWord ++ tailWord_3499639) baseStart_3499639 baseEnd_3499639 := by
    simpa [prefixWord, tailWord_3499639, baseEnd_3499639] using wordTrace_append hprefix tailTrace_3499639
  have hstable : (prefixWord ++ tailWord_3499639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499639).length < 2 ^ (prefixWord ++ tailWord_3499639).sum := by decide
  have hdescent : baseEnd_3499639 < baseStart_3499639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499696 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_3499696 : Nat := 118140960795 + 3499696 * 2 ^ 59
def prefixEnd_3499696 : Nat := 4983230072969 + 3 ^ 40 * 3499696 * 2
def baseEnd_3499696 : Nat := 1797026192617444657005197

theorem tailTrace_3499696 : CollatzResearch.WordTrace tailWord_3499696 prefixEnd_3499696 1797026192617444657005197 := by
  unfold tailWord_3499696
  simp only [CollatzResearch.WordTrace]
  refine ⟨63822199764603283668271471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85096266352804378224361961 63822199764603283668271471)
  ·
    refine ⟨95733299646904925502407207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63822199764603283668271471 95733299646904925502407207)
    ·
      refine ⟨143599949470357388253610811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95733299646904925502407207 143599949470357388253610811)
      ·
        refine ⟨215399924205536082380416217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143599949470357388253610811 215399924205536082380416217)
        ·
          refine ⟨161549943154152061785312163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215399924205536082380416217 161549943154152061785312163)
          ·
            refine ⟨242324914731228092677968245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161549943154152061785312163 242324914731228092677968245)
            ·
              refine ⟨22717960756052633688559523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242324914731228092677968245 22717960756052633688559523)
              ·
                refine ⟨34076941134078950532839285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22717960756052633688559523 34076941134078950532839285)
                ·
                  refine ⟨3194713231319901612453683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34076941134078950532839285 3194713231319901612453683)
                  ·
                    refine ⟨4792069846979852418680525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194713231319901612453683 4792069846979852418680525)
                    ·
                      refine ⟨1797026192617444657005197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792069846979852418680525 1797026192617444657005197)
                      ·
                        rfl

theorem cell23_3499696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_3499696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499696 prefixEnd_3499696 := by exact prefixLift 3499696
  have htrace : WordTrace (prefixWord ++ tailWord_3499696) baseStart_3499696 baseEnd_3499696 := by
    simpa [prefixWord, tailWord_3499696, baseEnd_3499696] using wordTrace_append hprefix tailTrace_3499696
  have hstable : (prefixWord ++ tailWord_3499696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499696).length < 2 ^ (prefixWord ++ tailWord_3499696).sum := by decide
  have hdescent : baseEnd_3499696 < baseStart_3499696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499699 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 3, 5]
def baseStart_3499699 : Nat := 118140960795 + 3499699 * 2 ^ 59
def prefixEnd_3499699 : Nat := 4983230072969 + 3 ^ 40 * 3499699 * 2
def baseEnd_3499699 : Nat := 599009244353136048422561

theorem tailTrace_3499699 : CollatzResearch.WordTrace tailWord_3499699 prefixEnd_3499699 599009244353136048422561 := by
  unfold tailWord_3499699
  simp only [CollatzResearch.WordTrace]
  refine ⟨127644508948195698848902151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85096339298797132565934767 127644508948195698848902151)
  ·
    refine ⟨191466763422293548273353227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127644508948195698848902151 191466763422293548273353227)
    ·
      refine ⟨287200145133440322410029841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191466763422293548273353227 287200145133440322410029841)
      ·
        refine ⟨215400108850080241807522381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287200145133440322410029841 215400108850080241807522381)
        ·
          refine ⟨80775040818780090677820893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215400108850080241807522381 80775040818780090677820893)
          ·
            refine ⟨30290640307042534004182835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80775040818780090677820893 30290640307042534004182835)
            ·
              refine ⟨45435960460563801006274253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30290640307042534004182835 45435960460563801006274253)
              ·
                refine ⟨17038485172711425377352845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45435960460563801006274253 17038485172711425377352845)
                ·
                  refine ⟨6389431939766784516507317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17038485172711425377352845 6389431939766784516507317)
                  ·
                    refine ⟨599009244353136048422561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6389431939766784516507317 599009244353136048422561)
                    ·
                      rfl

theorem cell23_3499699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 5].length) (baseStart_3499699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499699 prefixEnd_3499699 := by exact prefixLift 3499699
  have htrace : WordTrace (prefixWord ++ tailWord_3499699) baseStart_3499699 baseEnd_3499699 := by
    simpa [prefixWord, tailWord_3499699, baseEnd_3499699] using wordTrace_append hprefix tailTrace_3499699
  have hstable : (prefixWord ++ tailWord_3499699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499699).length < 2 ^ (prefixWord ++ tailWord_3499699).sum := by decide
  have hdescent : baseEnd_3499699 < baseStart_3499699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499730 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3499730 : Nat := 118140960795 + 3499730 * 2 ^ 59
def prefixEnd_3499730 : Nat := 4983230072969 + 3 ^ 40 * 3499730 * 2
def baseEnd_3499730 : Nat := 1797043650959697523980041

theorem tailTrace_3499730 : CollatzResearch.WordTrace tailWord_3499730 prefixEnd_3499730 1797043650959697523980041 := by
  unfold tailWord_3499730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31911409902770847785820161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85097093074055594095520429 31911409902770847785820161)
  ·
    refine ⟨23933557427078135839365121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31911409902770847785820161 23933557427078135839365121)
    ·
      refine ⟨17950168070308601879523841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23933557427078135839365121 17950168070308601879523841)
      ·
        refine ⟨13462626052731451409642881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17950168070308601879523841 13462626052731451409642881)
        ·
          refine ⟨10096969539548588557232161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13462626052731451409642881 10096969539548588557232161)
          ·
            refine ⟨7572727154661441417924121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096969539548588557232161 7572727154661441417924121)
            ·
              refine ⟨5679545365996081063443091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7572727154661441417924121 5679545365996081063443091)
              ·
                refine ⟨8519318048994121595164637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5679545365996081063443091 8519318048994121595164637)
                ·
                  refine ⟨3194744268372795598186739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8519318048994121595164637 3194744268372795598186739)
                  ·
                    refine ⟨4792116402559193397280109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194744268372795598186739 4792116402559193397280109)
                    ·
                      refine ⟨1797043650959697523980041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792116402559193397280109 1797043650959697523980041)
                      ·
                        rfl

theorem cell23_3499730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3499730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499730 prefixEnd_3499730 := by exact prefixLift 3499730
  have htrace : WordTrace (prefixWord ++ tailWord_3499730) baseStart_3499730 baseEnd_3499730 := by
    simpa [prefixWord, tailWord_3499730, baseEnd_3499730] using wordTrace_append hprefix tailTrace_3499730
  have hstable : (prefixWord ++ tailWord_3499730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499730).length < 2 ^ (prefixWord ++ tailWord_3499730).sum := by decide
  have hdescent : baseEnd_3499730 < baseStart_3499730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499756 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_3499756 : Nat := 118140960795 + 3499756 * 2 ^ 59
def prefixEnd_3499756 : Nat := 4983230072969 + 3 ^ 40 * 3499756 * 2
def baseEnd_3499756 : Nat := 1797057001456714422254921

theorem tailTrace_3499756 : CollatzResearch.WordTrace tailWord_3499756 prefixEnd_3499756 1797057001456714422254921 := by
  unfold tailWord_3499756
  simp only [CollatzResearch.WordTrace]
  refine ⟨63823293954494598791863561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85097725272659465055818081 63823293954494598791863561)
  ·
    refine ⟨47867470465870949093897671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63823293954494598791863561 47867470465870949093897671)
    ·
      refine ⟨71801205698806423640846507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47867470465870949093897671 71801205698806423640846507)
      ·
        refine ⟨107701808548209635461269761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71801205698806423640846507 107701808548209635461269761)
        ·
          refine ⟨80776356411157226595952321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107701808548209635461269761 80776356411157226595952321)
          ·
            refine ⟨60582267308367919946964241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80776356411157226595952321 60582267308367919946964241)
            ·
              refine ⟨45436700481275939960223181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60582267308367919946964241 45436700481275939960223181)
              ·
                refine ⟨17038762680478477485083693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45436700481275939960223181 17038762680478477485083693)
                ·
                  refine ⟨6389536005179429056906385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17038762680478477485083693 6389536005179429056906385)
                  ·
                    refine ⟨4792152003884571792679789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6389536005179429056906385 4792152003884571792679789)
                    ·
                      refine ⟨1797057001456714422254921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792152003884571792679789 1797057001456714422254921)
                      ·
                        rfl

theorem cell23_3499756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_3499756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499756 prefixEnd_3499756 := by exact prefixLift 3499756
  have htrace : WordTrace (prefixWord ++ tailWord_3499756) baseStart_3499756 baseEnd_3499756 := by
    simpa [prefixWord, tailWord_3499756, baseEnd_3499756] using wordTrace_append hprefix tailTrace_3499756
  have hstable : (prefixWord ++ tailWord_3499756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499756).length < 2 ^ (prefixWord ++ tailWord_3499756).sum := by decide
  have hdescent : baseEnd_3499756 < baseStart_3499756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499759 : List Nat := [1, 1, 2, 1, 5, 1, 3, 9]
def baseStart_3499759 : Nat := 118140960795 + 3499759 * 2 ^ 59
def prefixEnd_3499759 : Nat := 4983230072969 + 3 ^ 40 * 3499759 * 2
def baseEnd_3499759 : Nat := 66557723774025107796941

theorem tailTrace_3499759 : CollatzResearch.WordTrace tailWord_3499759 prefixEnd_3499759 66557723774025107796941 := by
  unfold tailWord_3499759
  simp only [CollatzResearch.WordTrace]
  refine ⟨127646697327978329096086331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85097798218652219397390887 127646697327978329096086331)
  ·
    refine ⟨191470045991967493644129497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127646697327978329096086331 191470045991967493644129497)
    ·
      refine ⟨143602534493975620233097123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191470045991967493644129497 143602534493975620233097123)
      ·
        refine ⟨215403801740963430349645685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143602534493975620233097123 215403801740963430349645685)
        ·
          refine ⟨20194106413215321595279283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215403801740963430349645685 20194106413215321595279283)
          ·
            refine ⟨30291159619822982392918925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20194106413215321595279283 30291159619822982392918925)
            ·
              refine ⟨11359184857433618397344597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30291159619822982392918925 11359184857433618397344597)
              ·
                refine ⟨66557723774025107796941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11359184857433618397344597 66557723774025107796941)
                ·
                  rfl

theorem cell23_3499759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 9].length) (baseStart_3499759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499759 prefixEnd_3499759 := by exact prefixLift 3499759
  have htrace : WordTrace (prefixWord ++ tailWord_3499759) baseStart_3499759 baseEnd_3499759 := by
    simpa [prefixWord, tailWord_3499759, baseEnd_3499759] using wordTrace_append hprefix tailTrace_3499759
  have hstable : (prefixWord ++ tailWord_3499759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499759).length < 2 ^ (prefixWord ++ tailWord_3499759).sum := by decide
  have hdescent : baseEnd_3499759 < baseStart_3499759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499803 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 3]
def baseStart_3499803 : Nat := 118140960795 + 3499803 * 2 ^ 59
def prefixEnd_3499803 : Nat := 4983230072969 + 3 ^ 40 * 3499803 * 2
def baseEnd_3499803 : Nat := 1797081135047475738367205

theorem tailTrace_3499803 : CollatzResearch.WordTrace tailWord_3499803 prefixEnd_3499803 1797081135047475738367205 := by
  unfold tailWord_3499803
  simp only [CollatzResearch.WordTrace]
  refine ⟨127648302139818924610688063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85098868093212616407125375 127648302139818924610688063)
  ·
    refine ⟨191472453209728386916032095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127648302139818924610688063 191472453209728386916032095)
    ·
      refine ⟨287208679814592580374048143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191472453209728386916032095 287208679814592580374048143)
      ·
        refine ⟨430813019721888870561072215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287208679814592580374048143 430813019721888870561072215)
        ·
          refine ⟨646219529582833305841608323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430813019721888870561072215 646219529582833305841608323)
          ·
            refine ⟨969329294374249958762412485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646219529582833305841608323 969329294374249958762412485)
            ·
              refine ⟨181749242695171867267952341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 969329294374249958762412485 181749242695171867267952341)
              ·
                refine ⟨4259747875668090639092633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181749242695171867267952341 4259747875668090639092633)
                ·
                  refine ⟨3194810906751067979319475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259747875668090639092633 3194810906751067979319475)
                  ·
                    refine ⟨4792216360126601968979213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194810906751067979319475 4792216360126601968979213)
                    ·
                      refine ⟨1797081135047475738367205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792216360126601968979213 1797081135047475738367205)
                      ·
                        rfl

theorem cell23_3499803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 3].length) (baseStart_3499803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499803 prefixEnd_3499803 := by exact prefixLift 3499803
  have htrace : WordTrace (prefixWord ++ tailWord_3499803) baseStart_3499803 baseEnd_3499803 := by
    simpa [prefixWord, tailWord_3499803, baseEnd_3499803] using wordTrace_append hprefix tailTrace_3499803
  have hstable : (prefixWord ++ tailWord_3499803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499803).length < 2 ^ (prefixWord ++ tailWord_3499803).sum := by decide
  have hdescent : baseEnd_3499803 < baseStart_3499803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499837 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3499837 : Nat := 118140960795 + 3499837 * 2 ^ 59
def prefixEnd_3499837 : Nat := 4983230072969 + 3 ^ 40 * 3499837 * 2
def baseEnd_3499837 : Nat := 1797098593389728605342049

theorem tailTrace_3499837 : CollatzResearch.WordTrace tailWord_3499837 prefixEnd_3499837 1797098593389728605342049 := by
  unfold tailWord_3499837
  simp only [CollatzResearch.WordTrace]
  refine ⟨127649542221695748417425765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85099694814463832278283843 127649542221695748417425765)
  ·
    refine ⟨23934289166567952828267331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127649542221695748417425765 23934289166567952828267331)
    ·
      refine ⟨35901433749851929242400997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23934289166567952828267331 35901433749851929242400997)
      ·
        refine ⟨6731518828097236732950187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35901433749851929242400997 6731518828097236732950187)
        ·
          refine ⟨10097278242145855099425281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731518828097236732950187 10097278242145855099425281)
          ·
            refine ⟨7572958681609391324568961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10097278242145855099425281 7572958681609391324568961)
            ·
              refine ⟨5679719011207043493426721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7572958681609391324568961 5679719011207043493426721)
              ·
                refine ⟨4259789258405282620070041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5679719011207043493426721 4259789258405282620070041)
                ·
                  refine ⟨3194841943803961965052531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4259789258405282620070041 3194841943803961965052531)
                  ·
                    refine ⟨4792262915705942947578797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3194841943803961965052531 4792262915705942947578797)
                    ·
                      refine ⟨1797098593389728605342049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792262915705942947578797 1797098593389728605342049)
                      ·
                        rfl

theorem cell23_3499837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3499837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499837 prefixEnd_3499837 := by exact prefixLift 3499837
  have htrace : WordTrace (prefixWord ++ tailWord_3499837) baseStart_3499837 baseEnd_3499837 := by
    simpa [prefixWord, tailWord_3499837, baseEnd_3499837] using wordTrace_append hprefix tailTrace_3499837
  have hstable : (prefixWord ++ tailWord_3499837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499837).length < 2 ^ (prefixWord ++ tailWord_3499837).sum := by decide
  have hdescent : baseEnd_3499837 < baseStart_3499837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499853 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_3499853 : Nat := 118140960795 + 3499853 * 2 ^ 59
def prefixEnd_3499853 : Nat := 4983230072969 + 3 ^ 40 * 3499853 * 2
def baseEnd_3499853 : Nat := 599035603026733514247325

theorem tailTrace_3499853 : CollatzResearch.WordTrace tailWord_3499853 prefixEnd_3499853 599035603026733514247325 := by
  unfold tailWord_3499853
  simp only [CollatzResearch.WordTrace]
  refine ⟨127650125789637783150008213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85100083859758522100005475 127650125789637783150008213)
  ·
    refine ⟨5983599646389271085156635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127650125789637783150008213 5983599646389271085156635)
    ·
      refine ⟨8975399469583906627734953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983599646389271085156635 8975399469583906627734953)
      ·
        refine ⟨6731549602187929970801215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8975399469583906627734953 6731549602187929970801215)
        ·
          refine ⟨10097324403281894956201823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6731549602187929970801215 10097324403281894956201823)
          ·
            refine ⟨15145986604922842434302735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10097324403281894956201823 15145986604922842434302735)
            ·
              refine ⟨22718979907384263651454103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15145986604922842434302735 22718979907384263651454103)
              ·
                refine ⟨34078469861076395477181155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22718979907384263651454103 34078469861076395477181155)
                ·
                  refine ⟨51117704791614593215771733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34078469861076395477181155 51117704791614593215771733)
                  ·
                    refine ⟨599035603026733514247325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51117704791614593215771733 599035603026733514247325)
                    ·
                      rfl

theorem cell23_3499853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_3499853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499853 prefixEnd_3499853 := by exact prefixLift 3499853
  have htrace : WordTrace (prefixWord ++ tailWord_3499853) baseStart_3499853 baseEnd_3499853 := by
    simpa [prefixWord, tailWord_3499853, baseEnd_3499853] using wordTrace_append hprefix tailTrace_3499853
  have hstable : (prefixWord ++ tailWord_3499853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499853).length < 2 ^ (prefixWord ++ tailWord_3499853).sum := by decide
  have hdescent : baseEnd_3499853 < baseStart_3499853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499860 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_3499860 : Nat := 118140960795 + 3499860 * 2 ^ 59
def prefixEnd_3499860 : Nat := 4983230072969 + 3 ^ 40 * 3499860 * 2
def baseEnd_3499860 : Nat := 1797110403444782015354443

theorem tailTrace_3499860 : CollatzResearch.WordTrace tailWord_3499860 prefixEnd_3499860 1797110403444782015354443 := by
  unfold tailWord_3499860
  simp only [CollatzResearch.WordTrace]
  refine ⟨63825190550306211672756517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85100254067074948897008689 63825190550306211672756517)
  ·
    refine ⟨11967223228182414688641847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63825190550306211672756517 11967223228182414688641847)
    ·
      refine ⟨17950834842273622032962771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11967223228182414688641847 17950834842273622032962771)
      ·
        refine ⟨26926252263410433049444157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17950834842273622032962771 26926252263410433049444157)
        ·
          refine ⟨10097344598778912393541559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26926252263410433049444157 10097344598778912393541559)
          ·
            refine ⟨15146016898168368590312339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10097344598778912393541559 15146016898168368590312339)
            ·
              refine ⟨22719025347252552885468509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15146016898168368590312339 22719025347252552885468509)
              ·
                refine ⟨8519634505219707332050691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22719025347252552885468509 8519634505219707332050691)
                ·
                  refine ⟨12779451757829560998076037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8519634505219707332050691 12779451757829560998076037)
                  ·
                    refine ⟨2396147204593042687139257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12779451757829560998076037 2396147204593042687139257)
                    ·
                      refine ⟨1797110403444782015354443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396147204593042687139257 1797110403444782015354443)
                      ·
                        rfl

theorem cell23_3499860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_3499860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499860 prefixEnd_3499860 := by exact prefixLift 3499860
  have htrace : WordTrace (prefixWord ++ tailWord_3499860) baseStart_3499860 baseEnd_3499860 := by
    simpa [prefixWord, tailWord_3499860, baseEnd_3499860] using wordTrace_append hprefix tailTrace_3499860
  have hstable : (prefixWord ++ tailWord_3499860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499860).length < 2 ^ (prefixWord ++ tailWord_3499860).sum := by decide
  have hdescent : baseEnd_3499860 < baseStart_3499860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499866 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 7]
def baseStart_3499866 : Nat := 118140960795 + 3499866 * 2 ^ 59
def prefixEnd_3499866 : Nat := 4983230072969 + 3 ^ 40 * 3499866 * 2
def baseEnd_3499866 : Nat := 199679276036523221319935

theorem tailTrace_3499866 : CollatzResearch.WordTrace tailWord_3499866 prefixEnd_3499866 199679276036523221319935 := by
  unfold tailWord_3499866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31912649984647671592557863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85100399959060457580154301 31912649984647671592557863)
  ·
    refine ⟨47868974976971507388836795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31912649984647671592557863 47868974976971507388836795)
    ·
      refine ⟨71803462465457261083255193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47868974976971507388836795 71803462465457261083255193)
      ·
        refine ⟨53852596849092945812441395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71803462465457261083255193 53852596849092945812441395)
        ·
          refine ⟨80778895273639418718662093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53852596849092945812441395 80778895273639418718662093)
          ·
            refine ⟨30292085727614782019498285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80778895273639418718662093 30292085727614782019498285)
            ·
              refine ⟨11359532147855543257311857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30292085727614782019498285 11359532147855543257311857)
              ·
                refine ⟨8519649110891657442983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11359532147855543257311857 8519649110891657442983893)
                ·
                  refine ⟨199679276036523221319935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8519649110891657442983893 199679276036523221319935)
                  ·
                    rfl

theorem cell23_3499866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_3499866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499866 prefixEnd_3499866 := by exact prefixLift 3499866
  have htrace : WordTrace (prefixWord ++ tailWord_3499866) baseStart_3499866 baseEnd_3499866 := by
    simpa [prefixWord, tailWord_3499866, baseEnd_3499866] using wordTrace_append hprefix tailTrace_3499866
  have hstable : (prefixWord ++ tailWord_3499866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499866).length < 2 ^ (prefixWord ++ tailWord_3499866).sum := by decide
  have hdescent : baseEnd_3499866 < baseStart_3499866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499893 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3499893 : Nat := 118140960795 + 3499893 * 2 ^ 59
def prefixEnd_3499893 : Nat := 4983230072969 + 3 ^ 40 * 3499893 * 2
def baseEnd_3499893 : Nat := 1797127348306380386241791

theorem tailTrace_3499893 : CollatzResearch.WordTrace tailWord_3499893 prefixEnd_3499893 1797127348306380386241791 := by
  unfold tailWord_3499893
  simp only [CollatzResearch.WordTrace]
  refine ⟨127651584709492869981464333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85101056472995246654309555 127651584709492869981464333)
  ·
    refine ⟨47869344266059826243049125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127651584709492869981464333 47869344266059826243049125)
    ·
      refine ⟨8975502049886217420571711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47869344266059826243049125 8975502049886217420571711)
      ·
        refine ⟨13463253074829326130857567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975502049886217420571711 13463253074829326130857567)
        ·
          refine ⟨20194879612243989196286351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13463253074829326130857567 20194879612243989196286351)
          ·
            refine ⟨30292319418365983794429527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20194879612243989196286351 30292319418365983794429527)
            ·
              refine ⟨45438479127548975691644291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30292319418365983794429527 45438479127548975691644291)
              ·
                refine ⟨68157718691323463537466437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45438479127548975691644291 68157718691323463537466437)
                ·
                  refine ⟨12779572254623149413274957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68157718691323463537466437 12779572254623149413274957)
                  ·
                    refine ⟨4792339595483681029978109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12779572254623149413274957 4792339595483681029978109)
                    ·
                      refine ⟨1797127348306380386241791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4792339595483681029978109 1797127348306380386241791)
                      ·
                        rfl

theorem cell23_3499893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3499893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499893 prefixEnd_3499893 := by exact prefixLift 3499893
  have htrace : WordTrace (prefixWord ++ tailWord_3499893) baseStart_3499893 baseEnd_3499893 := by
    simpa [prefixWord, tailWord_3499893, baseEnd_3499893] using wordTrace_append hprefix tailTrace_3499893
  have hstable : (prefixWord ++ tailWord_3499893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499893).length < 2 ^ (prefixWord ++ tailWord_3499893).sum := by decide
  have hdescent : baseEnd_3499893 < baseStart_3499893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499894 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3499894 : Nat := 118140960795 + 3499894 * 2 ^ 59
def prefixEnd_3499894 : Nat := 4983230072969 + 3 ^ 40 * 3499894 * 2
def baseEnd_3499894 : Nat := 1797127861787034882329287

theorem tailTrace_3499894 : CollatzResearch.WordTrace tailWord_3499894 prefixEnd_3499894 1797127861787034882329287 := by
  unfold tailWord_3499894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978226323905577947015671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85101080788326164768167157 7978226323905577947015671)
  ·
    refine ⟨11967339485858366920523507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7978226323905577947015671 11967339485858366920523507)
    ·
      refine ⟨17951009228787550380785261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11967339485858366920523507 17951009228787550380785261)
      ·
        refine ⟨6731628460795331392794473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17951009228787550380785261 6731628460795331392794473)
        ·
          refine ⟨5048721345596498544595855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6731628460795331392794473 5048721345596498544595855)
          ·
            refine ⟨7573082018394747816893783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048721345596498544595855 7573082018394747816893783)
            ·
              refine ⟨11359623027592121725340675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7573082018394747816893783 11359623027592121725340675)
              ·
                refine ⟨17039434541388182588011013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359623027592121725340675 17039434541388182588011013)
                ·
                  refine ⟨3194893976510284235252065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17039434541388182588011013 3194893976510284235252065)
                  ·
                    refine ⟨2396170482382713176439049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3194893976510284235252065 2396170482382713176439049)
                    ·
                      refine ⟨1797127861787034882329287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396170482382713176439049 1797127861787034882329287)
                      ·
                        rfl

theorem cell23_3499894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3499894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499894 prefixEnd_3499894 := by exact prefixLift 3499894
  have htrace : WordTrace (prefixWord ++ tailWord_3499894) baseStart_3499894 baseEnd_3499894 := by
    simpa [prefixWord, tailWord_3499894, baseEnd_3499894] using wordTrace_append hprefix tailTrace_3499894
  have hstable : (prefixWord ++ tailWord_3499894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499894).length < 2 ^ (prefixWord ++ tailWord_3499894).sum := by decide
  have hdescent : baseEnd_3499894 < baseStart_3499894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499933 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3499933 : Nat := 118140960795 + 3499933 * 2 ^ 59
def prefixEnd_3499933 : Nat := 4983230072969 + 3 ^ 40 * 3499933 * 2
def baseEnd_3499933 : Nat := 1797147887532560229741607

theorem tailTrace_3499933 : CollatzResearch.WordTrace tailWord_3499933 prefixEnd_3499933 1797147887532560229741607 := by
  unfold tailWord_3499933
  simp only [CollatzResearch.WordTrace]
  refine ⟨127653043629347956812920453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85102029086231971208613635 127653043629347956812920453)
  ·
    refine ⟨23934945680502741902422585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127653043629347956812920453 23934945680502741902422585)
    ·
      refine ⟨17951209260377056426816939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23934945680502741902422585 17951209260377056426816939)
      ·
        refine ⟨26926813890565584640225409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17951209260377056426816939 26926813890565584640225409)
        ·
          refine ⟨20195110417924188480169057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26926813890565584640225409 20195110417924188480169057)
          ·
            refine ⟨15146332813443141360126793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20195110417924188480169057 15146332813443141360126793)
            ·
              refine ⟨11359749610082356020095095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15146332813443141360126793 11359749610082356020095095)
              ·
                refine ⟨17039624415123534030142643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11359749610082356020095095 17039624415123534030142643)
                ·
                  refine ⟨25559436622685301045213965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17039624415123534030142643 25559436622685301045213965)
                  ·
                    refine ⟨9584788733506987891955237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25559436622685301045213965 9584788733506987891955237)
                    ·
                      refine ⟨1797147887532560229741607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9584788733506987891955237 1797147887532560229741607)
                      ·
                        rfl

theorem cell23_3499933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3499933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499933 prefixEnd_3499933 := by exact prefixLift 3499933
  have htrace : WordTrace (prefixWord ++ tailWord_3499933) baseStart_3499933 baseEnd_3499933 := by
    simpa [prefixWord, tailWord_3499933, baseEnd_3499933] using wordTrace_append hprefix tailTrace_3499933
  have hstable : (prefixWord ++ tailWord_3499933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499933).length < 2 ^ (prefixWord ++ tailWord_3499933).sum := by decide
  have hdescent : baseEnd_3499933 < baseStart_3499933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3499936 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3499936 : Nat := 118140960795 + 3499936 * 2 ^ 59
def prefixEnd_3499936 : Nat := 4983230072969 + 3 ^ 40 * 3499936 * 2
def baseEnd_3499936 : Nat := 1797149427974523718004093

theorem tailTrace_3499936 : CollatzResearch.WordTrace tailWord_3499936 prefixEnd_3499936 1797149427974523718004093 := by
  unfold tailWord_3499936
  simp only [CollatzResearch.WordTrace]
  refine ⟨63826576524168544162639831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85102102032224725550186441 63826576524168544162639831)
  ·
    refine ⟨95739864786252816243959747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63826576524168544162639831 95739864786252816243959747)
    ·
      refine ⟨143609797179379224365939621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95739864786252816243959747 143609797179379224365939621)
      ·
        refine ⟨26926836971133604568613679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143609797179379224365939621 26926836971133604568613679)
        ·
          refine ⟨40390255456700406852920519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26926836971133604568613679 40390255456700406852920519)
          ·
            refine ⟨60585383185050610279380779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40390255456700406852920519 60585383185050610279380779)
            ·
              refine ⟨90878074777575915419071169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60585383185050610279380779 90878074777575915419071169)
              ·
                refine ⟨68158556083181936564303377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90878074777575915419071169 68158556083181936564303377)
                ·
                  refine ⟨51118917062386452423227533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68158556083181936564303377 51118917062386452423227533)
                  ·
                    refine ⟨19169593898394919658710325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51118917062386452423227533 19169593898394919658710325)
                    ·
                      refine ⟨1797149427974523718004093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19169593898394919658710325 1797149427974523718004093)
                      ·
                        rfl

theorem cell23_3499936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3499936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3499936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3499936 prefixEnd_3499936 := by exact prefixLift 3499936
  have htrace : WordTrace (prefixWord ++ tailWord_3499936) baseStart_3499936 baseEnd_3499936 := by
    simpa [prefixWord, tailWord_3499936, baseEnd_3499936] using wordTrace_append hprefix tailTrace_3499936
  have hstable : (prefixWord ++ tailWord_3499936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3499936).length < 2 ^ (prefixWord ++ tailWord_3499936).sum := by decide
  have hdescent : baseEnd_3499936 < baseStart_3499936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3499936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500040 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3500040 : Nat := 118140960795 + 3500040 * 2 ^ 59
def prefixEnd_3500040 : Nat := 4983230072969 + 3 ^ 40 * 3500040 * 2
def baseEnd_3500040 : Nat := 1797202829962591311103615

theorem tailTrace_3500040 : CollatzResearch.WordTrace tailWord_3500040 prefixEnd_3500040 1797202829962591311103615 := by
  unfold tailWord_3500040
  simp only [CollatzResearch.WordTrace]
  refine ⟨63828473119980157043532787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85104630826640209391377049 63828473119980157043532787)
  ·
    refine ⟨95742709679970235565299181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63828473119980157043532787 95742709679970235565299181)
    ·
      refine ⟨35903516129988838336987193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95742709679970235565299181 35903516129988838336987193)
      ·
        refine ⟨26927637097491628752740395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35903516129988838336987193 26927637097491628752740395)
        ·
          refine ⟨40391455646237443129110593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26927637097491628752740395 40391455646237443129110593)
          ·
            refine ⟨30293591734678082346832945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40391455646237443129110593 30293591734678082346832945)
            ·
              refine ⟨22720193801008561760124709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30293591734678082346832945 22720193801008561760124709)
              ·
                refine ⟨4260036337689105330023383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22720193801008561760124709 4260036337689105330023383)
                ·
                  refine ⟨6390054506533657995035075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260036337689105330023383 6390054506533657995035075)
                  ·
                    refine ⟨9585081759800486992552613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390054506533657995035075 9585081759800486992552613)
                    ·
                      refine ⟨1797202829962591311103615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9585081759800486992552613 1797202829962591311103615)
                      ·
                        rfl

theorem cell23_3500040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3500040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500040 prefixEnd_3500040 := by exact prefixLift 3500040
  have htrace : WordTrace (prefixWord ++ tailWord_3500040) baseStart_3500040 baseEnd_3500040 := by
    simpa [prefixWord, tailWord_3500040, baseEnd_3500040] using wordTrace_append hprefix tailTrace_3500040
  have hstable : (prefixWord ++ tailWord_3500040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500040).length < 2 ^ (prefixWord ++ tailWord_3500040).sum := by decide
  have hdescent : baseEnd_3500040 < baseStart_3500040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500074 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3500074 : Nat := 118140960795 + 3500074 * 2 ^ 59
def prefixEnd_3500074 : Nat := 4983230072969 + 3 ^ 40 * 3500074 * 2
def baseEnd_3500074 : Nat := 1797220288304844178078459

theorem tailTrace_3500074 : CollatzResearch.WordTrace tailWord_3500074 prefixEnd_3500074 1797220288304844178078459 := by
  unfold tailWord_3500074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914546580459284473450819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85105457547891425262535517 31914546580459284473450819)
  ·
    refine ⟨47871819870688926710176229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31914546580459284473450819 47871819870688926710176229)
    ·
      refine ⟨8975966225754173758158043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47871819870688926710176229 8975966225754173758158043)
      ·
        refine ⟨13463949338631260637237065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8975966225754173758158043 13463949338631260637237065)
        ·
          refine ⟨10097962003973445477927799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13463949338631260637237065 10097962003973445477927799)
          ·
            refine ⟨15146943005960168216891699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10097962003973445477927799 15146943005960168216891699)
            ·
              refine ⟨22720414508940252325337549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15146943005960168216891699 22720414508940252325337549)
              ·
                refine ⟨8520155440852594622001581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22720414508940252325337549 8520155440852594622001581)
                ·
                  refine ⟨3195058290319722983250593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8520155440852594622001581 3195058290319722983250593)
                  ·
                    refine ⟨2396293717739792237437945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3195058290319722983250593 2396293717739792237437945)
                    ·
                      refine ⟨1797220288304844178078459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396293717739792237437945 1797220288304844178078459)
                      ·
                        rfl

theorem cell23_3500074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3500074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500074 prefixEnd_3500074 := by exact prefixLift 3500074
  have htrace : WordTrace (prefixWord ++ tailWord_3500074) baseStart_3500074 baseEnd_3500074 := by
    simpa [prefixWord, tailWord_3500074, baseEnd_3500074] using wordTrace_append hprefix tailTrace_3500074
  have hstable : (prefixWord ++ tailWord_3500074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500074).length < 2 ^ (prefixWord ++ tailWord_3500074).sum := by decide
  have hdescent : baseEnd_3500074 < baseStart_3500074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500084 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3500084 : Nat := 118140960795 + 3500084 * 2 ^ 59
def prefixEnd_3500084 : Nat := 4983230072969 + 3 ^ 40 * 3500084 * 2
def baseEnd_3500084 : Nat := 599075141037129712984471

theorem tailTrace_3500084 : CollatzResearch.WordTrace tailWord_3500084 prefixEnd_3500084 599075141037129712984471 := by
  unfold tailWord_3500084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63829275525900454800833653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85105700701200606401111537 63829275525900454800833653)
  ·
    refine ⟨5983994580553167637578155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63829275525900454800833653 5983994580553167637578155)
    ·
      refine ⟨8975991870829751456367233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5983994580553167637578155 8975991870829751456367233)
      ·
        refine ⟨6731993903122313592275425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8975991870829751456367233 6731993903122313592275425)
        ·
          refine ⟨5048995427341735194206569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6731993903122313592275425 5048995427341735194206569)
          ·
            refine ⟨3786746570506301395654927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5048995427341735194206569 3786746570506301395654927)
            ·
              refine ⟨5680119855759452093482391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3786746570506301395654927 5680119855759452093482391)
              ·
                refine ⟨8520179783639178140223587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680119855759452093482391 8520179783639178140223587)
                ·
                  refine ⟨12780269675458767210335381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8520179783639178140223587 12780269675458767210335381)
                  ·
                    refine ⟨599075141037129712984471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12780269675458767210335381 599075141037129712984471)
                    ·
                      rfl

theorem cell23_3500084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3500084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500084 prefixEnd_3500084 := by exact prefixLift 3500084
  have htrace : WordTrace (prefixWord ++ tailWord_3500084) baseStart_3500084 baseEnd_3500084 := by
    simpa [prefixWord, tailWord_3500084, baseEnd_3500084] using wordTrace_append hprefix tailTrace_3500084
  have hstable : (prefixWord ++ tailWord_3500084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500084).length < 2 ^ (prefixWord ++ tailWord_3500084).sum := by decide
  have hdescent : baseEnd_3500084 < baseStart_3500084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500097 : List Nat := [1, 2, 5, 1, 2, 3, 2, 7]
def baseStart_3500097 : Nat := 118140960795 + 3500097 * 2 ^ 59
def prefixEnd_3500097 : Nat := 4983230072969 + 3 ^ 40 * 3500097 * 2
def baseEnd_3500097 : Nat := 66564151791107318077439

theorem tailTrace_3500097 : CollatzResearch.WordTrace tailWord_3500097 prefixEnd_3500097 66564151791107318077439 := by
  unfold tailWord_3500097
  simp only [CollatzResearch.WordTrace]
  refine ⟨127659025200753812821890545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85106016800502541881260363 127659025200753812821890545)
  ·
    refine ⟨95744268900565359616417909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127659025200753812821890545 95744268900565359616417909)
    ·
      refine ⟨8976025209428002464039179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95744268900565359616417909 8976025209428002464039179)
      ·
        refine ⟨13464037814142003696058769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976025209428002464039179 13464037814142003696058769)
        ·
          refine ⟨10098028360606502772044077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13464037814142003696058769 10098028360606502772044077)
          ·
            refine ⟨3786760635227438539516529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10098028360606502772044077 3786760635227438539516529)
            ·
              refine ⟨2840070476420578904637397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3786760635227438539516529 2840070476420578904637397)
              ·
                refine ⟨66564151791107318077439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2840070476420578904637397 66564151791107318077439)
                ·
                  rfl

theorem cell23_3500097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 7].length) (baseStart_3500097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500097 prefixEnd_3500097 := by exact prefixLift 3500097
  have htrace : WordTrace (prefixWord ++ tailWord_3500097) baseStart_3500097 baseEnd_3500097 := by
    simpa [prefixWord, tailWord_3500097, baseEnd_3500097] using wordTrace_append hprefix tailTrace_3500097
  have hstable : (prefixWord ++ tailWord_3500097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500097).length < 2 ^ (prefixWord ++ tailWord_3500097).sum := by decide
  have hdescent : baseEnd_3500097 < baseStart_3500097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500103 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3500103 : Nat := 118140960795 + 3500103 * 2 ^ 59
def prefixEnd_3500103 : Nat := 4983230072969 + 3 ^ 40 * 3500103 * 2
def baseEnd_3500103 : Nat := 1797235179243824564615825

theorem tailTrace_3500103 : CollatzResearch.WordTrace tailWord_3500103 prefixEnd_3500103 1797235179243824564615825 := by
  unfold tailWord_3500103
  simp only [CollatzResearch.WordTrace]
  refine ⟨127659244038732075846608963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85106162692488050564405975 127659244038732075846608963)
  ·
    refine ⟨191488866058098113769913445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127659244038732075846608963 191488866058098113769913445)
    ·
      refine ⟨35904162385893396331858771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191488866058098113769913445 35904162385893396331858771)
      ·
        refine ⟨53856243578840094497788157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35904162385893396331858771 53856243578840094497788157)
        ·
          refine ⟨20196091342065035436670559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53856243578840094497788157 20196091342065035436670559)
          ·
            refine ⟨30294137013097553155005839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20196091342065035436670559 30294137013097553155005839)
            ·
              refine ⟨45441205519646329732508759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30294137013097553155005839 45441205519646329732508759)
              ·
                refine ⟨68161808279469494598763139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45441205519646329732508759 68161808279469494598763139)
                ·
                  refine ⟨102242712419204241898144709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68161808279469494598763139 102242712419204241898144709)
                  ·
                    refine ⟨19170508578600795355902133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102242712419204241898144709 19170508578600795355902133)
                    ·
                      refine ⟨1797235179243824564615825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19170508578600795355902133 1797235179243824564615825)
                      ·
                        rfl

theorem cell23_3500103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3500103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500103 prefixEnd_3500103 := by exact prefixLift 3500103
  have htrace : WordTrace (prefixWord ++ tailWord_3500103) baseStart_3500103 baseEnd_3500103 := by
    simpa [prefixWord, tailWord_3500103, baseEnd_3500103] using wordTrace_append hprefix tailTrace_3500103
  have hstable : (prefixWord ++ tailWord_3500103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500103).length < 2 ^ (prefixWord ++ tailWord_3500103).sum := by decide
  have hdescent : baseEnd_3500103 < baseStart_3500103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500113 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3500113 : Nat := 118140960795 + 3500113 * 2 ^ 59
def prefixEnd_3500113 : Nat := 4983230072969 + 3 ^ 40 * 3500113 * 2
def baseEnd_3500113 : Nat := 1797240314050369525490779

theorem tailTrace_3500113 : CollatzResearch.WordTrace tailWord_3500113 prefixEnd_3500113 1797240314050369525490779 := by
  unfold tailWord_3500113
  simp only [CollatzResearch.WordTrace]
  refine ⟨127659608768695847554472993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85106405845797231702981995 127659608768695847554472993)
  ·
    refine ⟨95744706576521885665854745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127659608768695847554472993 95744706576521885665854745)
    ·
      refine ⟨71808529932391414249391059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95744706576521885665854745 71808529932391414249391059)
      ·
        refine ⟨107712794898587121374086589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71808529932391414249391059 107712794898587121374086589)
        ·
          refine ⟨40392298086970170515282471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107712794898587121374086589 40392298086970170515282471)
          ·
            refine ⟨60588447130455255772923707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40392298086970170515282471 60588447130455255772923707)
            ·
              refine ⟨90882670695682883659385561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60588447130455255772923707 90882670695682883659385561)
              ·
                refine ⟨68162003021762162744539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90882670695682883659385561 68162003021762162744539171)
                ·
                  refine ⟨102243004532643244116808757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68162003021762162744539171 102243004532643244116808757)
                  ·
                    refine ⟨9585281674935304135950821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102243004532643244116808757 9585281674935304135950821)
                    ·
                      refine ⟨1797240314050369525490779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9585281674935304135950821 1797240314050369525490779)
                      ·
                        rfl

theorem cell23_3500113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3500113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500113 prefixEnd_3500113 := by exact prefixLift 3500113
  have htrace : WordTrace (prefixWord ++ tailWord_3500113) baseStart_3500113 baseEnd_3500113 := by
    simpa [prefixWord, tailWord_3500113, baseEnd_3500113] using wordTrace_append hprefix tailTrace_3500113
  have hstable : (prefixWord ++ tailWord_3500113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500113).length < 2 ^ (prefixWord ++ tailWord_3500113).sum := by decide
  have hdescent : baseEnd_3500113 < baseStart_3500113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500125 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3500125 : Nat := 118140960795 + 3500125 * 2 ^ 59
def prefixEnd_3500125 : Nat := 4983230072969 + 3 ^ 40 * 3500125 * 2
def baseEnd_3500125 : Nat := 1797246475818223478540725

theorem tailTrace_3500125 : CollatzResearch.WordTrace tailWord_3500125 prefixEnd_3500125 1797246475818223478540725 := by
  unfold tailWord_3500125
  simp only [CollatzResearch.WordTrace]
  refine ⟨127660046444652373603909829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85106697629768249069273219 127660046444652373603909829)
  ·
    refine ⟨23936258708372320050733093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127660046444652373603909829 23936258708372320050733093)
    ·
      refine ⟨4488048507819810009512455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23936258708372320050733093 4488048507819810009512455)
      ·
        refine ⟨6732072761729715014268683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4488048507819810009512455 6732072761729715014268683)
        ·
          refine ⟨10098109142594572521403025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6732072761729715014268683 10098109142594572521403025)
          ·
            refine ⟨7573581856945929391052269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10098109142594572521403025 7573581856945929391052269)
            ·
              refine ⟨2840093196354723521644601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7573581856945929391052269 2840093196354723521644601)
              ·
                refine ⟨2130069897266042641233451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840093196354723521644601 2130069897266042641233451)
                ·
                  refine ⟨3195104845899063961850177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130069897266042641233451 3195104845899063961850177)
                  ·
                    refine ⟨2396328634424297971387633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3195104845899063961850177 2396328634424297971387633)
                    ·
                      refine ⟨1797246475818223478540725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396328634424297971387633 1797246475818223478540725)
                      ·
                        rfl

theorem cell23_3500125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3500125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500125 prefixEnd_3500125 := by exact prefixLift 3500125
  have htrace : WordTrace (prefixWord ++ tailWord_3500125) baseStart_3500125 baseEnd_3500125 := by
    simpa [prefixWord, tailWord_3500125, baseEnd_3500125] using wordTrace_append hprefix tailTrace_3500125
  have hstable : (prefixWord ++ tailWord_3500125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500125).length < 2 ^ (prefixWord ++ tailWord_3500125).sum := by decide
  have hdescent : baseEnd_3500125 < baseStart_3500125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500324 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_3500324 : Nat := 118140960795 + 3500324 * 2 ^ 59
def prefixEnd_3500324 : Nat := 4983230072969 + 3 ^ 40 * 3500324 * 2
def baseEnd_3500324 : Nat := 599116219489489399984103

theorem tailTrace_3500324 : CollatzResearch.WordTrace tailWord_3500324 prefixEnd_3500324 599116219489489399984103 := by
  unfold tailWord_3500324
  simp only [CollatzResearch.WordTrace]
  refine ⟨63833652285465715295202013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85111536380620953726936017 63833652285465715295202013)
  ·
    refine ⟨23937619607049643235700755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63833652285465715295202013 23937619607049643235700755)
    ·
      refine ⟨35906429410574464853551133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23937619607049643235700755 35906429410574464853551133)
      ·
        refine ⟨13464911028965424320081675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35906429410574464853551133 13464911028965424320081675)
        ·
          refine ⟨20197366543448136480122513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13464911028965424320081675 20197366543448136480122513)
          ·
            refine ⟨15148024907586102360091885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20197366543448136480122513 15148024907586102360091885)
            ·
              refine ⟨5680509340344788385034457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15148024907586102360091885 5680509340344788385034457)
              ·
                refine ⟨4260382005258591288775843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680509340344788385034457 4260382005258591288775843)
                ·
                  refine ⟨6390573007887886933163765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260382005258591288775843 6390573007887886933163765)
                  ·
                    refine ⟨599116219489489399984103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6390573007887886933163765 599116219489489399984103)
                    ·
                      rfl

theorem cell23_3500324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_3500324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500324 prefixEnd_3500324 := by exact prefixLift 3500324
  have htrace : WordTrace (prefixWord ++ tailWord_3500324) baseStart_3500324 baseEnd_3500324 := by
    simpa [prefixWord, tailWord_3500324, baseEnd_3500324] using wordTrace_append hprefix tailTrace_3500324
  have hstable : (prefixWord ++ tailWord_3500324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500324).length < 2 ^ (prefixWord ++ tailWord_3500324).sum := by decide
  have hdescent : baseEnd_3500324 < baseStart_3500324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500382 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3500382 : Nat := 118140960795 + 3500382 * 2 ^ 59
def prefixEnd_3500382 : Nat := 4983230072969 + 3 ^ 40 * 3500382 * 2
def baseEnd_3500382 : Nat := 1797378440346428973027043

theorem tailTrace_3500382 : CollatzResearch.WordTrace tailWord_3500382 prefixEnd_3500382 1797378440346428973027043 := by
  unfold tailWord_3500382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958677500590163312001925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85112946669814204330676933 15958677500590163312001925)
  ·
    refine ⟨2992252031360655621000361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15958677500590163312001925 2992252031360655621000361)
    ·
      refine ⟨2244189023520491715750271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2992252031360655621000361 2244189023520491715750271)
      ·
        refine ⟨3366283535280737573625407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244189023520491715750271 3366283535280737573625407)
        ·
          refine ⟨5049425302921106360438111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366283535280737573625407 5049425302921106360438111)
          ·
            refine ⟨7574137954381659540657167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049425302921106360438111 7574137954381659540657167)
            ·
              refine ⟨11361206931572489310985751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7574137954381659540657167 11361206931572489310985751)
              ·
                refine ⟨17041810397358733966478627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361206931572489310985751 17041810397358733966478627)
                ·
                  refine ⟨25562715596038100949717941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17041810397358733966478627 25562715596038100949717941)
                  ·
                    refine ⟨2396504587128571964036057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25562715596038100949717941 2396504587128571964036057)
                    ·
                      refine ⟨1797378440346428973027043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396504587128571964036057 1797378440346428973027043)
                      ·
                        rfl

theorem cell23_3500382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3500382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500382 prefixEnd_3500382 := by exact prefixLift 3500382
  have htrace : WordTrace (prefixWord ++ tailWord_3500382) baseStart_3500382 baseEnd_3500382 := by
    simpa [prefixWord, tailWord_3500382, baseEnd_3500382] using wordTrace_append hprefix tailTrace_3500382
  have hstable : (prefixWord ++ tailWord_3500382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500382).length < 2 ^ (prefixWord ++ tailWord_3500382).sum := by decide
  have hdescent : baseEnd_3500382 < baseStart_3500382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500384 : List Nat := [2, 1, 1, 3, 5, 1, 3, 7]
def baseStart_3500384 : Nat := 118140960795 + 3500384 * 2 ^ 59
def prefixEnd_3500384 : Nat := 4983230072969 + 3 ^ 40 * 3500384 * 2
def baseEnd_3500384 : Nat := 66569609900286591303779

theorem tailTrace_3500384 : CollatzResearch.WordTrace tailWord_3500384 prefixEnd_3500384 66569609900286591303779 := by
  unfold tailWord_3500384
  simp only [CollatzResearch.WordTrace]
  refine ⟨63834746475357030418794103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85112995300476040558392137 63834746475357030418794103)
  ·
    refine ⟨95752119713035545628191155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63834746475357030418794103 95752119713035545628191155)
    ·
      refine ⟨143628179569553318442286733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95752119713035545628191155 143628179569553318442286733)
      ·
        refine ⟨53860567338582494415857525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143628179569553318442286733 53860567338582494415857525)
        ·
          refine ⟨5049428187992108851486643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53860567338582494415857525 5049428187992108851486643)
          ·
            refine ⟨7574142281988163277229965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5049428187992108851486643 7574142281988163277229965)
            ·
              refine ⟨2840303355745561228961237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7574142281988163277229965 2840303355745561228961237)
              ·
                refine ⟨66569609900286591303779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2840303355745561228961237 66569609900286591303779)
                ·
                  rfl

theorem cell23_3500384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 7].length) (baseStart_3500384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500384 prefixEnd_3500384 := by exact prefixLift 3500384
  have htrace : WordTrace (prefixWord ++ tailWord_3500384) baseStart_3500384 baseEnd_3500384 := by
    simpa [prefixWord, tailWord_3500384, baseEnd_3500384] using wordTrace_append hprefix tailTrace_3500384
  have hstable : (prefixWord ++ tailWord_3500384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500384).length < 2 ^ (prefixWord ++ tailWord_3500384).sum := by decide
  have hdescent : baseEnd_3500384 < baseStart_3500384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500411 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 3]
def baseStart_3500411 : Nat := 118140960795 + 3500411 * 2 ^ 59
def prefixEnd_3500411 : Nat := 4983230072969 + 3 ^ 40 * 3500411 * 2
def baseEnd_3500411 : Nat := 1797393331285409359564409

theorem tailTrace_3500411 : CollatzResearch.WordTrace tailWord_3500411 prefixEnd_3500411 1797393331285409359564409 := by
  unfold tailWord_3500411
  simp only [CollatzResearch.WordTrace]
  refine ⟨127670477721616244448821087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85113651814410829632547391 127670477721616244448821087)
  ·
    refine ⟨191505716582424366673231631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127670477721616244448821087 191505716582424366673231631)
    ·
      refine ⟨287258574873636550009847447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191505716582424366673231631 287258574873636550009847447)
      ·
        refine ⟨430887862310454825014771171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287258574873636550009847447 430887862310454825014771171)
        ·
          refine ⟨646331793465682237522156757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430887862310454825014771171 646331793465682237522156757)
          ·
            refine ⟨15148401409351927441925549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 646331793465682237522156757 15148401409351927441925549)
            ·
              refine ⟨5680650528506972790722081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15148401409351927441925549 5680650528506972790722081)
              ·
                refine ⟨4260487896380229593041561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680650528506972790722081 4260487896380229593041561)
                ·
                  refine ⟨3195365922285172194781171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260487896380229593041561 3195365922285172194781171)
                  ·
                    refine ⟨4793048883427758292171757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195365922285172194781171 4793048883427758292171757)
                    ·
                      refine ⟨1797393331285409359564409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793048883427758292171757 1797393331285409359564409)
                      ·
                        rfl

theorem cell23_3500411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 3].length) (baseStart_3500411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500411 prefixEnd_3500411 := by exact prefixLift 3500411
  have htrace : WordTrace (prefixWord ++ tailWord_3500411) baseStart_3500411 baseEnd_3500411 := by
    simpa [prefixWord, tailWord_3500411, baseEnd_3500411] using wordTrace_append hprefix tailTrace_3500411
  have hstable : (prefixWord ++ tailWord_3500411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500411).length < 2 ^ (prefixWord ++ tailWord_3500411).sum := by decide
  have hdescent : baseEnd_3500411 < baseStart_3500411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500427 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 2, 6]
def baseStart_3500427 : Nat := 118140960795 + 3500427 * 2 ^ 59
def prefixEnd_3500427 : Nat := 4983230072969 + 3 ^ 40 * 3500427 * 2
def baseEnd_3500427 : Nat := 599133848991960432321445

theorem tailTrace_3500427 : CollatzResearch.WordTrace tailWord_3500427 prefixEnd_3500427 599133848991960432321445 := by
  unfold tailWord_3500427
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671061289558279181403535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85114040859705519454269023 127671061289558279181403535)
  ·
    refine ⟨191506591934337418772105303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127671061289558279181403535 191506591934337418772105303)
    ·
      refine ⟨287259887901506128158157955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191506591934337418772105303 287259887901506128158157955)
      ·
        refine ⟨430889831852259192237236933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287259887901506128158157955 430889831852259192237236933)
        ·
          refine ⟨80791843472298598544481925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430889831852259192237236933 80791843472298598544481925)
          ·
            refine ⟨15148470651055987227090361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80791843472298598544481925 15148470651055987227090361)
            ·
              refine ⟨11361352988291990420317771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15148470651055987227090361 11361352988291990420317771)
              ·
                refine ⟨17042029482437985630476657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361352988291990420317771 17042029482437985630476657)
                ·
                  refine ⟨12781522111828489222857493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17042029482437985630476657 12781522111828489222857493)
                  ·
                    refine ⟨599133848991960432321445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12781522111828489222857493 599133848991960432321445)
                    ·
                      rfl

theorem cell23_3500427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_3500427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500427 prefixEnd_3500427 := by exact prefixLift 3500427
  have htrace : WordTrace (prefixWord ++ tailWord_3500427) baseStart_3500427 baseEnd_3500427 := by
    simpa [prefixWord, tailWord_3500427, baseEnd_3500427] using wordTrace_append hprefix tailTrace_3500427
  have hstable : (prefixWord ++ tailWord_3500427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500427).length < 2 ^ (prefixWord ++ tailWord_3500427).sum := by decide
  have hdescent : baseEnd_3500427 < baseStart_3500427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500428 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_3500428 : Nat := 118140960795 + 3500428 * 2 ^ 59
def prefixEnd_3500428 : Nat := 4983230072969 + 3 ^ 40 * 3500428 * 2
def baseEnd_3500428 : Nat := 1797402060456535793051831

theorem tailTrace_3500428 : CollatzResearch.WordTrace tailWord_3500428 prefixEnd_3500428 1797402060456535793051831 := by
  unfold tailWord_3500428
  simp only [CollatzResearch.WordTrace]
  refine ⟨63835548881277328176094969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85114065175036437568126625 63835548881277328176094969)
  ·
    refine ⟨47876661660957996132071227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63835548881277328176094969 47876661660957996132071227)
    ·
      refine ⟨71814992491436994198106841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47876661660957996132071227 71814992491436994198106841)
      ·
        refine ⟨53861244368577745648580131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71814992491436994198106841 53861244368577745648580131)
        ·
          refine ⟨80791866552866618472870197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53861244368577745648580131 80791866552866618472870197)
          ·
            refine ⟨7574237489331245481831581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80791866552866618472870197 7574237489331245481831581)
            ·
              refine ⟨2840339058499217055686843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7574237489331245481831581 2840339058499217055686843)
              ·
                refine ⟨4260508587748825583530265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840339058499217055686843 4260508587748825583530265)
                ·
                  refine ⟨3195381440811619187647699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4260508587748825583530265 3195381440811619187647699)
                  ·
                    refine ⟨4793072161217428781471549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195381440811619187647699 4793072161217428781471549)
                    ·
                      refine ⟨1797402060456535793051831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793072161217428781471549 1797402060456535793051831)
                      ·
                        rfl

theorem cell23_3500428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_3500428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500428 prefixEnd_3500428 := by exact prefixLift 3500428
  have htrace : WordTrace (prefixWord ++ tailWord_3500428) baseStart_3500428 baseEnd_3500428 := by
    simpa [prefixWord, tailWord_3500428, baseEnd_3500428] using wordTrace_append hprefix tailTrace_3500428
  have hstable : (prefixWord ++ tailWord_3500428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500428).length < 2 ^ (prefixWord ++ tailWord_3500428).sum := by decide
  have hdescent : baseEnd_3500428 < baseStart_3500428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500437 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3500437 : Nat := 118140960795 + 3500437 * 2 ^ 59
def prefixEnd_3500437 : Nat := 4983230072969 + 3 ^ 40 * 3500437 * 2
def baseEnd_3500437 : Nat := 1797406681782426257839289

theorem tailTrace_3500437 : CollatzResearch.WordTrace tailWord_3500437 prefixEnd_3500437 1797406681782426257839289 := by
  unfold tailWord_3500437
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671426019522050889267565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85114284013014700592845043 127671426019522050889267565)
  ·
    refine ⟨47876784757320769083475337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127671426019522050889267565 47876784757320769083475337)
    ·
      refine ⟨35907588567990576812606503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47876784757320769083475337 35907588567990576812606503)
      ·
        refine ⟨53861382851985865218909755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35907588567990576812606503 53861382851985865218909755)
        ·
          refine ⟨80792074277978797828364633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53861382851985865218909755 80792074277978797828364633)
          ·
            refine ⟨60594055708484098371273475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80792074277978797828364633 60594055708484098371273475)
            ·
              refine ⟨90891083562726147556910213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60594055708484098371273475 90891083562726147556910213)
              ·
                refine ⟨17042078168011152666920665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90891083562726147556910213 17042078168011152666920665)
                ·
                  refine ⟨12781558626008364500190499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17042078168011152666920665 12781558626008364500190499)
                  ·
                    refine ⟨19172337939012546750285749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12781558626008364500190499 19172337939012546750285749)
                    ·
                      refine ⟨1797406681782426257839289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19172337939012546750285749 1797406681782426257839289)
                      ·
                        rfl

theorem cell23_3500437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3500437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500437 prefixEnd_3500437 := by exact prefixLift 3500437
  have htrace : WordTrace (prefixWord ++ tailWord_3500437) baseStart_3500437 baseEnd_3500437 := by
    simpa [prefixWord, tailWord_3500437, baseEnd_3500437] using wordTrace_append hprefix tailTrace_3500437
  have hstable : (prefixWord ++ tailWord_3500437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500437).length < 2 ^ (prefixWord ++ tailWord_3500437).sum := by decide
  have hdescent : baseEnd_3500437 < baseStart_3500437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500451 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 4, 2, 2]
def baseStart_3500451 : Nat := 118140960795 + 3500451 * 2 ^ 59
def prefixEnd_3500451 : Nat := 4983230072969 + 3 ^ 40 * 3500451 * 2
def baseEnd_3500451 : Nat := 1797413870511589203064225

theorem tailTrace_3500451 : CollatzResearch.WordTrace tailWord_3500451 prefixEnd_3500451 1797413870511589203064225 := by
  unfold tailWord_3500451
  simp only [CollatzResearch.WordTrace]
  refine ⟨127671936641471331280277207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85114624427647554186851471 127671936641471331280277207)
  ·
    refine ⟨191507904962206996920415811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127671936641471331280277207 191507904962206996920415811)
    ·
      refine ⟨287261857443310495380623717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191507904962206996920415811 287261857443310495380623717)
      ·
        refine ⟨53861598270620717883866947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287261857443310495380623717 53861598270620717883866947)
        ·
          refine ⟨80792397405931076825800421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53861598270620717883866947 80792397405931076825800421)
          ·
            refine ⟨15148574513612076904837579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80792397405931076825800421 15148574513612076904837579)
            ·
              refine ⟨22722861770418115357256369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15148574513612076904837579 22722861770418115357256369)
              ·
                refine ⟨17042146327813586517942277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22722861770418115357256369 17042146327813586517942277)
                ·
                  refine ⟨3195402436465047472114177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17042146327813586517942277 3195402436465047472114177)
                  ·
                    refine ⟨2396551827348785604085633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3195402436465047472114177 2396551827348785604085633)
                    ·
                      refine ⟨1797413870511589203064225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396551827348785604085633 1797413870511589203064225)
                      ·
                        rfl

theorem cell23_3500451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_3500451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500451 prefixEnd_3500451 := by exact prefixLift 3500451
  have htrace : WordTrace (prefixWord ++ tailWord_3500451) baseStart_3500451 baseEnd_3500451 := by
    simpa [prefixWord, tailWord_3500451, baseEnd_3500451] using wordTrace_append hprefix tailTrace_3500451
  have hstable : (prefixWord ++ tailWord_3500451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500451).length < 2 ^ (prefixWord ++ tailWord_3500451).sum := by decide
  have hdescent : baseEnd_3500451 < baseStart_3500451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500474 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_3500474 : Nat := 118140960795 + 3500474 * 2 ^ 59
def prefixEnd_3500474 : Nat := 4983230072969 + 3 ^ 40 * 3500474 * 2
def baseEnd_3500474 : Nat := 199713964507404734786291

theorem tailTrace_3500474 : CollatzResearch.WordTrace tailWord_3500474 prefixEnd_3500474 199713964507404734786291 := by
  unfold tailWord_3500474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31918193880097001552091119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85115183680258670805576317 31918193880097001552091119)
  ·
    refine ⟨47877290820145502328136679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31918193880097001552091119 47877290820145502328136679)
    ·
      refine ⟨71815936230218253492205019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47877290820145502328136679 71815936230218253492205019)
      ·
        refine ⟨107723904345327380238307529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71815936230218253492205019 107723904345327380238307529)
        ·
          refine ⟨80792928258995535178730647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107723904345327380238307529 80792928258995535178730647)
          ·
            refine ⟨121189392388493302768095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80792928258995535178730647 121189392388493302768095971)
            ·
              refine ⟨181784088582739954152143957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121189392388493302768095971 181784088582739954152143957)
              ·
                refine ⟨2130282288078983837720437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 181784088582739954152143957 2130282288078983837720437)
                ·
                  refine ⟨199713964507404734786291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130282288078983837720437 199713964507404734786291)
                  ·
                    rfl

theorem cell23_3500474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_3500474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500474 prefixEnd_3500474 := by exact prefixLift 3500474
  have htrace : WordTrace (prefixWord ++ tailWord_3500474) baseStart_3500474 baseEnd_3500474 := by
    simpa [prefixWord, tailWord_3500474, baseEnd_3500474] using wordTrace_append hprefix tailTrace_3500474
  have hstable : (prefixWord ++ tailWord_3500474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500474).length < 2 ^ (prefixWord ++ tailWord_3500474).sum := by decide
  have hdescent : baseEnd_3500474 < baseStart_3500474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500524 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3500524 : Nat := 118140960795 + 3500524 * 2 ^ 59
def prefixEnd_3500524 : Nat := 4983230072969 + 3 ^ 40 * 3500524 * 2
def baseEnd_3500524 : Nat := 1797451354599367417451389

theorem tailTrace_3500524 : CollatzResearch.WordTrace tailWord_3500524 prefixEnd_3500524 1797451354599367417451389 := by
  unfold tailWord_3500524
  simp only [CollatzResearch.WordTrace]
  refine ⟨63837299585103432373842313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85116399446804576498456417 63837299585103432373842313)
  ·
    refine ⟨47877974688827574280381735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63837299585103432373842313 47877974688827574280381735)
    ·
      refine ⟨71816962033241361420572603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47877974688827574280381735 71816962033241361420572603)
      ·
        refine ⟨107725443049862042130858905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71816962033241361420572603 107725443049862042130858905)
        ·
          refine ⟨80794082287396531598144179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107725443049862042130858905 80794082287396531598144179)
          ·
            refine ⟨121191123431094797397216269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80794082287396531598144179 121191123431094797397216269)
            ·
              refine ⟨45446671286660549023956101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121191123431094797397216269 45446671286660549023956101)
              ·
                refine ⟨8521250866248852941991769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45446671286660549023956101 8521250866248852941991769)
                ·
                  refine ⟨6390938149686639706493827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521250866248852941991769 6390938149686639706493827)
                  ·
                    refine ⟨9586407224529959559740741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6390938149686639706493827 9586407224529959559740741)
                    ·
                      refine ⟨1797451354599367417451389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9586407224529959559740741 1797451354599367417451389)
                      ·
                        rfl

theorem cell23_3500524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3500524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500524 prefixEnd_3500524 := by exact prefixLift 3500524
  have htrace : WordTrace (prefixWord ++ tailWord_3500524) baseStart_3500524 baseEnd_3500524 := by
    simpa [prefixWord, tailWord_3500524, baseEnd_3500524] using wordTrace_append hprefix tailTrace_3500524
  have hstable : (prefixWord ++ tailWord_3500524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500524).length < 2 ^ (prefixWord ++ tailWord_3500524).sum := by decide
  have hdescent : baseEnd_3500524 < baseStart_3500524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500525 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3500525 : Nat := 118140960795 + 3500525 * 2 ^ 59
def prefixEnd_3500525 : Nat := 4983230072969 + 3 ^ 40 * 3500525 * 2
def baseEnd_3500525 : Nat := 199716874231113545948765

theorem tailTrace_3500525 : CollatzResearch.WordTrace tailWord_3500525 prefixEnd_3500525 199716874231113545948765 := by
  unfold tailWord_3500525
  simp only [CollatzResearch.WordTrace]
  refine ⟨127674635643203241918471029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85116423762135494612314019 127674635643203241918471029)
  ·
    refine ⟨11969497091550303929856659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127674635643203241918471029 11969497091550303929856659)
    ·
      refine ⟨17954245637325455894784989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969497091550303929856659 17954245637325455894784989)
      ·
        refine ⟨6732842113997045960544371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17954245637325455894784989 6732842113997045960544371)
        ·
          refine ⟨10099263170995568940816557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6732842113997045960544371 10099263170995568940816557)
          ·
            refine ⟨3787223689123338352806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10099263170995568940816557 3787223689123338352806209)
            ·
              refine ⟨2840417766842503764604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3787223689123338352806209 2840417766842503764604657)
              ·
                refine ⟨2130313325131877823453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840417766842503764604657 2130313325131877823453493)
                ·
                  refine ⟨199716874231113545948765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130313325131877823453493 199716874231113545948765)
                  ·
                    rfl

theorem cell23_3500525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3500525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500525 prefixEnd_3500525 := by exact prefixLift 3500525
  have htrace : WordTrace (prefixWord ++ tailWord_3500525) baseStart_3500525 baseEnd_3500525 := by
    simpa [prefixWord, tailWord_3500525, baseEnd_3500525] using wordTrace_append hprefix tailTrace_3500525
  have hstable : (prefixWord ++ tailWord_3500525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500525).length < 2 ^ (prefixWord ++ tailWord_3500525).sum := by decide
  have hdescent : baseEnd_3500525 < baseStart_3500525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500527 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_3500527 : Nat := 118140960795 + 3500527 * 2 ^ 59
def prefixEnd_3500527 : Nat := 4983230072969 + 3 ^ 40 * 3500527 * 2
def baseEnd_3500527 : Nat := 1797452895041330905713875

theorem tailTrace_3500527 : CollatzResearch.WordTrace tailWord_3500527 prefixEnd_3500527 1797452895041330905713875 := by
  unfold tailWord_3500527
  simp only [CollatzResearch.WordTrace]
  refine ⟨127674708589195996260043835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85116472392797330840029223 127674708589195996260043835)
  ·
    refine ⟨191512062883793994390065753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127674708589195996260043835 191512062883793994390065753)
    ·
      refine ⟨143634047162845495792549315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191512062883793994390065753 143634047162845495792549315)
      ·
        refine ⟨215451070744268243688823973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143634047162845495792549315 215451070744268243688823973)
        ·
          refine ⟨40397075764550295691654495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215451070744268243688823973 40397075764550295691654495)
          ·
            refine ⟨60595613646825443537481743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40397075764550295691654495 60595613646825443537481743)
            ·
              refine ⟨90893420470238165306222615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60595613646825443537481743 90893420470238165306222615)
              ·
                refine ⟨136340130705357247959333923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90893420470238165306222615 136340130705357247959333923)
                ·
                  refine ⟨204510196058035871939000885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136340130705357247959333923 204510196058035871939000885)
                  ·
                    refine ⟨19172830880440862994281333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204510196058035871939000885 19172830880440862994281333)
                    ·
                      refine ⟨1797452895041330905713875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19172830880440862994281333 1797452895041330905713875)
                      ·
                        rfl

theorem cell23_3500527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_3500527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500527 prefixEnd_3500527 := by exact prefixLift 3500527
  have htrace : WordTrace (prefixWord ++ tailWord_3500527) baseStart_3500527 baseEnd_3500527 := by
    simpa [prefixWord, tailWord_3500527, baseEnd_3500527] using wordTrace_append hprefix tailTrace_3500527
  have hstable : (prefixWord ++ tailWord_3500527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500527).length < 2 ^ (prefixWord ++ tailWord_3500527).sum := by decide
  have hdescent : baseEnd_3500527 < baseStart_3500527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500541 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_3500541 : Nat := 118140960795 + 3500541 * 2 ^ 59
def prefixEnd_3500541 : Nat := 4983230072969 + 3 ^ 40 * 3500541 * 2
def baseEnd_3500541 : Nat := 1797460083770493850938811

theorem tailTrace_3500541 : CollatzResearch.WordTrace tailWord_3500541 prefixEnd_3500541 1797460083770493850938811 := by
  unfold tailWord_3500541
  simp only [CollatzResearch.WordTrace]
  refine ⟨127675219211145276651053477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85116812807430184434035651 127675219211145276651053477)
  ·
    refine ⟨23939103602089739372072527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127675219211145276651053477 23939103602089739372072527)
    ·
      refine ⟨35908655403134609058108791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939103602089739372072527 35908655403134609058108791)
      ·
        refine ⟨53862983104701913587163187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35908655403134609058108791 53862983104701913587163187)
        ·
          refine ⟨80794474657052870380744781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53862983104701913587163187 80794474657052870380744781)
          ·
            refine ⟨30297927996394826392779293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80794474657052870380744781 30297927996394826392779293)
            ·
              refine ⟨11361722998648059897292235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30297927996394826392779293 11361722998648059897292235)
              ·
                refine ⟨17042584497972089845938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11361722998648059897292235 17042584497972089845938353)
                ·
                  refine ⟨12781938373479067384453765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17042584497972089845938353 12781938373479067384453765)
                  ·
                    refine ⟨2396613445027325134585081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12781938373479067384453765 2396613445027325134585081)
                    ·
                      refine ⟨1797460083770493850938811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396613445027325134585081 1797460083770493850938811)
                      ·
                        rfl

theorem cell23_3500541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_3500541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500541 prefixEnd_3500541 := by exact prefixLift 3500541
  have htrace : WordTrace (prefixWord ++ tailWord_3500541) baseStart_3500541 baseEnd_3500541 := by
    simpa [prefixWord, tailWord_3500541, baseEnd_3500541] using wordTrace_append hprefix tailTrace_3500541
  have hstable : (prefixWord ++ tailWord_3500541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500541).length < 2 ^ (prefixWord ++ tailWord_3500541).sum := by decide
  have hdescent : baseEnd_3500541 < baseStart_3500541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500558 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3500558 : Nat := 118140960795 + 3500558 * 2 ^ 59
def prefixEnd_3500558 : Nat := 4983230072969 + 3 ^ 40 * 3500558 * 2
def baseEnd_3500558 : Nat := 1797468812941620284426233

theorem tailTrace_3500558 : CollatzResearch.WordTrace tailWord_3500558 prefixEnd_3500558 1797468812941620284426233 := by
  unfold tailWord_3500558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959479906510461069302791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85117226168055792369614885 15959479906510461069302791)
  ·
    refine ⟨23939219859765691603954187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15959479906510461069302791 23939219859765691603954187)
    ·
      refine ⟨35908829789648537405931281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939219859765691603954187 35908829789648537405931281)
      ·
        refine ⟨26931622342236403054448461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35908829789648537405931281 26931622342236403054448461)
        ·
          refine ⟨10099358378338651145418173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26931622342236403054448461 10099358378338651145418173)
          ·
            refine ⟨3787259391876994179531815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10099358378338651145418173 3787259391876994179531815)
            ·
              refine ⟨5680889087815491269297723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787259391876994179531815 5680889087815491269297723)
              ·
                refine ⟨8521333631723236903946585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5680889087815491269297723 8521333631723236903946585)
                ·
                  refine ⟨6391000223792427677959939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521333631723236903946585 6391000223792427677959939)
                  ·
                    refine ⟨9586500335688641516939909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391000223792427677959939 9586500335688641516939909)
                    ·
                      refine ⟨1797468812941620284426233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9586500335688641516939909 1797468812941620284426233)
                      ·
                        rfl

theorem cell23_3500558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3500558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500558 prefixEnd_3500558 := by exact prefixLift 3500558
  have htrace : WordTrace (prefixWord ++ tailWord_3500558) baseStart_3500558 baseEnd_3500558 := by
    simpa [prefixWord, tailWord_3500558, baseEnd_3500558] using wordTrace_append hprefix tailTrace_3500558
  have hstable : (prefixWord ++ tailWord_3500558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500558).length < 2 ^ (prefixWord ++ tailWord_3500558).sum := by decide
  have hdescent : baseEnd_3500558 < baseStart_3500558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500568 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 1, 4]
def baseStart_3500568 : Nat := 118140960795 + 3500568 * 2 ^ 59
def prefixEnd_3500568 : Nat := 4983230072969 + 3 ^ 40 * 3500568 * 2
def baseEnd_3500568 : Nat := 599157982582721748433729

theorem tailTrace_3500568 : CollatzResearch.WordTrace tailWord_3500568 prefixEnd_3500568 599157982582721748433729 := by
  unfold tailWord_3500568
  simp only [CollatzResearch.WordTrace]
  refine ⟨63838101991023730131143179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85117469321364973508190905 63838101991023730131143179)
  ·
    refine ⟨95757152986535595196714769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63838101991023730131143179 95757152986535595196714769)
    ·
      refine ⟨71817864739901696397536077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95757152986535595196714769 71817864739901696397536077)
      ·
        refine ⟨26931699277463136149076029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71817864739901696397536077 26931699277463136149076029)
        ·
          refine ⟨10099387229048676055903511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26931699277463136149076029 10099387229048676055903511)
          ·
            refine ⟨15149080843573014083855267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10099387229048676055903511 15149080843573014083855267)
            ·
              refine ⟨22723621265359521125782901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15149080843573014083855267 22723621265359521125782901)
              ·
                refine ⟨2130339493627455105542147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22723621265359521125782901 2130339493627455105542147)
                ·
                  refine ⟨3195509240441182658313221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130339493627455105542147 3195509240441182658313221)
                  ·
                    refine ⟨599157982582721748433729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3195509240441182658313221 599157982582721748433729)
                    ·
                      rfl

theorem cell23_3500568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_3500568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500568 prefixEnd_3500568 := by exact prefixLift 3500568
  have htrace : WordTrace (prefixWord ++ tailWord_3500568) baseStart_3500568 baseEnd_3500568 := by
    simpa [prefixWord, tailWord_3500568, baseEnd_3500568] using wordTrace_append hprefix tailTrace_3500568
  have hstable : (prefixWord ++ tailWord_3500568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500568).length < 2 ^ (prefixWord ++ tailWord_3500568).sum := by decide
  have hdescent : baseEnd_3500568 < baseStart_3500568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
