import V185TrunkScan21Chunk045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_556826 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_556826 : Nat := 118140960795 + 556826 * 2 ^ 59
def prefixEnd_556826 : Nat := 4983230072969 + 3 ^ 40 * 556826 * 2
def baseEnd_556826 : Nat := 127075279520241621961871

theorem tailTrace_556826 : CollatzResearch.WordTrace tailWord_556826 prefixEnd_556826 127075279520241621961871 := by
  unfold tailWord_556826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077278170180493788686583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13539408453814650103164221 5077278170180493788686583)
  ·
    refine ⟨7615917255270740683029875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5077278170180493788686583 7615917255270740683029875)
    ·
      refine ⟨11423875882906111024544813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7615917255270740683029875 11423875882906111024544813)
      ·
        refine ⟨4283953456089791634204305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11423875882906111024544813 4283953456089791634204305)
        ·
          refine ⟨3212965092067343725653229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4283953456089791634204305 3212965092067343725653229)
          ·
            refine ⟨1204861909525253897119961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3212965092067343725653229 1204861909525253897119961)
            ·
              refine ⟨903646432143940422839971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204861909525253897119961 903646432143940422839971)
              ·
                refine ⟨1355469648215910634259957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903646432143940422839971 1355469648215910634259957)
                ·
                  refine ⟨127075279520241621961871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355469648215910634259957 127075279520241621961871)
                  ·
                    rfl

theorem cell21_556826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_556826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556826 prefixEnd_556826 := by exact prefixLift 556826
  have htrace : WordTrace (prefixWord ++ tailWord_556826) baseStart_556826 baseEnd_556826 := by
    simpa [prefixWord, tailWord_556826, baseEnd_556826] using wordTrace_append hprefix tailTrace_556826
  have hstable : (prefixWord ++ tailWord_556826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556826).length < 2 ^ (prefixWord ++ tailWord_556826).sum := by decide
  have hdescent : baseEnd_556826 < baseStart_556826 := by decide
  rcases family_descends (prefixWord ++ tailWord_556826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556846 : List Nat := [4, 1, 3, 2, 3, 1, 2, 5]
def baseStart_556846 : Nat := 118140960795 + 556846 * 2 ^ 59
def prefixEnd_556846 : Nat := 4983230072969 + 3 ^ 40 * 556846 * 2
def baseEnd_556846 : Nat := 42359947930908677209499

theorem tailTrace_556846 : CollatzResearch.WordTrace tailWord_556846 prefixEnd_556846 42359947930908677209499 := by
  unfold tailWord_556846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538730267581189821309299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13539894760433012380316261 2538730267581189821309299)
  ·
    refine ⟨3808095401371784731963949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2538730267581189821309299 3808095401371784731963949)
    ·
      refine ⟨1428035775514419274486481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3808095401371784731963949 1428035775514419274486481)
      ·
        refine ⟨1071026831635814455864861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428035775514419274486481 1071026831635814455864861)
        ·
          refine ⟨401635061863430420949323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1071026831635814455864861 401635061863430420949323)
          ·
            refine ⟨602452592795145631423985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401635061863430420949323 602452592795145631423985)
            ·
              refine ⟨451839444596359223567989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602452592795145631423985 451839444596359223567989)
              ·
                refine ⟨42359947930908677209499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451839444596359223567989 42359947930908677209499)
                ·
                  rfl

theorem cell21_556846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_556846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556846 prefixEnd_556846 := by exact prefixLift 556846
  have htrace : WordTrace (prefixWord ++ tailWord_556846) baseStart_556846 baseEnd_556846 := by
    simpa [prefixWord, tailWord_556846, baseEnd_556846] using wordTrace_append hprefix tailTrace_556846
  have hstable : (prefixWord ++ tailWord_556846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556846).length < 2 ^ (prefixWord ++ tailWord_556846).sum := by decide
  have hdescent : baseEnd_556846 < baseStart_556846 := by decide
  rcases family_descends (prefixWord ++ tailWord_556846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556877 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 3]
def baseStart_556877 : Nat := 118140960795 + 556877 * 2 ^ 59
def prefixEnd_556877 : Nat := 4983230072969 + 3 ^ 40 * 556877 * 2
def baseEnd_556877 : Nat := 127086918415076866611767

theorem tailTrace_556877 : CollatzResearch.WordTrace tailWord_556877 prefixEnd_556877 127086918415076866611767 := by
  unfold tailWord_556877
  simp only [CollatzResearch.WordTrace]
  refine ⟨20310972803537210864852885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13540648535691473909901923 20310972803537210864852885)
  ·
    refine ⟨952076850165806759289979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20310972803537210864852885 952076850165806759289979)
    ·
      refine ⟨1428115275248710138934969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952076850165806759289979 1428115275248710138934969)
      ·
        refine ⟨1071086456436532604201227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428115275248710138934969 1071086456436532604201227)
        ·
          refine ⟨1606629684654798906301841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071086456436532604201227 1606629684654798906301841)
          ·
            refine ⟨1204972263491099179726381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1606629684654798906301841 1204972263491099179726381)
            ·
              refine ⟨451864598809162192397393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1204972263491099179726381 451864598809162192397393)
              ·
                refine ⟨338898449106871644298045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451864598809162192397393 338898449106871644298045)
                ·
                  refine ⟨127086918415076866611767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338898449106871644298045 127086918415076866611767)
                  ·
                    rfl

theorem cell21_556877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_556877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556877 prefixEnd_556877 := by exact prefixLift 556877
  have htrace : WordTrace (prefixWord ++ tailWord_556877) baseStart_556877 baseEnd_556877 := by
    simpa [prefixWord, tailWord_556877, baseEnd_556877] using wordTrace_append hprefix tailTrace_556877
  have hstable : (prefixWord ++ tailWord_556877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556877).length < 2 ^ (prefixWord ++ tailWord_556877).sum := by decide
  have hdescent : baseEnd_556877 < baseStart_556877 := by decide
  rcases family_descends (prefixWord ++ tailWord_556877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556975 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_556975 : Nat := 118140960795 + 556975 * 2 ^ 59
def prefixEnd_556975 : Nat := 4983230072969 + 3 ^ 40 * 556975 * 2
def baseEnd_556975 : Nat := 127109283350250473978233

theorem tailTrace_556975 : CollatzResearch.WordTrace tailWord_556975 prefixEnd_556975 127109283350250473978233 := by
  unfold tailWord_556975
  simp only [CollatzResearch.WordTrace]
  refine ⟨20314547157182173601920379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13543031438121449067946919 20314547157182173601920379)
  ·
    refine ⟨30471820735773260402880569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20314547157182173601920379 30471820735773260402880569)
    ·
      refine ⟨22853865551829945302160427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30471820735773260402880569 22853865551829945302160427)
      ·
        refine ⟨34280798327744917953240641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22853865551829945302160427 34280798327744917953240641)
        ·
          refine ⟨25710598745808688464930481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34280798327744917953240641 25710598745808688464930481)
          ·
            refine ⟨19282949059356516348697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25710598745808688464930481 19282949059356516348697861)
            ·
              refine ⟨3615552948629346815380849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19282949059356516348697861 3615552948629346815380849)
              ·
                refine ⟨2711664711472010111535637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3615552948629346815380849 2711664711472010111535637)
                ·
                  refine ⟨127109283350250473978233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2711664711472010111535637 127109283350250473978233)
                  ·
                    rfl

theorem cell21_556975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_556975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556975 prefixEnd_556975 := by exact prefixLift 556975
  have htrace : WordTrace (prefixWord ++ tailWord_556975) baseStart_556975 baseEnd_556975 := by
    simpa [prefixWord, tailWord_556975, baseEnd_556975] using wordTrace_append hprefix tailTrace_556975
  have hstable : (prefixWord ++ tailWord_556975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556975).length < 2 ^ (prefixWord ++ tailWord_556975).sum := by decide
  have hdescent : baseEnd_556975 < baseStart_556975 := by decide
  rcases family_descends (prefixWord ++ tailWord_556975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557006 : List Nat := [4, 1, 1, 1, 2, 2, 2, 8]
def baseStart_557006 : Nat := 118140960795 + 557006 * 2 ^ 59
def prefixEnd_557006 : Nat := 4983230072969 + 3 ^ 40 * 557006 * 2
def baseEnd_557006 : Nat := 42372119324200436320501

theorem tailTrace_557006 : CollatzResearch.WordTrace tailWord_557006 prefixEnd_557006 42372119324200436320501 := by
  unfold tailWord_557006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539459727508733237037359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13543785213379910597532581 2539459727508733237037359)
  ·
    refine ⟨3809189591263099855556039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2539459727508733237037359 3809189591263099855556039)
    ·
      refine ⟨5713784386894649783334059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3809189591263099855556039 5713784386894649783334059)
      ·
        refine ⟨8570676580341974675001089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713784386894649783334059 8570676580341974675001089)
        ·
          refine ⟨6428007435256481006250817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8570676580341974675001089 6428007435256481006250817)
          ·
            refine ⟨4821005576442360754688113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6428007435256481006250817 4821005576442360754688113)
            ·
              refine ⟨3615754182331770566016085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821005576442360754688113 3615754182331770566016085)
              ·
                refine ⟨42372119324200436320501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3615754182331770566016085 42372119324200436320501)
                ·
                  rfl

theorem cell21_557006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_557006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557006 prefixEnd_557006 := by exact prefixLift 557006
  have htrace : WordTrace (prefixWord ++ tailWord_557006) baseStart_557006 baseEnd_557006 := by
    simpa [prefixWord, tailWord_557006, baseEnd_557006] using wordTrace_append hprefix tailTrace_557006
  have hstable : (prefixWord ++ tailWord_557006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557006).length < 2 ^ (prefixWord ++ tailWord_557006).sum := by decide
  have hdescent : baseEnd_557006 < baseStart_557006 := by decide
  rcases family_descends (prefixWord ++ tailWord_557006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557023 : List Nat := [1, 1, 2, 3, 4, 1, 4, 5]
def baseStart_557023 : Nat := 118140960795 + 557023 * 2 ^ 59
def prefixEnd_557023 : Nat := 4983230072969 + 3 ^ 40 * 557023 * 2
def baseEnd_557023 : Nat := 42373412534737685726045

theorem tailTrace_557023 : CollatzResearch.WordTrace tailWord_557023 prefixEnd_557023 42373412534737685726045 := by
  unfold tailWord_557023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20316297861008277799667723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13544198574005518533111815 20316297861008277799667723)
  ·
    refine ⟨30474446791512416699501585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20316297861008277799667723 30474446791512416699501585)
    ·
      refine ⟨22855835093634312524626189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30474446791512416699501585 22855835093634312524626189)
      ·
        refine ⟨8570938160112867196734821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22855835093634312524626189 8570938160112867196734821)
        ·
          refine ⟨1607050905021162599387779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8570938160112867196734821 1607050905021162599387779)
          ·
            refine ⟨2410576357531743899081669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607050905021162599387779 2410576357531743899081669)
            ·
              refine ⟨451983067037201981077813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2410576357531743899081669 451983067037201981077813)
              ·
                refine ⟨42373412534737685726045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451983067037201981077813 42373412534737685726045)
                ·
                  rfl

theorem cell21_557023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 5].length) (baseStart_557023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557023 prefixEnd_557023 := by exact prefixLift 557023
  have htrace : WordTrace (prefixWord ++ tailWord_557023) baseStart_557023 baseEnd_557023 := by
    simpa [prefixWord, tailWord_557023, baseEnd_557023] using wordTrace_append hprefix tailTrace_557023
  have hstable : (prefixWord ++ tailWord_557023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557023).length < 2 ^ (prefixWord ++ tailWord_557023).sum := by decide
  have hdescent : baseEnd_557023 < baseStart_557023 := by decide
  rcases family_descends (prefixWord ++ tailWord_557023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557051 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_557051 : Nat := 118140960795 + 557051 * 2 ^ 59
def prefixEnd_557051 : Nat := 4983230072969 + 3 ^ 40 * 557051 * 2
def baseEnd_557051 : Nat := 127126627585691230711411

theorem tailTrace_557051 : CollatzResearch.WordTrace tailWord_557051 prefixEnd_557051 127126627585691230711411 := by
  unfold tailWord_557051
  simp only [CollatzResearch.WordTrace]
  refine ⟨20317319104906838581687007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13544879403271225721124671 20317319104906838581687007)
  ·
    refine ⟨30475978657360257872530511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20317319104906838581687007 30475978657360257872530511)
    ·
      refine ⟨45713967986040386808795767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30475978657360257872530511 45713967986040386808795767)
      ·
        refine ⟨68570951979060580213193651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45713967986040386808795767 68570951979060580213193651)
        ·
          refine ⟨102856427968590870319790477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68570951979060580213193651 102856427968590870319790477)
          ·
            refine ⟨38571160488221576369921429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102856427968590870319790477 38571160488221576369921429)
            ·
              refine ⟨1808023147885386392340067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38571160488221576369921429 1808023147885386392340067)
              ·
                refine ⟨2712034721828079588510101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808023147885386392340067 2712034721828079588510101)
                ·
                  refine ⟨127126627585691230711411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2712034721828079588510101 127126627585691230711411)
                  ·
                    rfl

theorem cell21_557051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_557051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557051 prefixEnd_557051 := by exact prefixLift 557051
  have htrace : WordTrace (prefixWord ++ tailWord_557051) baseStart_557051 baseEnd_557051 := by
    simpa [prefixWord, tailWord_557051, baseEnd_557051] using wordTrace_append hprefix tailTrace_557051
  have hstable : (prefixWord ++ tailWord_557051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557051).length < 2 ^ (prefixWord ++ tailWord_557051).sum := by decide
  have hdescent : baseEnd_557051 < baseStart_557051 := by decide
  rcases family_descends (prefixWord ++ tailWord_557051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557060 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_557060 : Nat := 118140960795 + 557060 * 2 ^ 59
def prefixEnd_557060 : Nat := 4983230072969 + 3 ^ 40 * 557060 * 2
def baseEnd_557060 : Nat := 127128681508309215061393

theorem tailTrace_557060 : CollatzResearch.WordTrace tailWord_557060 prefixEnd_557060 127128681508309215061393 := by
  unfold tailWord_557060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158823680937116559382317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13545098241249488745843089 10158823680937116559382317)
  ·
    refine ⟨3809558880351418709768369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10158823680937116559382317 3809558880351418709768369)
    ·
      refine ⟨2857169160263564032326277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3809558880351418709768369 2857169160263564032326277)
      ·
        refine ⟨535719217549418256061177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2857169160263564032326277 535719217549418256061177)
        ·
          refine ⟨401789413162063692045883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535719217549418256061177 401789413162063692045883)
          ·
            refine ⟨602684119743095538068825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401789413162063692045883 602684119743095538068825)
            ·
              refine ⟨452013089807321653551619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602684119743095538068825 452013089807321653551619)
              ·
                refine ⟨678019634710982480327429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452013089807321653551619 678019634710982480327429)
                ·
                  refine ⟨127128681508309215061393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678019634710982480327429 127128681508309215061393)
                  ·
                    rfl

theorem cell21_557060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_557060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557060 prefixEnd_557060 := by exact prefixLift 557060
  have htrace : WordTrace (prefixWord ++ tailWord_557060) baseStart_557060 baseEnd_557060 := by
    simpa [prefixWord, tailWord_557060, baseEnd_557060] using wordTrace_append hprefix tailTrace_557060
  have hstable : (prefixWord ++ tailWord_557060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557060).length < 2 ^ (prefixWord ++ tailWord_557060).sum := by decide
  have hdescent : baseEnd_557060 < baseStart_557060 := by decide
  rcases family_descends (prefixWord ++ tailWord_557060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557068 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_557068 : Nat := 118140960795 + 557068 * 2 ^ 59
def prefixEnd_557068 : Nat := 4983230072969 + 3 ^ 40 * 557068 * 2
def baseEnd_557068 : Nat := 127130507217302978928043

theorem tailTrace_557068 : CollatzResearch.WordTrace tailWord_557068 prefixEnd_557068 127130507217302978928043 := by
  unfold tailWord_557068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158969572922625242527929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13545292763896833656703905 10158969572922625242527929)
  ·
    refine ⟨7619227179691968931895947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10158969572922625242527929 7619227179691968931895947)
    ·
      refine ⟨11428840769537953397843921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7619227179691968931895947 11428840769537953397843921)
      ·
        refine ⟨8571630577153465048382941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11428840769537953397843921 8571630577153465048382941)
        ·
          refine ⟨3214361466432549393143603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8571630577153465048382941 3214361466432549393143603)
          ·
            refine ⟨4821542199648824089715405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214361466432549393143603 4821542199648824089715405)
            ·
              refine ⟨1808078324868309033643277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4821542199648824089715405 1808078324868309033643277)
              ·
                refine ⟨678029371825615887616229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808078324868309033643277 678029371825615887616229)
                ·
                  refine ⟨127130507217302978928043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678029371825615887616229 127130507217302978928043)
                  ·
                    rfl

theorem cell21_557068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_557068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557068 prefixEnd_557068 := by exact prefixLift 557068
  have htrace : WordTrace (prefixWord ++ tailWord_557068) baseStart_557068 baseEnd_557068 := by
    simpa [prefixWord, tailWord_557068, baseEnd_557068] using wordTrace_append hprefix tailTrace_557068
  have hstable : (prefixWord ++ tailWord_557068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557068).length < 2 ^ (prefixWord ++ tailWord_557068).sum := by decide
  have hdescent : baseEnd_557068 < baseStart_557068 := by decide
  rcases family_descends (prefixWord ++ tailWord_557068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557082 : List Nat := [3, 1, 1, 3, 1, 3, 2, 7]
def baseStart_557082 : Nat := 118140960795 + 557082 * 2 ^ 59
def prefixEnd_557082 : Nat := 4983230072969 + 3 ^ 40 * 557082 * 2
def baseEnd_557082 : Nat := 42377900736014021898227

theorem tailTrace_557082 : CollatzResearch.WordTrace tailWord_557082 prefixEnd_557082 42377900736014021898227 := by
  unfold tailWord_557082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079612441948632719016375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13545633178529687250710333 5079612441948632719016375)
  ·
    refine ⟨7619418662922949078524563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5079612441948632719016375 7619418662922949078524563)
    ·
      refine ⟨11429127994384423617786845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7619418662922949078524563 11429127994384423617786845)
      ·
        refine ⟨4285922997894158856670067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11429127994384423617786845 4285922997894158856670067)
        ·
          refine ⟨6428884496841238285005101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285922997894158856670067 6428884496841238285005101)
          ·
            refine ⟨2410831686315464356876913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6428884496841238285005101 2410831686315464356876913)
            ·
              refine ⟨1808123764736598267657685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2410831686315464356876913 1808123764736598267657685)
              ·
                refine ⟨42377900736014021898227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1808123764736598267657685 42377900736014021898227)
                ·
                  rfl

theorem cell21_557082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_557082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557082 prefixEnd_557082 := by exact prefixLift 557082
  have htrace : WordTrace (prefixWord ++ tailWord_557082) baseStart_557082 baseEnd_557082 := by
    simpa [prefixWord, tailWord_557082, baseEnd_557082] using wordTrace_append hprefix tailTrace_557082
  have hstable : (prefixWord ++ tailWord_557082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557082).length < 2 ^ (prefixWord ++ tailWord_557082).sum := by decide
  have hdescent : baseEnd_557082 < baseStart_557082 := by decide
  rcases family_descends (prefixWord ++ tailWord_557082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557189 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_557189 : Nat := 118140960795 + 557189 * 2 ^ 59
def prefixEnd_557189 : Nat := 4983230072969 + 3 ^ 40 * 557189 * 2
def baseEnd_557189 : Nat := 127158121065833657411129

theorem tailTrace_557189 : CollatzResearch.WordTrace tailWord_557189 prefixEnd_557189 127158121065833657411129 := by
  unfold tailWord_557189
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322352378406888150210621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13548234918937925433473747 20322352378406888150210621)
  ·
    refine ⟨7620882141902583056328983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20322352378406888150210621 7620882141902583056328983)
    ·
      refine ⟨11431323212853874584493475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7620882141902583056328983 11431323212853874584493475)
      ·
        refine ⟨17146984819280811876740213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11431323212853874584493475 17146984819280811876740213)
        ·
          refine ⟨1607529826807576113444395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17146984819280811876740213 1607529826807576113444395)
          ·
            refine ⟨2411294740211364170166593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607529826807576113444395 2411294740211364170166593)
            ·
              refine ⟨1808471055158523127624945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2411294740211364170166593 1808471055158523127624945)
              ·
                refine ⟨1356353291368892345718709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808471055158523127624945 1356353291368892345718709)
                ·
                  refine ⟨127158121065833657411129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356353291368892345718709 127158121065833657411129)
                  ·
                    rfl

theorem cell21_557189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_557189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557189 prefixEnd_557189 := by exact prefixLift 557189
  have htrace : WordTrace (prefixWord ++ tailWord_557189) baseStart_557189 baseEnd_557189 := by
    simpa [prefixWord, tailWord_557189, baseEnd_557189] using wordTrace_append hprefix tailTrace_557189
  have hstable : (prefixWord ++ tailWord_557189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557189).length < 2 ^ (prefixWord ++ tailWord_557189).sum := by decide
  have hdescent : baseEnd_557189 < baseStart_557189 := by decide
  rcases family_descends (prefixWord ++ tailWord_557189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557192 : List Nat := [2, 1, 3, 4, 1, 3, 2, 5]
def baseStart_557192 : Nat := 118140960795 + 557192 * 2 ^ 59
def prefixEnd_557192 : Nat := 4983230072969 + 3 ^ 40 * 557192 * 2
def baseEnd_557192 : Nat := 42386268568902106287041

theorem tailTrace_557192 : CollatzResearch.WordTrace tailWord_557192 prefixEnd_557192 42386268568902106287041 := by
  unfold tailWord_557192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10161230898698009831284915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13548307864930679775046553 10161230898698009831284915)
  ·
    refine ⟨15241846348047014746927373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10161230898698009831284915 15241846348047014746927373)
    ·
      refine ⟨5715692380517630530097765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15241846348047014746927373 5715692380517630530097765)
      ·
        refine ⟨1071692321347055724393331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5715692380517630530097765 1071692321347055724393331)
        ·
          refine ⟨1607538482020583586589997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071692321347055724393331 1607538482020583586589997)
          ·
            refine ⟨602826930757718844971249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1607538482020583586589997 602826930757718844971249)
            ·
              refine ⟨452120198068289133728437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602826930757718844971249 452120198068289133728437)
              ·
                refine ⟨42386268568902106287041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452120198068289133728437 42386268568902106287041)
                ·
                  rfl

theorem cell21_557192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_557192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557192 prefixEnd_557192 := by exact prefixLift 557192
  have htrace : WordTrace (prefixWord ++ tailWord_557192) baseStart_557192 baseEnd_557192 := by
    simpa [prefixWord, tailWord_557192, baseEnd_557192] using wordTrace_append hprefix tailTrace_557192
  have hstable : (prefixWord ++ tailWord_557192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557192).length < 2 ^ (prefixWord ++ tailWord_557192).sum := by decide
  have hdescent : baseEnd_557192 < baseStart_557192 := by decide
  rcases family_descends (prefixWord ++ tailWord_557192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557223 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_557223 : Nat := 118140960795 + 557223 * 2 ^ 59
def prefixEnd_557223 : Nat := 4983230072969 + 3 ^ 40 * 557223 * 2
def baseEnd_557223 : Nat := 127165880329057153844393

theorem tailTrace_557223 : CollatzResearch.WordTrace tailWord_557223 prefixEnd_557223 127165880329057153844393 := by
  unfold tailWord_557223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323592460283711956948323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13549061640189141304632215 20323592460283711956948323)
  ·
    refine ⟨30485388690425567935422485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20323592460283711956948323 30485388690425567935422485)
    ·
      refine ⟨1429002594863698496972929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30485388690425567935422485 1429002594863698496972929)
      ·
        refine ⟨1071751946147773872729697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429002594863698496972929 1071751946147773872729697)
        ·
          refine ⟨803813959610830404547273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1071751946147773872729697 803813959610830404547273)
          ·
            refine ⟨602860469708122803410455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803813959610830404547273 602860469708122803410455)
            ·
              refine ⟨904290704562184205115683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602860469708122803410455 904290704562184205115683)
              ·
                refine ⟨1356436056843276307673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904290704562184205115683 1356436056843276307673525)
                ·
                  refine ⟨127165880329057153844393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356436056843276307673525 127165880329057153844393)
                  ·
                    rfl

theorem cell21_557223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_557223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557223 prefixEnd_557223 := by exact prefixLift 557223
  have htrace : WordTrace (prefixWord ++ tailWord_557223) baseStart_557223 baseEnd_557223 := by
    simpa [prefixWord, tailWord_557223, baseEnd_557223] using wordTrace_append hprefix tailTrace_557223
  have hstable : (prefixWord ++ tailWord_557223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557223).length < 2 ^ (prefixWord ++ tailWord_557223).sum := by decide
  have hdescent : baseEnd_557223 < baseStart_557223 := by decide
  rcases family_descends (prefixWord ++ tailWord_557223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557234 : List Nat := [3, 2, 1, 1, 1, 3, 4, 6]
def baseStart_557234 : Nat := 118140960795 + 557234 * 2 ^ 59
def prefixEnd_557234 : Nat := 4983230072969 + 3 ^ 40 * 557234 * 2
def baseEnd_557234 : Nat := 42389463559641193053679

theorem tailTrace_557234 : CollatzResearch.WordTrace tailWord_557234 prefixEnd_557234 42389463559641193053679 := by
  unfold tailWord_557234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080998415810965208899689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13549329108829240557065837 5080998415810965208899689)
  ·
    refine ⟨3810748811858223906674767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5080998415810965208899689 3810748811858223906674767)
    ·
      refine ⟨5716123217787335860012151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3810748811858223906674767 5716123217787335860012151)
      ·
        refine ⟨8574184826681003790018227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5716123217787335860012151 8574184826681003790018227)
        ·
          refine ⟨12861277240021505685027341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8574184826681003790018227 12861277240021505685027341)
          ·
            refine ⟨4822978965008064631885253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12861277240021505685027341 4822978965008064631885253)
            ·
              refine ⟨904308555939012118478485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4822978965008064631885253 904308555939012118478485)
              ·
                refine ⟨42389463559641193053679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 904308555939012118478485 42389463559641193053679)
                ·
                  rfl

theorem cell21_557234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_557234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557234 prefixEnd_557234 := by exact prefixLift 557234
  have htrace : WordTrace (prefixWord ++ tailWord_557234) baseStart_557234 baseEnd_557234 := by
    simpa [prefixWord, tailWord_557234, baseEnd_557234] using wordTrace_append hprefix tailTrace_557234
  have hstable : (prefixWord ++ tailWord_557234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557234).length < 2 ^ (prefixWord ++ tailWord_557234).sum := by decide
  have hdescent : baseEnd_557234 < baseStart_557234 := by decide
  rcases family_descends (prefixWord ++ tailWord_557234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557324 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_557324 : Nat := 118140960795 + 557324 * 2 ^ 59
def prefixEnd_557324 : Nat := 4983230072969 + 3 ^ 40 * 557324 * 2
def baseEnd_557324 : Nat := 127188929905103422660853

theorem tailTrace_557324 : CollatzResearch.WordTrace tailWord_557324 prefixEnd_557324 127188929905103422660853 := by
  unfold tailWord_557324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163638116458903103187513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13551517488611870804250017 10163638116458903103187513)
  ·
    refine ⟨7622728587344177327390635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10163638116458903103187513 7622728587344177327390635)
    ·
      refine ⟨11434092881016265991085953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7622728587344177327390635 11434092881016265991085953)
      ·
        refine ⟨8575569660762199493314465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11434092881016265991085953 8575569660762199493314465)
        ·
          refine ⟨6431677245571649619985849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8575569660762199493314465 6431677245571649619985849)
          ·
            refine ⟨4823757934178737214989387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6431677245571649619985849 4823757934178737214989387)
            ·
              refine ⟨7235636901268105822484081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823757934178737214989387 7235636901268105822484081)
              ·
                refine ⟨5426727675951079366863061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7235636901268105822484081 5426727675951079366863061)
                ·
                  refine ⟨127188929905103422660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5426727675951079366863061 127188929905103422660853)
                  ·
                    rfl

theorem cell21_557324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_557324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557324 prefixEnd_557324 := by exact prefixLift 557324
  have htrace : WordTrace (prefixWord ++ tailWord_557324) baseStart_557324 baseEnd_557324 := by
    simpa [prefixWord, tailWord_557324, baseEnd_557324] using wordTrace_append hprefix tailTrace_557324
  have hstable : (prefixWord ++ tailWord_557324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557324).length < 2 ^ (prefixWord ++ tailWord_557324).sum := by decide
  have hdescent : baseEnd_557324 < baseStart_557324 := by decide
  rcases family_descends (prefixWord ++ tailWord_557324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557400 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_557400 : Nat := 118140960795 + 557400 * 2 ^ 59
def prefixEnd_557400 : Nat := 4983230072969 + 3 ^ 40 * 557400 * 2
def baseEnd_557400 : Nat := 127206274140544179394031

theorem tailTrace_557400 : CollatzResearch.WordTrace tailWord_557400 prefixEnd_557400 127206274140544179394031 := by
  unfold tailWord_557400
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165024090321235593070827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13553365453761647457427769 10165024090321235593070827)
  ·
    refine ⟨15247536135481853389606241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165024090321235593070827 15247536135481853389606241)
    ·
      refine ⟨11435652101611390042204681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15247536135481853389606241 11435652101611390042204681)
      ·
        refine ⟨8576739076208542531653511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11435652101611390042204681 8576739076208542531653511)
        ·
          refine ⟨12865108614312813797480267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576739076208542531653511 12865108614312813797480267)
          ·
            refine ⟨19297662921469220696220401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12865108614312813797480267 19297662921469220696220401)
            ·
              refine ⟨14473247191101915522165301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19297662921469220696220401 14473247191101915522165301)
              ·
                refine ⟨1356866924165804580202997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14473247191101915522165301 1356866924165804580202997)
                ·
                  refine ⟨127206274140544179394031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356866924165804580202997 127206274140544179394031)
                  ·
                    rfl

theorem cell21_557400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_557400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557400 prefixEnd_557400 := by exact prefixLift 557400
  have htrace : WordTrace (prefixWord ++ tailWord_557400) baseStart_557400 baseEnd_557400 := by
    simpa [prefixWord, tailWord_557400, baseEnd_557400] using wordTrace_append hprefix tailTrace_557400
  have hstable : (prefixWord ++ tailWord_557400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557400).length < 2 ^ (prefixWord ++ tailWord_557400).sum := by decide
  have hdescent : baseEnd_557400 < baseStart_557400 := by decide
  rcases family_descends (prefixWord ++ tailWord_557400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557448 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_557448 : Nat := 118140960795 + 557448 * 2 ^ 59
def prefixEnd_557448 : Nat := 4983230072969 + 3 ^ 40 * 557448 * 2
def baseEnd_557448 : Nat := 127217228394506762593933

theorem tailTrace_557448 : CollatzResearch.WordTrace tailWord_557448 prefixEnd_557448 127217228394506762593933 := by
  unfold tailWord_557448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165899442234287691944499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13554532589645716922592665 10165899442234287691944499)
  ·
    refine ⟨15248849163351431537916749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10165899442234287691944499 15248849163351431537916749)
    ·
      refine ⟨5718318436256786826718781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15248849163351431537916749 5718318436256786826718781)
      ·
        refine ⟨2144369413596295060019543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5718318436256786826718781 2144369413596295060019543)
        ·
          refine ⟨3216554120394442590029315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144369413596295060019543 3216554120394442590029315)
          ·
            refine ⟨4824831180591663885043973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216554120394442590029315 4824831180591663885043973)
            ·
              refine ⟨904655846360936978445745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4824831180591663885043973 904655846360936978445745)
              ·
                refine ⟨678491884770702733834309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904655846360936978445745 678491884770702733834309)
                ·
                  refine ⟨127217228394506762593933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678491884770702733834309 127217228394506762593933)
                  ·
                    rfl

theorem cell21_557448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_557448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557448 prefixEnd_557448 := by exact prefixLift 557448
  have htrace : WordTrace (prefixWord ++ tailWord_557448) baseStart_557448 baseEnd_557448 := by
    simpa [prefixWord, tailWord_557448, baseEnd_557448] using wordTrace_append hprefix tailTrace_557448
  have hstable : (prefixWord ++ tailWord_557448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557448).length < 2 ^ (prefixWord ++ tailWord_557448).sum := by decide
  have hdescent : baseEnd_557448 < baseStart_557448 := by decide
  rcases family_descends (prefixWord ++ tailWord_557448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557451 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 3]
def baseStart_557451 : Nat := 118140960795 + 557451 * 2 ^ 59
def prefixEnd_557451 : Nat := 4983230072969 + 3 ^ 40 * 557451 * 2
def baseEnd_557451 : Nat := 127217913035379424043927

theorem tailTrace_557451 : CollatzResearch.WordTrace tailWord_557451 prefixEnd_557451 127217913035379424043927 := by
  unfold tailWord_557451
  simp only [CollatzResearch.WordTrace]
  refine ⟨20331908303457706896248207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13554605535638471264165471 20331908303457706896248207)
  ·
    refine ⟨30497862455186560344372311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20331908303457706896248207 30497862455186560344372311)
    ·
      refine ⟨45746793682779840516558467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30497862455186560344372311 45746793682779840516558467)
      ·
        refine ⟨68620190524169760774837701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45746793682779840516558467 68620190524169760774837701)
        ·
          refine ⟨12866285723281830145282069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68620190524169760774837701 12866285723281830145282069)
          ·
            refine ⟨603107143278835788060097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12866285723281830145282069 603107143278835788060097)
            ·
              refine ⟨452330357459126841045073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603107143278835788060097 452330357459126841045073)
              ·
                refine ⟨339247768094345130783805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452330357459126841045073 339247768094345130783805)
                ·
                  refine ⟨127217913035379424043927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339247768094345130783805 127217913035379424043927)
                  ·
                    rfl

theorem cell21_557451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].length) (baseStart_557451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557451 prefixEnd_557451 := by exact prefixLift 557451
  have htrace : WordTrace (prefixWord ++ tailWord_557451) baseStart_557451 baseEnd_557451 := by
    simpa [prefixWord, tailWord_557451, baseEnd_557451] using wordTrace_append hprefix tailTrace_557451
  have hstable : (prefixWord ++ tailWord_557451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557451).length < 2 ^ (prefixWord ++ tailWord_557451).sum := by decide
  have hdescent : baseEnd_557451 < baseStart_557451 := by decide
  rcases family_descends (prefixWord ++ tailWord_557451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557476 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_557476 : Nat := 118140960795 + 557476 * 2 ^ 59
def prefixEnd_557476 : Nat := 4983230072969 + 3 ^ 40 * 557476 * 2
def baseEnd_557476 : Nat := 127223618375984936127209

theorem tailTrace_557476 : CollatzResearch.WordTrace tailWord_557476 prefixEnd_557476 127223618375984936127209 := by
  unfold tailWord_557476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10166410064183568082954141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13555213418911424110605521 10166410064183568082954141)
  ·
    refine ⟨3812403774068838031107803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10166410064183568082954141 3812403774068838031107803)
    ·
      refine ⟨5718605661103257046661705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3812403774068838031107803 5718605661103257046661705)
      ·
        refine ⟨4288954245827442784996279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5718605661103257046661705 4288954245827442784996279)
        ·
          refine ⟨6433431368741164177494419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288954245827442784996279 6433431368741164177494419)
          ·
            refine ⟨9650147053111746266241629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6433431368741164177494419 9650147053111746266241629)
            ·
              refine ⟨3618805144916904849840611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9650147053111746266241629 3618805144916904849840611)
              ·
                refine ⟨5428207717375357274760917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618805144916904849840611 5428207717375357274760917)
                ·
                  refine ⟨127223618375984936127209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5428207717375357274760917 127223618375984936127209)
                  ·
                    rfl

theorem cell21_557476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_557476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557476 prefixEnd_557476 := by exact prefixLift 557476
  have htrace : WordTrace (prefixWord ++ tailWord_557476) baseStart_557476 baseEnd_557476 := by
    simpa [prefixWord, tailWord_557476, baseEnd_557476] using wordTrace_append hprefix tailTrace_557476
  have hstable : (prefixWord ++ tailWord_557476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557476).length < 2 ^ (prefixWord ++ tailWord_557476).sum := by decide
  have hdescent : baseEnd_557476 < baseStart_557476 := by decide
  rcases family_descends (prefixWord ++ tailWord_557476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557479 : List Nat := [1, 1, 6, 1, 1, 3, 3, 5]
def baseStart_557479 : Nat := 118140960795 + 557479 * 2 ^ 59
def prefixEnd_557479 : Nat := 4983230072969 + 3 ^ 40 * 557479 * 2
def baseEnd_557479 : Nat := 42408101005619199192401

theorem tailTrace_557479 : CollatzResearch.WordTrace tailWord_557479 prefixEnd_557479 42408101005619199192401 := by
  unfold tailWord_557479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332929547356267678267491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13555286364904178452178327 20332929547356267678267491)
  ·
    refine ⟨30499394321034401517401237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20332929547356267678267491 30499394321034401517401237)
    ·
      refine ⟨1429659108798487571128183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30499394321034401517401237 1429659108798487571128183)
      ·
        refine ⟨2144488663197731356692275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429659108798487571128183 2144488663197731356692275)
        ·
          refine ⟨3216732994796597035038413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144488663197731356692275 3216732994796597035038413)
          ·
            refine ⟨1206274873048723888139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3216732994796597035038413 1206274873048723888139405)
            ·
              refine ⟨452353077393271458052277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1206274873048723888139405 452353077393271458052277)
              ·
                refine ⟨42408101005619199192401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452353077393271458052277 42408101005619199192401)
                ·
                  rfl

theorem cell21_557479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 5].length) (baseStart_557479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557479 prefixEnd_557479 := by exact prefixLift 557479
  have htrace : WordTrace (prefixWord ++ tailWord_557479) baseStart_557479 baseEnd_557479 := by
    simpa [prefixWord, tailWord_557479, baseEnd_557479] using wordTrace_append hprefix tailTrace_557479
  have hstable : (prefixWord ++ tailWord_557479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557479).length < 2 ^ (prefixWord ++ tailWord_557479).sum := by decide
  have hdescent : baseEnd_557479 < baseStart_557479 := by decide
  rcases family_descends (prefixWord ++ tailWord_557479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557569 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_557569 : Nat := 118140960795 + 557569 * 2 ^ 59
def prefixEnd_557569 : Nat := 4983230072969 + 3 ^ 40 * 557569 * 2
def baseEnd_557569 : Nat := 127244842243037441077019

theorem tailTrace_557569 : CollatzResearch.WordTrace tailWord_557569 prefixEnd_557569 127244842243037441077019 := by
  unfold tailWord_557569
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336212117030213049043761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13557474744686808699362507 20336212117030213049043761)
  ·
    refine ⟨15252159087772659786782821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20336212117030213049043761 15252159087772659786782821)
    ·
      refine ⟨2859779828957373710021779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15252159087772659786782821 2859779828957373710021779)
      ·
        refine ⟨4289669743436060565032669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859779828957373710021779 4289669743436060565032669)
        ·
          refine ⟨1608626153788522711887251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4289669743436060565032669 1608626153788522711887251)
          ·
            refine ⟨2412939230682784067830877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608626153788522711887251 2412939230682784067830877)
            ·
              refine ⟨904852211506044025436579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412939230682784067830877 904852211506044025436579)
              ·
                refine ⟨1357278317259066038154869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904852211506044025436579 1357278317259066038154869)
                ·
                  refine ⟨127244842243037441077019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1357278317259066038154869 127244842243037441077019)
                  ·
                    rfl

theorem cell21_557569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_557569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557569 prefixEnd_557569 := by exact prefixLift 557569
  have htrace : WordTrace (prefixWord ++ tailWord_557569) baseStart_557569 baseEnd_557569 := by
    simpa [prefixWord, tailWord_557569, baseEnd_557569] using wordTrace_append hprefix tailTrace_557569
  have hstable : (prefixWord ++ tailWord_557569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557569).length < 2 ^ (prefixWord ++ tailWord_557569).sum := by decide
  have hdescent : baseEnd_557569 < baseStart_557569 := by decide
  rcases family_descends (prefixWord ++ tailWord_557569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557614 : List Nat := [4, 1, 3, 1, 3, 9]
def baseStart_557614 : Nat := 118140960795 + 557614 * 2 ^ 59
def prefixEnd_557614 : Nat := 4983230072969 + 3 ^ 40 * 557614 * 2
def baseEnd_557614 : Nat := 4713152290967680104701

theorem tailTrace_557614 : CollatzResearch.WordTrace tailWord_557614 prefixEnd_557614 4713152290967680104701 := by
  unfold tailWord_557614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542231675233398216803987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13558568934578123822954597 2542231675233398216803987)
  ·
    refine ⟨3813347512850097325205981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2542231675233398216803987 3813347512850097325205981)
    ·
      refine ⟨1430005317318786496952243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3813347512850097325205981 1430005317318786496952243)
      ·
        refine ⟨2145007975978179745428365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430005317318786496952243 2145007975978179745428365)
        ·
          refine ⟨804377990991817404535637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2145007975978179745428365 804377990991817404535637)
          ·
            refine ⟨4713152290967680104701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 804377990991817404535637 4713152290967680104701)
            ·
              rfl

theorem cell21_557614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 9].length) (baseStart_557614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557614 prefixEnd_557614 := by exact prefixLift 557614
  have htrace : WordTrace (prefixWord ++ tailWord_557614) baseStart_557614 baseEnd_557614 := by
    simpa [prefixWord, tailWord_557614, baseEnd_557614] using wordTrace_append hprefix tailTrace_557614
  have hstable : (prefixWord ++ tailWord_557614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557614).length < 2 ^ (prefixWord ++ tailWord_557614).sum := by decide
  have hdescent : baseEnd_557614 < baseStart_557614 := by decide
  rcases family_descends (prefixWord ++ tailWord_557614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557620 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_557620 : Nat := 118140960795 + 557620 * 2 ^ 59
def prefixEnd_557620 : Nat := 4983230072969 + 3 ^ 40 * 557620 * 2
def baseEnd_557620 : Nat := 127256481137872685726915

theorem tailTrace_557620 : CollatzResearch.WordTrace tailWord_557620 prefixEnd_557620 127256481137872685726915 := by
  unfold tailWord_557620
  simp only [CollatzResearch.WordTrace]
  refine ⟨10169036119922724379575157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13558714826563632506100209 10169036119922724379575157)
  ·
    refine ⟨953347136242755410585171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10169036119922724379575157 953347136242755410585171)
    ·
      refine ⟨1430020704364133115877757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953347136242755410585171 1430020704364133115877757)
      ·
        refine ⟨536257764136549918454159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1430020704364133115877757 536257764136549918454159)
        ·
          refine ⟨804386646204824877681239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536257764136549918454159 804386646204824877681239)
          ·
            refine ⟨1206579969307237316521859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804386646204824877681239 1206579969307237316521859)
            ·
              refine ⟨1809869953960855974782789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206579969307237316521859 1809869953960855974782789)
              ·
                refine ⟨339350616367660495271773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1809869953960855974782789 339350616367660495271773)
                ·
                  refine ⟨127256481137872685726915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339350616367660495271773 127256481137872685726915)
                  ·
                    rfl

theorem cell21_557620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_557620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557620 prefixEnd_557620 := by exact prefixLift 557620
  have htrace : WordTrace (prefixWord ++ tailWord_557620) baseStart_557620 baseEnd_557620 := by
    simpa [prefixWord, tailWord_557620, baseEnd_557620] using wordTrace_append hprefix tailTrace_557620
  have hstable : (prefixWord ++ tailWord_557620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557620).length < 2 ^ (prefixWord ++ tailWord_557620).sum := by decide
  have hdescent : baseEnd_557620 < baseStart_557620 := by decide
  rcases family_descends (prefixWord ++ tailWord_557620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557645 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_557645 : Nat := 118140960795 + 557645 * 2 ^ 59
def prefixEnd_557645 : Nat := 4983230072969 + 3 ^ 40 * 557645 * 2
def baseEnd_557645 : Nat := 127262186478478197810197

theorem tailTrace_557645 : CollatzResearch.WordTrace tailWord_557645 prefixEnd_557645 127262186478478197810197 := by
  unfold tailWord_557645
  simp only [CollatzResearch.WordTrace]
  refine ⟨20338984064754878028810389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13559322709836585352540259 20338984064754878028810389)
  ·
    refine ⟨953389878035384907600487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20338984064754878028810389 953389878035384907600487)
    ·
      refine ⟨1430084817053077361400731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953389878035384907600487 1430084817053077361400731)
      ·
        refine ⟨2145127225579616042101097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430084817053077361400731 2145127225579616042101097)
        ·
          refine ⟨1608845419184712031575823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2145127225579616042101097 1608845419184712031575823)
          ·
            refine ⟨2413268128777068047363735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608845419184712031575823 2413268128777068047363735)
            ·
              refine ⟨3619902193165602071045603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413268128777068047363735 3619902193165602071045603)
              ·
                refine ⟨5429853289748403106568405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3619902193165602071045603 5429853289748403106568405)
                ·
                  refine ⟨127262186478478197810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5429853289748403106568405 127262186478478197810197)
                  ·
                    rfl

theorem cell21_557645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_557645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557645 prefixEnd_557645 := by exact prefixLift 557645
  have htrace : WordTrace (prefixWord ++ tailWord_557645) baseStart_557645 baseEnd_557645 := by
    simpa [prefixWord, tailWord_557645, baseEnd_557645] using wordTrace_append hprefix tailTrace_557645
  have hstable : (prefixWord ++ tailWord_557645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557645).length < 2 ^ (prefixWord ++ tailWord_557645).sum := by decide
  have hdescent : baseEnd_557645 < baseStart_557645 := by decide
  rcases family_descends (prefixWord ++ tailWord_557645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557693 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 4]
def baseStart_557693 : Nat := 118140960795 + 557693 * 2 ^ 59
def prefixEnd_557693 : Nat := 4983230072969 + 3 ^ 40 * 557693 * 2
def baseEnd_557693 : Nat := 127273140732440781010099

theorem tailTrace_557693 : CollatzResearch.WordTrace tailWord_557693 prefixEnd_557693 127273140732440781010099 := by
  unfold tailWord_557693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340734768580982226557733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13560489845720654817705155 20340734768580982226557733)
  ·
    refine ⟨3813887769108934167479575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20340734768580982226557733 3813887769108934167479575)
    ·
      refine ⟨5720831653663401251219363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3813887769108934167479575 5720831653663401251219363)
      ·
        refine ⟨8581247480495101876829045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720831653663401251219363 8581247480495101876829045)
        ·
          refine ⟨804491951296415800952723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8581247480495101876829045 804491951296415800952723)
          ·
            refine ⟨1206737926944623701429085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804491951296415800952723 1206737926944623701429085)
            ·
              refine ⟨452526722604233888035907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1206737926944623701429085 452526722604233888035907)
              ·
                refine ⟨678790083906350832053861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452526722604233888035907 678790083906350832053861)
                ·
                  refine ⟨127273140732440781010099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678790083906350832053861 127273140732440781010099)
                  ·
                    rfl

theorem cell21_557693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_557693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557693 prefixEnd_557693 := by exact prefixLift 557693
  have htrace : WordTrace (prefixWord ++ tailWord_557693) baseStart_557693 baseEnd_557693 := by
    simpa [prefixWord, tailWord_557693, baseEnd_557693] using wordTrace_append hprefix tailTrace_557693
  have hstable : (prefixWord ++ tailWord_557693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557693).length < 2 ^ (prefixWord ++ tailWord_557693).sum := by decide
  have hdescent : baseEnd_557693 < baseStart_557693 := by decide
  rcases family_descends (prefixWord ++ tailWord_557693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557839 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_557839 : Nat := 118140960795 + 557839 * 2 ^ 59
def prefixEnd_557839 : Nat := 4983230072969 + 3 ^ 40 * 557839 * 2
def baseEnd_557839 : Nat := 127306459921576971576467

theorem tailTrace_557839 : CollatzResearch.WordTrace tailWord_557839 prefixEnd_557839 127306459921576971576467 := by
  unfold tailWord_557839
  simp only [CollatzResearch.WordTrace]
  refine ⟨20346059826052049161372571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13564039884034699440915047 20346059826052049161372571)
  ·
    refine ⟨30519089739078073742058857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20346059826052049161372571 30519089739078073742058857)
    ·
      refine ⟨22889317304308555306544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30519089739078073742058857 22889317304308555306544143)
      ·
        refine ⟨34333975956462832959816215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22889317304308555306544143 34333975956462832959816215)
        ·
          refine ⟨51500963934694249439724323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34333975956462832959816215 51500963934694249439724323)
          ·
            refine ⟨77251445902041374159586485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51500963934694249439724323 77251445902041374159586485)
            ·
              refine ⟨7242323053316378827461233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77251445902041374159586485 7242323053316378827461233)
              ·
                refine ⟨5431742289987284120595925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7242323053316378827461233 5431742289987284120595925)
                ·
                  refine ⟨127306459921576971576467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5431742289987284120595925 127306459921576971576467)
                  ·
                    rfl

theorem cell21_557839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_557839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557839 prefixEnd_557839 := by exact prefixLift 557839
  have htrace : WordTrace (prefixWord ++ tailWord_557839) baseStart_557839 baseEnd_557839 := by
    simpa [prefixWord, tailWord_557839, baseEnd_557839] using wordTrace_append hprefix tailTrace_557839
  have hstable : (prefixWord ++ tailWord_557839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557839).length < 2 ^ (prefixWord ++ tailWord_557839).sum := by decide
  have hdescent : baseEnd_557839 < baseStart_557839 := by decide
  rcases family_descends (prefixWord ++ tailWord_557839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557856 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_557856 : Nat := 118140960795 + 557856 * 2 ^ 59
def prefixEnd_557856 : Nat := 4983230072969 + 3 ^ 40 * 557856 * 2
def baseEnd_557856 : Nat := 127310339553188719793099

theorem tailTrace_557856 : CollatzResearch.WordTrace tailWord_557856 prefixEnd_557856 127310339553188719793099 := by
  unfold tailWord_557856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173339933495230532370711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13564453244660307376494281 10173339933495230532370711)
  ·
    refine ⟨15260009900242845798556067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10173339933495230532370711 15260009900242845798556067)
    ·
      refine ⟨22890014850364268697834101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15260009900242845798556067 22890014850364268697834101)
      ·
        refine ⟨2145938892221650190421947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22890014850364268697834101 2145938892221650190421947)
        ·
          refine ⟨3218908338332475285632921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145938892221650190421947 3218908338332475285632921)
          ·
            refine ⟨2414181253749356464224691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218908338332475285632921 2414181253749356464224691)
            ·
              refine ⟨3621271880624034696337037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414181253749356464224691 3621271880624034696337037)
              ·
                refine ⟨1357976955234013011126389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3621271880624034696337037 1357976955234013011126389)
                ·
                  refine ⟨127310339553188719793099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1357976955234013011126389 127310339553188719793099)
                  ·
                    rfl

theorem cell21_557856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_557856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557856 prefixEnd_557856 := by exact prefixLift 557856
  have htrace : WordTrace (prefixWord ++ tailWord_557856) baseStart_557856 baseEnd_557856 := by
    simpa [prefixWord, tailWord_557856, baseEnd_557856] using wordTrace_append hprefix tailTrace_557856
  have hstable : (prefixWord ++ tailWord_557856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557856).length < 2 ^ (prefixWord ++ tailWord_557856).sum := by decide
  have hdescent : baseEnd_557856 < baseStart_557856 := by decide
  rcases family_descends (prefixWord ++ tailWord_557856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557876 : List Nat := [2, 5, 1, 1, 3, 2, 2, 5]
def baseStart_557876 : Nat := 118140960795 + 557876 * 2 ^ 59
def prefixEnd_557876 : Nat := 4983230072969 + 3 ^ 40 * 557876 * 2
def baseEnd_557876 : Nat := 42438301275224376486575

theorem tailTrace_557876 : CollatzResearch.WordTrace tailWord_557876 prefixEnd_557876 42438301275224376486575 := by
  unfold tailWord_557876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10173704663459002240234741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13564939551278669653646321 10173704663459002240234741)
  ·
    refine ⟨953784812199281460022007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10173704663459002240234741 953784812199281460022007)
    ·
      refine ⟨1430677218298922190033011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953784812199281460022007 1430677218298922190033011)
      ·
        refine ⟨2146015827448383285049517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430677218298922190033011 2146015827448383285049517)
        ·
          refine ⟨804755935293143731893569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2146015827448383285049517 804755935293143731893569)
          ·
            refine ⟨603566951469857798920177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804755935293143731893569 603566951469857798920177)
            ·
              refine ⟨452675213602393349190133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603566951469857798920177 452675213602393349190133)
              ·
                refine ⟨42438301275224376486575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452675213602393349190133 42438301275224376486575)
                ·
                  rfl

theorem cell21_557876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_557876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_557876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_557876 prefixEnd_557876 := by exact prefixLift 557876
  have htrace : WordTrace (prefixWord ++ tailWord_557876) baseStart_557876 baseEnd_557876 := by
    simpa [prefixWord, tailWord_557876, baseEnd_557876] using wordTrace_append hprefix tailTrace_557876
  have hstable : (prefixWord ++ tailWord_557876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557876).length < 2 ^ (prefixWord ++ tailWord_557876).sum := by decide
  have hdescent : baseEnd_557876 < baseStart_557876 := by decide
  rcases family_descends (prefixWord ++ tailWord_557876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558070 : List Nat := [5, 1, 1, 1, 3, 3, 7]
def baseStart_558070 : Nat := 118140960795 + 558070 * 2 ^ 59
def prefixEnd_558070 : Nat := 4983230072969 + 3 ^ 40 * 558070 * 2
def baseEnd_558070 : Nat := 14151019696530211469555

theorem tailTrace_558070 : CollatzResearch.WordTrace tailWord_558070 prefixEnd_558070 14151019696530211469555 := by
  unfold tailWord_558070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272155318013448475814479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13569656725476783742021109 1272155318013448475814479)
  ·
    refine ⟨1908232977020172713721719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272155318013448475814479 1908232977020172713721719)
    ·
      refine ⟨2862349465530259070582579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908232977020172713721719 2862349465530259070582579)
      ·
        refine ⟨4293524198295388605873869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862349465530259070582579 4293524198295388605873869)
        ·
          refine ⟨1610071574360770727202701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4293524198295388605873869 1610071574360770727202701)
          ·
            refine ⟨603776840385289022701013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1610071574360770727202701 603776840385289022701013)
            ·
              refine ⟨14151019696530211469555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 603776840385289022701013 14151019696530211469555)
              ·
                rfl

theorem cell21_558070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 7].length) (baseStart_558070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558070 prefixEnd_558070 := by exact prefixLift 558070
  have htrace : WordTrace (prefixWord ++ tailWord_558070) baseStart_558070 baseEnd_558070 := by
    simpa [prefixWord, tailWord_558070, baseEnd_558070] using wordTrace_append hprefix tailTrace_558070
  have hstable : (prefixWord ++ tailWord_558070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558070).length < 2 ^ (prefixWord ++ tailWord_558070).sum := by decide
  have hdescent : baseEnd_558070 < baseStart_558070 := by decide
  rcases family_descends (prefixWord ++ tailWord_558070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558132 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_558132 : Nat := 118140960795 + 558132 * 2 ^ 59
def prefixEnd_558132 : Nat := 4983230072969 + 3 ^ 40 * 558132 * 2
def baseEnd_558132 : Nat := 127373326513473573192535

theorem tailTrace_558132 : CollatzResearch.WordTrace tailWord_558132 prefixEnd_558132 127373326513473573192535 := by
  unfold tailWord_558132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178373206995280100894325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13571164275993706801192433 10178373206995280100894325)
  ·
    refine ⟨954222488155807509458843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10178373206995280100894325 954222488155807509458843)
    ·
      refine ⟨1431333732233711264188265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954222488155807509458843 1431333732233711264188265)
      ·
        refine ⟨1073500299175283448141199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431333732233711264188265 1073500299175283448141199)
        ·
          refine ⟨1610250448762925172211799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073500299175283448141199 1610250448762925172211799)
          ·
            refine ⟨2415375673144387758317699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610250448762925172211799 2415375673144387758317699)
            ·
              refine ⟨3623063509716581637476549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415375673144387758317699 3623063509716581637476549)
              ·
                refine ⟨679324408071859057026853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3623063509716581637476549 679324408071859057026853)
                ·
                  refine ⟨127373326513473573192535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679324408071859057026853 127373326513473573192535)
                  ·
                    rfl

theorem cell21_558132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_558132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558132 prefixEnd_558132 := by exact prefixLift 558132
  have htrace : WordTrace (prefixWord ++ tailWord_558132) baseStart_558132 baseEnd_558132 := by
    simpa [prefixWord, tailWord_558132, baseEnd_558132] using wordTrace_append hprefix tailTrace_558132
  have hstable : (prefixWord ++ tailWord_558132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558132).length < 2 ^ (prefixWord ++ tailWord_558132).sum := by decide
  have hdescent : baseEnd_558132 < baseStart_558132 := by decide
  rcases family_descends (prefixWord ++ tailWord_558132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558143 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_558143 : Nat := 118140960795 + 558143 * 2 ^ 59
def prefixEnd_558143 : Nat := 4983230072969 + 3 ^ 40 * 558143 * 2
def baseEnd_558143 : Nat := 127375836863339998509179

theorem tailTrace_558143 : CollatzResearch.WordTrace tailWord_558143 prefixEnd_558143 127375836863339998509179 := by
  unfold tailWord_558143
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357147616950709080439083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13571431744633806053626055 20357147616950709080439083)
  ·
    refine ⟨30535721425426063620658625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20357147616950709080439083 30535721425426063620658625)
    ·
      refine ⟨22901791069069547715493969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30535721425426063620658625 22901791069069547715493969)
      ·
        refine ⟨17176343301802160786620477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22901791069069547715493969 17176343301802160786620477)
        ·
          refine ⟨6441128738175810294982679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17176343301802160786620477 6441128738175810294982679)
          ·
            refine ⟨9661693107263715442474019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6441128738175810294982679 9661693107263715442474019)
            ·
              refine ⟨14492539660895573163711029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9661693107263715442474019 14492539660895573163711029)
              ·
                refine ⟨1358675593208959984097909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14492539660895573163711029 1358675593208959984097909)
                ·
                  refine ⟨127375836863339998509179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1358675593208959984097909 127375836863339998509179)
                  ·
                    rfl

theorem cell21_558143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_558143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558143 prefixEnd_558143 := by exact prefixLift 558143
  have htrace : WordTrace (prefixWord ++ tailWord_558143) baseStart_558143 baseEnd_558143 := by
    simpa [prefixWord, tailWord_558143, baseEnd_558143] using wordTrace_append hprefix tailTrace_558143
  have hstable : (prefixWord ++ tailWord_558143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558143).length < 2 ^ (prefixWord ++ tailWord_558143).sum := by decide
  have hdescent : baseEnd_558143 < baseStart_558143 := by decide
  rcases family_descends (prefixWord ++ tailWord_558143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558188 : List Nat := [2, 2, 1, 1, 3, 2, 10]
def baseStart_558188 : Nat := 118140960795 + 558188 * 2 ^ 59
def prefixEnd_558188 : Nat := 4983230072969 + 3 ^ 40 * 558188 * 2
def baseEnd_558188 : Nat := 14154011830714435584343

theorem tailTrace_558188 : CollatzResearch.WordTrace tailWord_558188 prefixEnd_558188 14154011830714435584343 := by
  unfold tailWord_558188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10179394450893840882913609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13572525934525121177218145 10179394450893840882913609)
  ·
    refine ⟨7634545838170380662185207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10179394450893840882913609 7634545838170380662185207)
    ·
      refine ⟨11451818757255570993277811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634545838170380662185207 11451818757255570993277811)
      ·
        refine ⟨17177728135883356489916717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11451818757255570993277811 17177728135883356489916717)
        ·
          refine ⟨6441648050956258683718769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17177728135883356489916717 6441648050956258683718769)
          ·
            refine ⟨4831236038217194012789077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6441648050956258683718769 4831236038217194012789077)
            ·
              refine ⟨14154011830714435584343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4831236038217194012789077 14154011830714435584343)
              ·
                rfl

theorem cell21_558188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 10].length) (baseStart_558188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558188 prefixEnd_558188 := by exact prefixLift 558188
  have htrace : WordTrace (prefixWord ++ tailWord_558188) baseStart_558188 baseEnd_558188 := by
    simpa [prefixWord, tailWord_558188, baseEnd_558188] using wordTrace_append hprefix tailTrace_558188
  have hstable : (prefixWord ++ tailWord_558188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558188).length < 2 ^ (prefixWord ++ tailWord_558188).sum := by decide
  have hdescent : baseEnd_558188 < baseStart_558188 := by decide
  rcases family_descends (prefixWord ++ tailWord_558188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558222 : List Nat := [4, 1, 1, 3, 2, 1, 4, 5]
def baseStart_558222 : Nat := 118140960795 + 558222 * 2 ^ 59
def prefixEnd_558222 : Nat := 4983230072969 + 3 ^ 40 * 558222 * 2
def baseEnd_558222 : Nat := 42464621913217805564117

theorem tailTrace_558222 : CollatzResearch.WordTrace tailWord_558222 prefixEnd_558222 42464621913217805564117 := by
  unfold tailWord_558222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545003622958063196570615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13573352655776337048376613 2545003622958063196570615)
  ·
    refine ⟨3817505434437094794855923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545003622958063196570615 3817505434437094794855923)
    ·
      refine ⟨5726258151655642192283885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3817505434437094794855923 5726258151655642192283885)
      ·
        refine ⟨2147346806870865822106457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5726258151655642192283885 2147346806870865822106457)
        ·
          refine ⟨1610510105153149366579843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2147346806870865822106457 1610510105153149366579843)
          ·
            refine ⟨2415765157729724049869765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610510105153149366579843 2415765157729724049869765)
            ·
              refine ⟨452955967074323259350581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2415765157729724049869765 452955967074323259350581)
              ·
                refine ⟨42464621913217805564117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 452955967074323259350581 42464621913217805564117)
                ·
                  rfl

theorem cell21_558222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_558222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558222 prefixEnd_558222 := by exact prefixLift 558222
  have htrace : WordTrace (prefixWord ++ tailWord_558222) baseStart_558222 baseEnd_558222 := by
    simpa [prefixWord, tailWord_558222, baseEnd_558222] using wordTrace_append hprefix tailTrace_558222
  have hstable : (prefixWord ++ tailWord_558222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558222).length < 2 ^ (prefixWord ++ tailWord_558222).sum := by decide
  have hdescent : baseEnd_558222 < baseStart_558222 := by decide
  rcases family_descends (prefixWord ++ tailWord_558222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558326 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_558326 : Nat := 118140960795 + 558326 * 2 ^ 59
def prefixEnd_558326 : Nat := 4983230072969 + 3 ^ 40 * 558326 * 2
def baseEnd_558326 : Nat := 127417599956572346958805

theorem tailTrace_558326 : CollatzResearch.WordTrace tailWord_558326 prefixEnd_558326 127417599956572346958805 := by
  unfold tailWord_558326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272738885955483208396927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13575881450191820889567221 1272738885955483208396927)
  ·
    refine ⟨1909108328933224812595391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272738885955483208396927 1909108328933224812595391)
    ·
      refine ⟨2863662493399837218893087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909108328933224812595391 2863662493399837218893087)
      ·
        refine ⟨4295493740099755828339631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863662493399837218893087 4295493740099755828339631)
        ·
          refine ⟨6443240610149633742509447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295493740099755828339631 6443240610149633742509447)
          ·
            refine ⟨9664860915224450613764171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443240610149633742509447 9664860915224450613764171)
            ·
              refine ⟨14497291372836675920646257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664860915224450613764171 14497291372836675920646257)
              ·
                refine ⟨10872968529627506940484693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14497291372836675920646257 10872968529627506940484693)
                ·
                  refine ⟨127417599956572346958805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10872968529627506940484693 127417599956572346958805)
                  ·
                    rfl

theorem cell21_558326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_558326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558326 prefixEnd_558326 := by exact prefixLift 558326
  have htrace : WordTrace (prefixWord ++ tailWord_558326) baseStart_558326 baseEnd_558326 := by
    simpa [prefixWord, tailWord_558326, baseEnd_558326] using wordTrace_append hprefix tailTrace_558326
  have hstable : (prefixWord ++ tailWord_558326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558326).length < 2 ^ (prefixWord ++ tailWord_558326).sum := by decide
  have hdescent : baseEnd_558326 < baseStart_558326 := by decide
  rcases family_descends (prefixWord ++ tailWord_558326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558371 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_558371 : Nat := 118140960795 + 558371 * 2 ^ 59
def prefixEnd_558371 : Nat := 4983230072969 + 3 ^ 40 * 558371 * 2
def baseEnd_558371 : Nat := 127427869569662268708713

theorem tailTrace_558371 : CollatzResearch.WordTrace tailWord_558371 prefixEnd_558371 127427869569662268708713 := by
  unfold tailWord_558371
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365463460124704019738967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13576975640083136013159311 20365463460124704019738967)
  ·
    refine ⟨30548195190187056029608451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365463460124704019738967 30548195190187056029608451)
    ·
      refine ⟨45822292785280584044412677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30548195190187056029608451 45822292785280584044412677)
      ·
        refine ⟨8591679897240109508327377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45822292785280584044412677 8591679897240109508327377)
        ·
          refine ⟨6443759922930082131245533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8591679897240109508327377 6443759922930082131245533)
          ·
            refine ⟨2416409971098780799217075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6443759922930082131245533 2416409971098780799217075)
            ·
              refine ⟨3624614956648171198825613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416409971098780799217075 3624614956648171198825613)
              ·
                refine ⟨1359230608743064199559605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624614956648171198825613 1359230608743064199559605)
                ·
                  refine ⟨127427869569662268708713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359230608743064199559605 127427869569662268708713)
                  ·
                    rfl

theorem cell21_558371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_558371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558371 prefixEnd_558371 := by exact prefixLift 558371
  have htrace : WordTrace (prefixWord ++ tailWord_558371) baseStart_558371 baseEnd_558371 := by
    simpa [prefixWord, tailWord_558371, baseEnd_558371] using wordTrace_append hprefix tailTrace_558371
  have hstable : (prefixWord ++ tailWord_558371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558371).length < 2 ^ (prefixWord ++ tailWord_558371).sum := by decide
  have hdescent : baseEnd_558371 < baseStart_558371 := by decide
  rcases family_descends (prefixWord ++ tailWord_558371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558388 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_558388 : Nat := 118140960795 + 558388 * 2 ^ 59
def prefixEnd_558388 : Nat := 4983230072969 + 3 ^ 40 * 558388 * 2
def baseEnd_558388 : Nat := 127431749201274016925345

theorem tailTrace_558388 : CollatzResearch.WordTrace tailWord_558388 prefixEnd_558388 127431749201274016925345 := by
  unfold tailWord_558388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183041750531557961553909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13577389000708743948738545 10183041750531557961553909)
  ·
    refine ⟨954660164112333558895679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10183041750531557961553909 954660164112333558895679)
    ·
      refine ⟨1431990246168500338343519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954660164112333558895679 1431990246168500338343519)
      ·
        refine ⟨2147985369252750507515279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1431990246168500338343519 2147985369252750507515279)
        ·
          refine ⟨3221978053879125761272919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147985369252750507515279 3221978053879125761272919)
          ·
            refine ⟨4832967080818688641909379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221978053879125761272919 4832967080818688641909379)
            ·
              refine ⟨7249450621228032962864069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832967080818688641909379 7249450621228032962864069)
              ·
                refine ⟨1359271991480256180537013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7249450621228032962864069 1359271991480256180537013)
                ·
                  refine ⟨127431749201274016925345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359271991480256180537013 127431749201274016925345)
                  ·
                    rfl

theorem cell21_558388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_558388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558388 prefixEnd_558388 := by exact prefixLift 558388
  have htrace : WordTrace (prefixWord ++ tailWord_558388) baseStart_558388 baseEnd_558388 := by
    simpa [prefixWord, tailWord_558388, baseEnd_558388] using wordTrace_append hprefix tailTrace_558388
  have hstable : (prefixWord ++ tailWord_558388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558388).length < 2 ^ (prefixWord ++ tailWord_558388).sum := by decide
  have hdescent : baseEnd_558388 < baseStart_558388 := by decide
  rcases family_descends (prefixWord ++ tailWord_558388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558436 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_558436 : Nat := 118140960795 + 558436 * 2 ^ 59
def prefixEnd_558436 : Nat := 4983230072969 + 3 ^ 40 * 558436 * 2
def baseEnd_558436 : Nat := 127442703455236600125247

theorem tailTrace_558436 : CollatzResearch.WordTrace tailWord_558436 prefixEnd_558436 127442703455236600125247 := by
  unfold tailWord_558436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10183917102444610060427581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13578556136592813413903441 10183917102444610060427581)
  ·
    refine ⟨3818968913416728772660343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10183917102444610060427581 3818968913416728772660343)
    ·
      refine ⟨5728453370125093158990515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818968913416728772660343 5728453370125093158990515)
      ·
        refine ⟨8592680055187639738485773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728453370125093158990515 8592680055187639738485773)
        ·
          refine ⟨3222255020695364901932165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8592680055187639738485773 3222255020695364901932165)
          ·
            refine ⟨604172816380380919112281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3222255020695364901932165 604172816380380919112281)
            ·
              refine ⟨453129612285285689334211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604172816380380919112281 453129612285285689334211)
              ·
                refine ⟨679694418427928534001317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453129612285285689334211 679694418427928534001317)
                ·
                  refine ⟨127442703455236600125247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679694418427928534001317 127442703455236600125247)
                  ·
                    rfl

theorem cell21_558436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_558436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558436 prefixEnd_558436 := by exact prefixLift 558436
  have htrace : WordTrace (prefixWord ++ tailWord_558436) baseStart_558436 baseEnd_558436 := by
    simpa [prefixWord, tailWord_558436, baseEnd_558436] using wordTrace_append hprefix tailTrace_558436
  have hstable : (prefixWord ++ tailWord_558436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558436).length < 2 ^ (prefixWord ++ tailWord_558436).sum := by decide
  have hdescent : baseEnd_558436 < baseStart_558436 := by decide
  rcases family_descends (prefixWord ++ tailWord_558436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558540 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_558540 : Nat := 118140960795 + 558540 * 2 ^ 59
def prefixEnd_558540 : Nat := 4983230072969 + 3 ^ 40 * 558540 * 2
def baseEnd_558540 : Nat := 127466437672155530391701

theorem tailTrace_558540 : CollatzResearch.WordTrace tailWord_558540 prefixEnd_558540 127466437672155530391701 := by
  unfold tailWord_558540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10185813698256222941320537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13581084931008297255094049 10185813698256222941320537)
  ·
    refine ⟨7639360273692167205990403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10185813698256222941320537 7639360273692167205990403)
    ·
      refine ⟨11459040410538250808985605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639360273692167205990403 11459040410538250808985605)
      ·
        refine ⟨2148570076975922026684801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11459040410538250808985605 2148570076975922026684801)
        ·
          refine ⟨1611427557731941520013601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2148570076975922026684801 1611427557731941520013601)
          ·
            refine ⟨1208570668298956140010201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611427557731941520013601 1208570668298956140010201)
            ·
              refine ⟨906428001224217105007651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1208570668298956140010201 906428001224217105007651)
              ·
                refine ⟨1359642001836325657511477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906428001224217105007651 1359642001836325657511477)
                ·
                  refine ⟨127466437672155530391701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1359642001836325657511477 127466437672155530391701)
                  ·
                    rfl

theorem cell21_558540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_558540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558540 prefixEnd_558540 := by exact prefixLift 558540
  have htrace : WordTrace (prefixWord ++ tailWord_558540) baseStart_558540 baseEnd_558540 := by
    simpa [prefixWord, tailWord_558540, baseEnd_558540] using wordTrace_append hprefix tailTrace_558540
  have hstable : (prefixWord ++ tailWord_558540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558540).length < 2 ^ (prefixWord ++ tailWord_558540).sum := by decide
  have hdescent : baseEnd_558540 < baseStart_558540 := by decide
  rcases family_descends (prefixWord ++ tailWord_558540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558568 : List Nat := [2, 1, 4, 1, 1, 2, 3, 7]
def baseStart_558568 : Nat := 118140960795 + 558568 * 2 ^ 59
def prefixEnd_558568 : Nat := 4983230072969 + 3 ^ 40 * 558568 * 2
def baseEnd_558568 : Nat := 42490942551211234641659

theorem tailTrace_558568 : CollatzResearch.WordTrace tailWord_558568 prefixEnd_558568 42490942551211234641659 := by
  unfold tailWord_558568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10186324320205503332330179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13581765760274004443106905 10186324320205503332330179)
  ·
    refine ⟨15279486480308254998495269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10186324320205503332330179 15279486480308254998495269)
    ·
      refine ⟨2864903715057797812217863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15279486480308254998495269 2864903715057797812217863)
      ·
        refine ⟨4297355572586696718326795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864903715057797812217863 4297355572586696718326795)
        ·
          refine ⟨6446033358880045077490193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4297355572586696718326795 6446033358880045077490193)
          ·
            refine ⟨4834525019160033808117645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6446033358880045077490193 4834525019160033808117645)
            ·
              refine ⟨1812946882185012678044117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4834525019160033808117645 1812946882185012678044117)
              ·
                refine ⟨42490942551211234641659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1812946882185012678044117 42490942551211234641659)
                ·
                  rfl

theorem cell21_558568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_558568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558568 prefixEnd_558568 := by exact prefixLift 558568
  have htrace : WordTrace (prefixWord ++ tailWord_558568) baseStart_558568 baseEnd_558568 := by
    simpa [prefixWord, tailWord_558568, baseEnd_558568] using wordTrace_append hprefix tailTrace_558568
  have hstable : (prefixWord ++ tailWord_558568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558568).length < 2 ^ (prefixWord ++ tailWord_558568).sum := by decide
  have hdescent : baseEnd_558568 < baseStart_558568 := by decide
  rcases family_descends (prefixWord ++ tailWord_558568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558605 : List Nat := [1, 7, 1, 1, 2, 1, 1, 3, 4]
def baseStart_558605 : Nat := 118140960795 + 558605 * 2 ^ 59
def prefixEnd_558605 : Nat := 4983230072969 + 3 ^ 40 * 558605 * 2
def baseEnd_558605 : Nat := 127481271557729861808235

theorem tailTrace_558605 : CollatzResearch.WordTrace tailWord_558605 prefixEnd_558605 127481271557729861808235 := by
  unfold tailWord_558605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373998141276961983757269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13582665427517974655838179 20373998141276961983757269)
  ·
    refine ⟨477515581436178796494311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20373998141276961983757269 477515581436178796494311)
    ·
      refine ⟨716273372154268194741467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477515581436178796494311 716273372154268194741467)
      ·
        refine ⟨1074410058231402292112201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716273372154268194741467 1074410058231402292112201)
        ·
          refine ⟨805807543673551719084151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074410058231402292112201 805807543673551719084151)
          ·
            refine ⟨1208711315510327578626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805807543673551719084151 1208711315510327578626227)
            ·
              refine ⟨1813066973265491367939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208711315510327578626227 1813066973265491367939341)
              ·
                refine ⟨679900114974559262977253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1813066973265491367939341 679900114974559262977253)
                ·
                  refine ⟨127481271557729861808235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679900114974559262977253 127481271557729861808235)
                  ·
                    rfl

theorem cell21_558605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_558605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558605 prefixEnd_558605 := by exact prefixLift 558605
  have htrace : WordTrace (prefixWord ++ tailWord_558605) baseStart_558605 baseEnd_558605 := by
    simpa [prefixWord, tailWord_558605, baseEnd_558605] using wordTrace_append hprefix tailTrace_558605
  have hstable : (prefixWord ++ tailWord_558605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558605).length < 2 ^ (prefixWord ++ tailWord_558605).sum := by decide
  have hdescent : baseEnd_558605 < baseStart_558605 := by decide
  rcases family_descends (prefixWord ++ tailWord_558605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558644 : List Nat := [2, 5, 1, 13]
def baseStart_558644 : Nat := 118140960795 + 558644 * 2 ^ 59
def prefixEnd_558644 : Nat := 4983230072969 + 3 ^ 40 * 558644 * 2
def baseEnd_558644 : Nat := 524650913123763212585

theorem tailTrace_558644 : CollatzResearch.WordTrace tailWord_558644 prefixEnd_558644 524650913123763212585 := by
  unfold tailWord_558644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10187710294067835822213493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13583613725423781096284657 10187710294067835822213493)
  ·
    refine ⟨955097840068859608332515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10187710294067835822213493 955097840068859608332515)
    ·
      refine ⟨1432646760103289412498773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955097840068859608332515 1432646760103289412498773)
      ·
        refine ⟨524650913123763212585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1432646760103289412498773 524650913123763212585)
        ·
          rfl

theorem cell21_558644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 13].length) (baseStart_558644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558644 prefixEnd_558644 := by exact prefixLift 558644
  have htrace : WordTrace (prefixWord ++ tailWord_558644) baseStart_558644 baseEnd_558644 := by
    simpa [prefixWord, tailWord_558644, baseEnd_558644] using wordTrace_append hprefix tailTrace_558644
  have hstable : (prefixWord ++ tailWord_558644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558644).length < 2 ^ (prefixWord ++ tailWord_558644).sum := by decide
  have hdescent : baseEnd_558644 < baseStart_558644 := by decide
  rcases family_descends (prefixWord ++ tailWord_558644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558689 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_558689 : Nat := 118140960795 + 558689 * 2 ^ 59
def prefixEnd_558689 : Nat := 4983230072969 + 3 ^ 40 * 558689 * 2
def baseEnd_558689 : Nat := 127500441502164382408063

theorem tailTrace_558689 : CollatzResearch.WordTrace tailWord_558689 prefixEnd_558689 127500441502164382408063 := by
  unfold tailWord_558689
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377061872972644329815121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13584707915315096219876747 20377061872972644329815121)
  ·
    refine ⟨15282796404729483247361341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20377061872972644329815121 15282796404729483247361341)
    ·
      refine ⟨5731048651773556217760503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15282796404729483247361341 5731048651773556217760503)
      ·
        refine ⟨8596572977660334326640755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731048651773556217760503 8596572977660334326640755)
        ·
          refine ⟨12894859466490501489961133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596572977660334326640755 12894859466490501489961133)
          ·
            refine ⟨4835572299933938058735425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12894859466490501489961133 4835572299933938058735425)
            ·
              refine ⟨3626679224950453544051569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835572299933938058735425 3626679224950453544051569)
              ·
                refine ⟨2720009418712840158038677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626679224950453544051569 2720009418712840158038677)
                ·
                  refine ⟨127500441502164382408063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2720009418712840158038677 127500441502164382408063)
                  ·
                    rfl

theorem cell21_558689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_558689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558689 prefixEnd_558689 := by exact prefixLift 558689
  have htrace : WordTrace (prefixWord ++ tailWord_558689) baseStart_558689 baseEnd_558689 := by
    simpa [prefixWord, tailWord_558689, baseEnd_558689] using wordTrace_append hprefix tailTrace_558689
  have hstable : (prefixWord ++ tailWord_558689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558689).length < 2 ^ (prefixWord ++ tailWord_558689).sum := by decide
  have hdescent : baseEnd_558689 < baseStart_558689 := by decide
  rcases family_descends (prefixWord ++ tailWord_558689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558692 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_558692 : Nat := 118140960795 + 558692 * 2 ^ 59
def prefixEnd_558692 : Nat := 4983230072969 + 3 ^ 40 * 558692 * 2
def baseEnd_558692 : Nat := 127501126143037043858057

theorem tailTrace_558692 : CollatzResearch.WordTrace tailWord_558692 prefixEnd_558692 127501126143037043858057 := by
  unfold tailWord_558692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188585645980887921087165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13584780861307850561449553 10188585645980887921087165)
  ·
    refine ⟨3820719617242832970407687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10188585645980887921087165 3820719617242832970407687)
    ·
      refine ⟨5731079425864249455611531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820719617242832970407687 5731079425864249455611531)
      ·
        refine ⟨8596619138796374183417297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731079425864249455611531 8596619138796374183417297)
        ·
          refine ⟨6447464354097280637562973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8596619138796374183417297 6447464354097280637562973)
          ·
            refine ⟨2417799132786480239086115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6447464354097280637562973 2417799132786480239086115)
            ·
              refine ⟨3626698699179720358629173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417799132786480239086115 3626698699179720358629173)
              ·
                refine ⟨340003003048098783621485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3626698699179720358629173 340003003048098783621485)
                ·
                  refine ⟨127501126143037043858057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340003003048098783621485 127501126143037043858057)
                  ·
                    rfl

theorem cell21_558692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_558692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558692 prefixEnd_558692 := by exact prefixLift 558692
  have htrace : WordTrace (prefixWord ++ tailWord_558692) baseStart_558692 baseEnd_558692 := by
    simpa [prefixWord, tailWord_558692, baseEnd_558692] using wordTrace_append hprefix tailTrace_558692
  have hstable : (prefixWord ++ tailWord_558692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558692).length < 2 ^ (prefixWord ++ tailWord_558692).sum := by decide
  have hdescent : baseEnd_558692 < baseStart_558692 := by decide
  rcases family_descends (prefixWord ++ tailWord_558692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558706 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_558706 : Nat := 118140960795 + 558706 * 2 ^ 59
def prefixEnd_558706 : Nat := 4983230072969 + 3 ^ 40 * 558706 * 2
def baseEnd_558706 : Nat := 127504321133776130624695

theorem tailTrace_558706 : CollatzResearch.WordTrace tailWord_558706 prefixEnd_558706 127504321133776130624695 := by
  unfold tailWord_558706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094420478477764058295993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13585121275940704155455981 5094420478477764058295993)
  ·
    refine ⟨3820815358858323043721995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5094420478477764058295993 3820815358858323043721995)
    ·
      refine ⟨5731223038287484565582993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820815358858323043721995 5731223038287484565582993)
      ·
        refine ⟨4298417278715613424187245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5731223038287484565582993 4298417278715613424187245)
        ·
          refine ⟨1611906479518355034070217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4298417278715613424187245 1611906479518355034070217)
          ·
            refine ⟨1208929859638766275552663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611906479518355034070217 1208929859638766275552663)
            ·
              refine ⟨1813394789458149413328995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208929859638766275552663 1813394789458149413328995)
              ·
                refine ⟨2720092184187224119993493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813394789458149413328995 2720092184187224119993493)
                ·
                  refine ⟨127504321133776130624695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2720092184187224119993493 127504321133776130624695)
                  ·
                    rfl

theorem cell21_558706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_558706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558706 prefixEnd_558706 := by exact prefixLift 558706
  have htrace : WordTrace (prefixWord ++ tailWord_558706) baseStart_558706 baseEnd_558706 := by
    simpa [prefixWord, tailWord_558706, baseEnd_558706] using wordTrace_append hprefix tailTrace_558706
  have hstable : (prefixWord ++ tailWord_558706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558706).length < 2 ^ (prefixWord ++ tailWord_558706).sum := by decide
  have hdescent : baseEnd_558706 < baseStart_558706 := by decide
  rcases family_descends (prefixWord ++ tailWord_558706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558709 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 3]
def baseStart_558709 : Nat := 118140960795 + 558709 * 2 ^ 59
def prefixEnd_558709 : Nat := 4983230072969 + 3 ^ 40 * 558709 * 2
def baseEnd_558709 : Nat := 127505005774648792074689

theorem tailTrace_558709 : CollatzResearch.WordTrace tailWord_558709 prefixEnd_558709 127505005774648792074689 := by
  unfold tailWord_558709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377791332900187745543181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13585194221933458497028787 20377791332900187745543181)
  ·
    refine ⟨7641671749837570404578693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20377791332900187745543181 7641671749837570404578693)
    ·
      refine ⟨1432813453094544450858505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7641671749837570404578693 1432813453094544450858505)
      ·
        refine ⟨1074610089820908338143879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432813453094544450858505 1074610089820908338143879)
        ·
          refine ⟨1611915134731362507215819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074610089820908338143879 1611915134731362507215819)
          ·
            refine ⟨2417872702097043760823729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611915134731362507215819 2417872702097043760823729)
            ·
              refine ⟨1813404526572782820617797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417872702097043760823729 1813404526572782820617797)
              ·
                refine ⟨340013348732396778865837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1813404526572782820617797 340013348732396778865837)
                ·
                  refine ⟨127505005774648792074689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340013348732396778865837 127505005774648792074689)
                  ·
                    rfl

theorem cell21_558709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_558709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558709 prefixEnd_558709 := by exact prefixLift 558709
  have htrace : WordTrace (prefixWord ++ tailWord_558709) baseStart_558709 baseEnd_558709 := by
    simpa [prefixWord, tailWord_558709, baseEnd_558709] using wordTrace_append hprefix tailTrace_558709
  have hstable : (prefixWord ++ tailWord_558709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558709).length < 2 ^ (prefixWord ++ tailWord_558709).sum := by decide
  have hdescent : baseEnd_558709 < baseStart_558709 := by decide
  rcases family_descends (prefixWord ++ tailWord_558709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558754 : List Nat := [3, 3, 1, 4, 1, 2, 7]
def baseStart_558754 : Nat := 118140960795 + 558754 * 2 ^ 59
def prefixEnd_558754 : Nat := 4983230072969 + 3 ^ 40 * 558754 * 2
def baseEnd_558754 : Nat := 14168363931970968202733

theorem tailTrace_558754 : CollatzResearch.WordTrace tailWord_558754 prefixEnd_558754 14168363931970968202733 := by
  unfold tailWord_558754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094858154434290107732829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13586288411824773620620877 5094858154434290107732829)
  ·
    refine ⟨1910571807912858790399811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5094858154434290107732829 1910571807912858790399811)
    ·
      refine ⟨2865857711869288185599717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1910571807912858790399811 2865857711869288185599717)
      ·
        refine ⟨537348320975491534799947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2865857711869288185599717 537348320975491534799947)
        ·
          refine ⟨806022481463237302199921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537348320975491534799947 806022481463237302199921)
          ·
            refine ⟨604516861097427976649941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806022481463237302199921 604516861097427976649941)
            ·
              refine ⟨14168363931970968202733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 604516861097427976649941 14168363931970968202733)
              ·
                rfl

theorem cell21_558754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 7].length) (baseStart_558754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558754 prefixEnd_558754 := by exact prefixLift 558754
  have htrace : WordTrace (prefixWord ++ tailWord_558754) baseStart_558754 baseEnd_558754 := by
    simpa [prefixWord, tailWord_558754, baseEnd_558754] using wordTrace_append hprefix tailTrace_558754
  have hstable : (prefixWord ++ tailWord_558754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558754).length < 2 ^ (prefixWord ++ tailWord_558754).sum := by decide
  have hdescent : baseEnd_558754 < baseStart_558754 := by decide
  rcases family_descends (prefixWord ++ tailWord_558754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558760 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_558760 : Nat := 118140960795 + 558760 * 2 ^ 59
def prefixEnd_558760 : Nat := 4983230072969 + 3 ^ 40 * 558760 * 2
def baseEnd_558760 : Nat := 127516644669484036724585

theorem tailTrace_558760 : CollatzResearch.WordTrace tailWord_558760 prefixEnd_558760 127516644669484036724585 := by
  unfold tailWord_558760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10189825727857711727824867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13586434303810282303766489 10189825727857711727824867)
  ·
    refine ⟨15284738591786567591737301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10189825727857711727824867 15284738591786567591737301)
    ·
      refine ⟨358236060744997677931343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15284738591786567591737301 358236060744997677931343)
      ·
        refine ⟨537354091117496516897015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358236060744997677931343 537354091117496516897015)
        ·
          refine ⟨806031136676244775345523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537354091117496516897015 806031136676244775345523)
          ·
            refine ⟨1209046705014367163018285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806031136676244775345523 1209046705014367163018285)
            ·
              refine ⟨453392514380387686131857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1209046705014367163018285 453392514380387686131857)
              ·
                refine ⟨340044385785290764598893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453392514380387686131857 340044385785290764598893)
                ·
                  refine ⟨127516644669484036724585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340044385785290764598893 127516644669484036724585)
                  ·
                    rfl

theorem cell21_558760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_558760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558760 prefixEnd_558760 := by exact prefixLift 558760
  have htrace : WordTrace (prefixWord ++ tailWord_558760) baseStart_558760 baseEnd_558760 := by
    simpa [prefixWord, tailWord_558760, baseEnd_558760] using wordTrace_append hprefix tailTrace_558760
  have hstable : (prefixWord ++ tailWord_558760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558760).length < 2 ^ (prefixWord ++ tailWord_558760).sum := by decide
  have hdescent : baseEnd_558760 < baseStart_558760 := by decide
  rcases family_descends (prefixWord ++ tailWord_558760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558813 : List Nat := [1, 4, 3, 3, 1, 9]
def baseStart_558813 : Nat := 118140960795 + 558813 * 2 ^ 59
def prefixEnd_558813 : Nat := 4983230072969 + 3 ^ 40 * 558813 * 2
def baseEnd_558813 : Nat := 4723286666354360086709

theorem tailTrace_558813 : CollatzResearch.WordTrace tailWord_558813 prefixEnd_558813 4723286666354360086709 := by
  unfold tailWord_558813
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381584524523413507329093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587723016348942338219395 20381584524523413507329093)
  ·
    refine ⟨3821547098348140032624205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20381584524523413507329093 3821547098348140032624205)
    ·
      refine ⟨1433080161880552512234077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3821547098348140032624205 1433080161880552512234077)
      ·
        refine ⟨537405060705207192087779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1433080161880552512234077 537405060705207192087779)
        ·
          refine ⟨806107591057810788131669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537405060705207192087779 806107591057810788131669)
          ·
            refine ⟨4723286666354360086709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 806107591057810788131669 4723286666354360086709)
            ·
              rfl

theorem cell21_558813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 9].length) (baseStart_558813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558813 prefixEnd_558813 := by exact prefixLift 558813
  have htrace : WordTrace (prefixWord ++ tailWord_558813) baseStart_558813 baseEnd_558813 := by
    simpa [prefixWord, tailWord_558813, baseEnd_558813] using wordTrace_append hprefix tailTrace_558813
  have hstable : (prefixWord ++ tailWord_558813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558813).length < 2 ^ (prefixWord ++ tailWord_558813).sum := by decide
  have hdescent : baseEnd_558813 < baseStart_558813 := by decide
  rcases family_descends (prefixWord ++ tailWord_558813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558819 : List Nat := [1, 1, 1, 7, 3, 1, 2, 2, 3]
def baseStart_558819 : Nat := 118140960795 + 558819 * 2 ^ 59
def prefixEnd_558819 : Nat := 4983230072969 + 3 ^ 40 * 558819 * 2
def baseEnd_558819 : Nat := 127530109273313045241131

theorem tailTrace_558819 : CollatzResearch.WordTrace tailWord_558819 prefixEnd_558819 127530109273313045241131 := by
  unfold tailWord_558819
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381803362501676532047511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13587868908334451021365007 20381803362501676532047511)
  ·
    refine ⟨30572705043752514798071267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20381803362501676532047511 30572705043752514798071267)
    ·
      refine ⟨45859057565628772197106901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30572705043752514798071267 45859057565628772197106901)
      ·
        refine ⟨1074821661694424348369693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 45859057565628772197106901 1074821661694424348369693)
        ·
          refine ⟨403058123135409130638635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1074821661694424348369693 403058123135409130638635)
          ·
            refine ⟨604587184703113695957953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403058123135409130638635 604587184703113695957953)
            ·
              refine ⟨453440388527335271968465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604587184703113695957953 453440388527335271968465)
              ·
                refine ⟨340080291395501453976349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453440388527335271968465 340080291395501453976349)
                ·
                  refine ⟨127530109273313045241131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340080291395501453976349 127530109273313045241131)
                  ·
                    rfl

theorem cell21_558819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].length) (baseStart_558819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558819 prefixEnd_558819 := by exact prefixLift 558819
  have htrace : WordTrace (prefixWord ++ tailWord_558819) baseStart_558819 baseEnd_558819 := by
    simpa [prefixWord, tailWord_558819, baseEnd_558819] using wordTrace_append hprefix tailTrace_558819
  have hstable : (prefixWord ++ tailWord_558819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558819).length < 2 ^ (prefixWord ++ tailWord_558819).sum := by decide
  have hdescent : baseEnd_558819 < baseStart_558819 := by decide
  rcases family_descends (prefixWord ++ tailWord_558819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558878 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_558878 : Nat := 118140960795 + 558878 * 2 ^ 59
def prefixEnd_558878 : Nat := 4983230072969 + 3 ^ 40 * 558878 * 2
def baseEnd_558878 : Nat := 127543573877142053757677

theorem tailTrace_558878 : CollatzResearch.WordTrace tailWord_558878 prefixEnd_558878 127543573877142053757677 := by
  unfold tailWord_558878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547994408660991201055661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13589303512858619738963525 2547994408660991201055661)
  ·
    refine ⟨955497903247871700395873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2547994408660991201055661 955497903247871700395873)
    ·
      refine ⟨716623427435903775296905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 955497903247871700395873 716623427435903775296905)
      ·
        refine ⟨537467570576927831472679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716623427435903775296905 537467570576927831472679)
        ·
          refine ⟨806201355865391747209019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537467570576927831472679 806201355865391747209019)
          ·
            refine ⟨1209302033798087620813529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806201355865391747209019 1209302033798087620813529)
            ·
              refine ⟨906976525348565715610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209302033798087620813529 906976525348565715610147)
              ·
                refine ⟨1360464788022848573415221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906976525348565715610147 1360464788022848573415221)
                ·
                  refine ⟨127543573877142053757677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1360464788022848573415221 127543573877142053757677)
                  ·
                    rfl

theorem cell21_558878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_558878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558878 prefixEnd_558878 := by exact prefixLift 558878
  have htrace : WordTrace (prefixWord ++ tailWord_558878) baseStart_558878 baseEnd_558878 := by
    simpa [prefixWord, tailWord_558878, baseEnd_558878] using wordTrace_append hprefix tailTrace_558878
  have hstable : (prefixWord ++ tailWord_558878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558878).length < 2 ^ (prefixWord ++ tailWord_558878).sum := by decide
  have hdescent : baseEnd_558878 < baseStart_558878 := by decide
  rcases family_descends (prefixWord ++ tailWord_558878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558920 : List Nat := [2, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_558920 : Nat := 118140960795 + 558920 * 2 ^ 59
def prefixEnd_558920 : Nat := 4983230072969 + 3 ^ 40 * 558920 * 2
def baseEnd_558920 : Nat := 127553158849359314057591

theorem tailTrace_558920 : CollatzResearch.WordTrace tailWord_558920 prefixEnd_558920 127553158849359314057591 := by
  unfold tailWord_558920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10192743567567885390737107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13590324756757180520982809 10192743567567885390737107)
  ·
    refine ⟨15289115351351828086105661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10192743567567885390737107 15289115351351828086105661)
    ·
      refine ⟨5733418256756935532289623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15289115351351828086105661 5733418256756935532289623)
      ·
        refine ⟨8600127385135403298434435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733418256756935532289623 8600127385135403298434435)
        ·
          refine ⟨12900191077703104947651653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8600127385135403298434435 12900191077703104947651653)
          ·
            refine ⟨2418785827069332177684685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12900191077703104947651653 2418785827069332177684685)
            ·
              refine ⟨907044685150999566631757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2418785827069332177684685 907044685150999566631757)
              ·
                refine ⟨340141756931624837486909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907044685150999566631757 340141756931624837486909)
                ·
                  refine ⟨127553158849359314057591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340141756931624837486909 127553158849359314057591)
                  ·
                    rfl

theorem cell21_558920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_558920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558920 prefixEnd_558920 := by exact prefixLift 558920
  have htrace : WordTrace (prefixWord ++ tailWord_558920) baseStart_558920 baseEnd_558920 := by
    simpa [prefixWord, tailWord_558920, baseEnd_558920] using wordTrace_append hprefix tailTrace_558920
  have hstable : (prefixWord ++ tailWord_558920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558920).length < 2 ^ (prefixWord ++ tailWord_558920).sum := by decide
  have hdescent : baseEnd_558920 < baseStart_558920 := by decide
  rcases family_descends (prefixWord ++ tailWord_558920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558962 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_558962 : Nat := 118140960795 + 558962 * 2 ^ 59
def prefixEnd_558962 : Nat := 4983230072969 + 3 ^ 40 * 558962 * 2
def baseEnd_558962 : Nat := 127562743821576574357505

theorem tailTrace_558962 : CollatzResearch.WordTrace tailWord_558962 prefixEnd_558962 127562743821576574357505 := by
  unfold tailWord_558962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096754750245902988625785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13591346000655741303002093 5096754750245902988625785)
  ·
    refine ⟨3822566062684427241469339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5096754750245902988625785 3822566062684427241469339)
    ·
      refine ⟨5733849094026640862204009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3822566062684427241469339 5733849094026640862204009)
      ·
        refine ⟨4300386820519980646653007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733849094026640862204009 4300386820519980646653007)
        ·
          refine ⟨6450580230779970969979511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300386820519980646653007 6450580230779970969979511)
          ·
            refine ⟨9675870346169956454969267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450580230779970969979511 9675870346169956454969267)
            ·
              refine ⟨14513805519254934682453901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675870346169956454969267 14513805519254934682453901)
              ·
                refine ⟨5442677069720600505920213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14513805519254934682453901 5442677069720600505920213)
                ·
                  refine ⟨127562743821576574357505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5442677069720600505920213 127562743821576574357505)
                  ·
                    rfl

theorem cell21_558962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_558962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558962 prefixEnd_558962 := by exact prefixLift 558962
  have htrace : WordTrace (prefixWord ++ tailWord_558962) baseStart_558962 baseEnd_558962 := by
    simpa [prefixWord, tailWord_558962, baseEnd_558962] using wordTrace_append hprefix tailTrace_558962
  have hstable : (prefixWord ++ tailWord_558962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558962).length < 2 ^ (prefixWord ++ tailWord_558962).sum := by decide
  have hdescent : baseEnd_558962 < baseStart_558962 := by decide
  rcases family_descends (prefixWord ++ tailWord_558962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_558993 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_558993 : Nat := 118140960795 + 558993 * 2 ^ 59
def prefixEnd_558993 : Nat := 4983230072969 + 3 ^ 40 * 558993 * 2
def baseEnd_558993 : Nat := 127569818443927409340775

theorem tailTrace_558993 : CollatzResearch.WordTrace tailWord_558993 prefixEnd_558993 127569818443927409340775 := by
  unfold tailWord_558993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388149663871304248881633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13592099775914202832587755 20388149663871304248881633)
  ·
    refine ⟨15291112247903478186661225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20388149663871304248881633 15291112247903478186661225)
    ·
      refine ⟨11468334185927608639995919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15291112247903478186661225 11468334185927608639995919)
      ·
        refine ⟨17202501278891412959993879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11468334185927608639995919 17202501278891412959993879)
        ·
          refine ⟨25803751918337119439990819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17202501278891412959993879 25803751918337119439990819)
          ·
            refine ⟨38705627877505679159986229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25803751918337119439990819 38705627877505679159986229)
            ·
              refine ⟨3628652613516157421248709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38705627877505679159986229 3628652613516157421248709)
              ·
                refine ⟨680372365034279516484133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3628652613516157421248709 680372365034279516484133)
                ·
                  refine ⟨127569818443927409340775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680372365034279516484133 127569818443927409340775)
                  ·
                    rfl

theorem cell21_558993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_558993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_558993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_558993 prefixEnd_558993 := by exact prefixLift 558993
  have htrace : WordTrace (prefixWord ++ tailWord_558993) baseStart_558993 baseEnd_558993 := by
    simpa [prefixWord, tailWord_558993, baseEnd_558993] using wordTrace_append hprefix tailTrace_558993
  have hstable : (prefixWord ++ tailWord_558993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_558993).length < 2 ^ (prefixWord ++ tailWord_558993).sum := by decide
  have hdescent : baseEnd_558993 < baseStart_558993 := by decide
  rcases family_descends (prefixWord ++ tailWord_558993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559055 : List Nat := [1, 1, 2, 1, 1, 5, 1, 6, 3]
def baseStart_559055 : Nat := 118140960795 + 559055 * 2 ^ 59
def prefixEnd_559055 : Nat := 4983230072969 + 3 ^ 40 * 559055 * 2
def baseEnd_559055 : Nat := 127583967688629079307315

theorem tailTrace_559055 : CollatzResearch.WordTrace tailWord_559055 prefixEnd_559055 127583967688629079307315 := by
  unfold tailWord_559055
  simp only [CollatzResearch.WordTrace]
  refine ⟨20390410989646688837638619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13593607326431125891759079 20390410989646688837638619)
  ·
    refine ⟨30585616484470033256457929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20390410989646688837638619 30585616484470033256457929)
    ·
      refine ⟨22939212363352524942343447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30585616484470033256457929 22939212363352524942343447)
      ·
        refine ⟨34408818545028787413515171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22939212363352524942343447 34408818545028787413515171)
        ·
          refine ⟨51613227817543181120272757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34408818545028787413515171 51613227817543181120272757)
          ·
            refine ⟨4838740107894673230025571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51613227817543181120272757 4838740107894673230025571)
            ·
              refine ⟨7258110161842009845038357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4838740107894673230025571 7258110161842009845038357)
              ·
                refine ⟨340223913836344211486173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7258110161842009845038357 340223913836344211486173)
                ·
                  refine ⟨127583967688629079307315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340223913836344211486173 127583967688629079307315)
                  ·
                    rfl

theorem cell21_559055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].length) (baseStart_559055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559055 prefixEnd_559055 := by exact prefixLift 559055
  have htrace : WordTrace (prefixWord ++ tailWord_559055) baseStart_559055 baseEnd_559055 := by
    simpa [prefixWord, tailWord_559055, baseEnd_559055] using wordTrace_append hprefix tailTrace_559055
  have hstable : (prefixWord ++ tailWord_559055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559055).length < 2 ^ (prefixWord ++ tailWord_559055).sum := by decide
  have hdescent : baseEnd_559055 < baseStart_559055 := by decide
  rcases family_descends (prefixWord ++ tailWord_559055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559089 : List Nat := [1, 2, 2, 2, 5, 2, 1, 3, 3]
def baseStart_559089 : Nat := 118140960795 + 559089 * 2 ^ 59
def prefixEnd_559089 : Nat := 4983230072969 + 3 ^ 40 * 559089 * 2
def baseEnd_559089 : Nat := 127591726951852575740579

theorem tailTrace_559089 : CollatzResearch.WordTrace tailWord_559089 prefixEnd_559089 127591726951852575740579 := by
  unfold tailWord_559089
  simp only [CollatzResearch.WordTrace]
  refine ⟨20391651071523512644376321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13594434047682341762917547 20391651071523512644376321)
  ·
    refine ⟨15293738303642634483282241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20391651071523512644376321 15293738303642634483282241)
    ·
      refine ⟨11470303727731975862461681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15293738303642634483282241 11470303727731975862461681)
      ·
        refine ⟨8602727795798981896846261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11470303727731975862461681 8602727795798981896846261)
        ·
          refine ⟨806505730856154552829337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8602727795798981896846261 806505730856154552829337)
          ·
            refine ⟨604879298142115914622003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806505730856154552829337 604879298142115914622003)
            ·
              refine ⟨907318947213173871933005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604879298142115914622003 907318947213173871933005)
              ·
                refine ⟨340244605204940201974877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907318947213173871933005 340244605204940201974877)
                ·
                  refine ⟨127591726951852575740579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340244605204940201974877 127591726951852575740579)
                  ·
                    rfl

theorem cell21_559089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_559089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559089 prefixEnd_559089 := by exact prefixLift 559089
  have htrace : WordTrace (prefixWord ++ tailWord_559089) baseStart_559089 baseEnd_559089 := by
    simpa [prefixWord, tailWord_559089, baseEnd_559089] using wordTrace_append hprefix tailTrace_559089
  have hstable : (prefixWord ++ tailWord_559089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559089).length < 2 ^ (prefixWord ++ tailWord_559089).sum := by decide
  have hdescent : baseEnd_559089 < baseStart_559089 := by decide
  rcases family_descends (prefixWord ++ tailWord_559089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559258 : List Nat := [3, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_559258 : Nat := 118140960795 + 559258 * 2 ^ 59
def prefixEnd_559258 : Nat := 4983230072969 + 3 ^ 40 * 559258 * 2
def baseEnd_559258 : Nat := 127630295054345837423567

theorem tailTrace_559258 : CollatzResearch.WordTrace tailWord_559258 prefixEnd_559258 127630295054345837423567 := by
  unfold tailWord_559258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099453751977813626819607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13598543338607503004852285 5099453751977813626819607)
  ·
    refine ⟨7649180627966720440229411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099453751977813626819607 7649180627966720440229411)
    ·
      refine ⟨11473770941950080660344117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7649180627966720440229411 11473770941950080660344117)
      ·
        refine ⟨1075666025807820061907261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11473770941950080660344117 1075666025807820061907261)
        ·
          refine ⟨403374759677932523215223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1075666025807820061907261 403374759677932523215223)
          ·
            refine ⟨605062139516898784822835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403374759677932523215223 605062139516898784822835)
            ·
              refine ⟨907593209275348177234253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605062139516898784822835 907593209275348177234253)
              ·
                refine ⟨340347453478255566462845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907593209275348177234253 340347453478255566462845)
                ·
                  refine ⟨127630295054345837423567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340347453478255566462845 127630295054345837423567)
                  ·
                    rfl

theorem cell21_559258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_559258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559258 prefixEnd_559258 := by exact prefixLift 559258
  have htrace : WordTrace (prefixWord ++ tailWord_559258) baseStart_559258 baseEnd_559258 := by
    simpa [prefixWord, tailWord_559258, baseEnd_559258] using wordTrace_append hprefix tailTrace_559258
  have hstable : (prefixWord ++ tailWord_559258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559258).length < 2 ^ (prefixWord ++ tailWord_559258).sum := by decide
  have hdescent : baseEnd_559258 < baseStart_559258 := by decide
  rcases family_descends (prefixWord ++ tailWord_559258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559331 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_559331 : Nat := 118140960795 + 559331 * 2 ^ 59
def prefixEnd_559331 : Nat := 4983230072969 + 3 ^ 40 * 559331 * 2
def baseEnd_559331 : Nat := 127646954648913932706751

theorem tailTrace_559331 : CollatzResearch.WordTrace tailWord_559331 prefixEnd_559331 127646954648913932706751 := by
  unfold tailWord_559331
  simp only [CollatzResearch.WordTrace]
  refine ⟨20400477536646787974685847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13600318357764525316457231 20400477536646787974685847)
  ·
    refine ⟨30600716304970181962028771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20400477536646787974685847 30600716304970181962028771)
    ·
      refine ⟨45901074457455272943043157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30600716304970181962028771 45901074457455272943043157)
      ·
        refine ⟨537903216298303979801287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 45901074457455272943043157 537903216298303979801287)
        ·
          refine ⟨806854824447455969701931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537903216298303979801287 806854824447455969701931)
          ·
            refine ⟨1210282236671183954552897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806854824447455969701931 1210282236671183954552897)
            ·
              refine ⟨907711677503387965914673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210282236671183954552897 907711677503387965914673)
              ·
                refine ⟨680783758127540974436005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907711677503387965914673 680783758127540974436005)
                ·
                  refine ⟨127646954648913932706751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680783758127540974436005 127646954648913932706751)
                  ·
                    rfl

theorem cell21_559331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_559331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559331 prefixEnd_559331 := by exact prefixLift 559331
  have htrace : WordTrace (prefixWord ++ tailWord_559331) baseStart_559331 baseEnd_559331 := by
    simpa [prefixWord, tailWord_559331, baseEnd_559331] using wordTrace_append hprefix tailTrace_559331
  have hstable : (prefixWord ++ tailWord_559331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559331).length < 2 ^ (prefixWord ++ tailWord_559331).sum := by decide
  have hdescent : baseEnd_559331 < baseStart_559331 := by decide
  rcases family_descends (prefixWord ++ tailWord_559331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559342 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_559342 : Nat := 118140960795 + 559342 * 2 ^ 59
def prefixEnd_559342 : Nat := 4983230072969 + 3 ^ 40 * 559342 * 2
def baseEnd_559342 : Nat := 127649464998780358023395

theorem tailTrace_559342 : CollatzResearch.WordTrace tailWord_559342 prefixEnd_559342 127649464998780358023395 := by
  unfold tailWord_559342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550109842450867106667035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13600585826404624568890853 2550109842450867106667035)
  ·
    refine ⟨3825164763676300660000553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2550109842450867106667035 3825164763676300660000553)
    ·
      refine ⟨2868873572757225495000415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3825164763676300660000553 2868873572757225495000415)
      ·
        refine ⟨4303310359135838242500623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868873572757225495000415 4303310359135838242500623)
        ·
          refine ⟨6454965538703757363750935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4303310359135838242500623 6454965538703757363750935)
          ·
            refine ⟨9682448308055636045626403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6454965538703757363750935 9682448308055636045626403)
            ·
              refine ⟨14523672462083454068439605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9682448308055636045626403 14523672462083454068439605)
              ·
                refine ⟨1361594293320323818916213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14523672462083454068439605 1361594293320323818916213)
                ·
                  refine ⟨127649464998780358023395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1361594293320323818916213 127649464998780358023395)
                  ·
                    rfl

theorem cell21_559342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_559342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559342 prefixEnd_559342 := by exact prefixLift 559342
  have htrace : WordTrace (prefixWord ++ tailWord_559342) baseStart_559342 baseEnd_559342 := by
    simpa [prefixWord, tailWord_559342, baseEnd_559342] using wordTrace_append hprefix tailTrace_559342
  have hstable : (prefixWord ++ tailWord_559342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559342).length < 2 ^ (prefixWord ++ tailWord_559342).sum := by decide
  have hdescent : baseEnd_559342 < baseStart_559342 := by decide
  rcases family_descends (prefixWord ++ tailWord_559342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559418 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_559418 : Nat := 118140960795 + 559418 * 2 ^ 59
def prefixEnd_559418 : Nat := 4983230072969 + 3 ^ 40 * 559418 * 2
def baseEnd_559418 : Nat := 127666809234221114756573

theorem tailTrace_559418 : CollatzResearch.WordTrace tailWord_559418 prefixEnd_559418 127666809234221114756573 := by
  unfold tailWord_559418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100912671832900458275727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13602433791554401222068605 5100912671832900458275727)
  ·
    refine ⟨7651369007749350687413591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100912671832900458275727 7651369007749350687413591)
    ·
      refine ⟨11477053511624026031120387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7651369007749350687413591 11477053511624026031120387)
      ·
        refine ⟨17215580267436039046680581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11477053511624026031120387 17215580267436039046680581)
        ·
          refine ⟨3227921300144257321252609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17215580267436039046680581 3227921300144257321252609)
          ·
            refine ⟨2420940975108192990939457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3227921300144257321252609 2420940975108192990939457)
            ·
              refine ⟨1815705731331144743204593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420940975108192990939457 1815705731331144743204593)
              ·
                refine ⟨1361779298498358557403445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815705731331144743204593 1361779298498358557403445)
                ·
                  refine ⟨127666809234221114756573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1361779298498358557403445 127666809234221114756573)
                  ·
                    rfl

theorem cell21_559418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_559418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559418 prefixEnd_559418 := by exact prefixLift 559418
  have htrace : WordTrace (prefixWord ++ tailWord_559418) baseStart_559418 baseEnd_559418 := by
    simpa [prefixWord, tailWord_559418, baseEnd_559418] using wordTrace_append hprefix tailTrace_559418
  have hstable : (prefixWord ++ tailWord_559418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559418).length < 2 ^ (prefixWord ++ tailWord_559418).sum := by decide
  have hdescent : baseEnd_559418 < baseStart_559418 := by decide
  rcases family_descends (prefixWord ++ tailWord_559418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559432 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_559432 : Nat := 118140960795 + 559432 * 2 ^ 59
def prefixEnd_559432 : Nat := 4983230072969 + 3 ^ 40 * 559432 * 2
def baseEnd_559432 : Nat := 127670004224960201523211

theorem tailTrace_559432 : CollatzResearch.WordTrace tailWord_559432 prefixEnd_559432 127670004224960201523211 := by
  unfold tailWord_559432
  simp only [CollatzResearch.WordTrace]
  refine ⟨10202080654640441112056275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13602774206187254816075033 10202080654640441112056275)
  ·
    refine ⟨15303120981960661668084413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10202080654640441112056275 15303120981960661668084413)
    ·
      refine ⟨5738670368235248125531655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15303120981960661668084413 5738670368235248125531655)
      ·
        refine ⟨8608005552352872188297483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738670368235248125531655 8608005552352872188297483)
        ·
          refine ⟨12912008328529308282446225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608005552352872188297483 12912008328529308282446225)
          ·
            refine ⟨9684006246396981211834669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12912008328529308282446225 9684006246396981211834669)
            ·
              refine ⟨3631502342398867954438001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9684006246396981211834669 3631502342398867954438001)
              ·
                refine ⟨2723626756799150965828501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631502342398867954438001 2723626756799150965828501)
                ·
                  refine ⟨127670004224960201523211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2723626756799150965828501 127670004224960201523211)
                  ·
                    rfl

theorem cell21_559432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_559432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559432 prefixEnd_559432 := by exact prefixLift 559432
  have htrace : WordTrace (prefixWord ++ tailWord_559432) baseStart_559432 baseEnd_559432 := by
    simpa [prefixWord, tailWord_559432, baseEnd_559432] using wordTrace_append hprefix tailTrace_559432
  have hstable : (prefixWord ++ tailWord_559432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559432).length < 2 ^ (prefixWord ++ tailWord_559432).sum := by decide
  have hdescent : baseEnd_559432 < baseStart_559432 := by decide
  rcases family_descends (prefixWord ++ tailWord_559432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559463 : List Nat := [1, 1, 5, 1, 3, 1, 1, 8]
def baseStart_559463 : Nat := 118140960795 + 559463 * 2 ^ 59
def prefixEnd_559463 : Nat := 4983230072969 + 3 ^ 40 * 559463 * 2
def baseEnd_559463 : Nat := 42559026282437012168827

theorem tailTrace_559463 : CollatzResearch.WordTrace tailWord_559463 prefixEnd_559463 42559026282437012168827 := by
  unfold tailWord_559463
  simp only [CollatzResearch.WordTrace]
  refine ⟨20405291972168574518491043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13603527981445716345660695 20405291972168574518491043)
  ·
    refine ⟨30607937958252861777736565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20405291972168574518491043 30607937958252861777736565)
    ·
      refine ⟨2869494183586205791662803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30607937958252861777736565 2869494183586205791662803)
      ·
        refine ⟨4304241275379308687494205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869494183586205791662803 4304241275379308687494205)
        ·
          refine ⟨1614090478267240757810327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4304241275379308687494205 1614090478267240757810327)
          ·
            refine ⟨2421135717400861136715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614090478267240757810327 2421135717400861136715491)
            ·
              refine ⟨3631703576101291705073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421135717400861136715491 3631703576101291705073237)
              ·
                refine ⟨42559026282437012168827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3631703576101291705073237 42559026282437012168827)
                ·
                  rfl

theorem cell21_559463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_559463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559463 prefixEnd_559463 := by exact prefixLift 559463
  have htrace : WordTrace (prefixWord ++ tailWord_559463) baseStart_559463 baseEnd_559463 := by
    simpa [prefixWord, tailWord_559463, baseEnd_559463] using wordTrace_append hprefix tailTrace_559463
  have hstable : (prefixWord ++ tailWord_559463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559463).length < 2 ^ (prefixWord ++ tailWord_559463).sum := by decide
  have hdescent : baseEnd_559463 < baseStart_559463 := by decide
  rcases family_descends (prefixWord ++ tailWord_559463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559466 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_559466 : Nat := 118140960795 + 559466 * 2 ^ 59
def prefixEnd_559466 : Nat := 4983230072969 + 3 ^ 40 * 559466 * 2
def baseEnd_559466 : Nat := 127677763488183697956475

theorem tailTrace_559466 : CollatzResearch.WordTrace tailWord_559466 prefixEnd_559466 127677763488183697956475 := by
  unfold tailWord_559466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101350347789426507712563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13603600927438470687233501 5101350347789426507712563)
  ·
    refine ⟨7652025521684139761568845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5101350347789426507712563 7652025521684139761568845)
    ·
      refine ⟨2869509570631552410588317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7652025521684139761568845 2869509570631552410588317)
      ·
        refine ⟨1076066088986832153970619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2869509570631552410588317 1076066088986832153970619)
        ·
          refine ⟨1614099133480248230955929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076066088986832153970619 1614099133480248230955929)
          ·
            refine ⟨1210574350110186173216947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1614099133480248230955929 1210574350110186173216947)
            ·
              refine ⟨1815861525165279259825421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210574350110186173216947 1815861525165279259825421)
              ·
                refine ⟨680948071936979722434533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815861525165279259825421 680948071936979722434533)
                ·
                  refine ⟨127677763488183697956475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680948071936979722434533 127677763488183697956475)
                  ·
                    rfl

theorem cell21_559466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_559466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559466 prefixEnd_559466 := by exact prefixLift 559466
  have htrace : WordTrace (prefixWord ++ tailWord_559466) baseStart_559466 baseEnd_559466 := by
    simpa [prefixWord, tailWord_559466, baseEnd_559466] using wordTrace_append hprefix tailTrace_559466
  have hstable : (prefixWord ++ tailWord_559466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559466).length < 2 ^ (prefixWord ++ tailWord_559466).sum := by decide
  have hdescent : baseEnd_559466 < baseStart_559466 := by decide
  rcases family_descends (prefixWord ++ tailWord_559466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559556 : List Nat := [2, 3, 3, 2, 2, 1, 8]
def baseStart_559556 : Nat := 118140960795 + 559556 * 2 ^ 59
def prefixEnd_559556 : Nat := 4983230072969 + 3 ^ 40 * 559556 * 2
def baseEnd_559556 : Nat := 14188700301595949050699

theorem tailTrace_559556 : CollatzResearch.WordTrace tailWord_559556 prefixEnd_559556 14188700301595949050699 := by
  unfold tailWord_559556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10204341980415825700813261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13605789307221100934417681 10204341980415825700813261)
  ·
    refine ⟨3826628242655934637804973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10204341980415825700813261 3826628242655934637804973)
    ·
      refine ⟨1434985590995975489176865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3826628242655934637804973 1434985590995975489176865)
      ·
        refine ⟨1076239193246981616882649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434985590995975489176865 1076239193246981616882649)
        ·
          refine ⟨807179394935236212661987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076239193246981616882649 807179394935236212661987)
          ·
            refine ⟨1210769092402854318992981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807179394935236212661987 1210769092402854318992981)
            ·
              refine ⟨14188700301595949050699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1210769092402854318992981 14188700301595949050699)
              ·
                rfl

theorem cell21_559556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 8].length) (baseStart_559556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559556 prefixEnd_559556 := by exact prefixLift 559556
  have htrace : WordTrace (prefixWord ++ tailWord_559556) baseStart_559556 baseEnd_559556 := by
    simpa [prefixWord, tailWord_559556, baseEnd_559556] using wordTrace_append hprefix tailTrace_559556
  have hstable : (prefixWord ++ tailWord_559556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559556).length < 2 ^ (prefixWord ++ tailWord_559556).sum := by decide
  have hdescent : baseEnd_559556 < baseStart_559556 := by decide
  rcases family_descends (prefixWord ++ tailWord_559556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559674 : List Nat := [3, 1, 1, 1, 3, 12]
def baseStart_559674 : Nat := 118140960795 + 559674 * 2 ^ 59
def prefixEnd_559674 : Nat := 4983230072969 + 3 ^ 40 * 559674 * 2
def baseEnd_559674 : Nat := 4730564145260057721829

theorem tailTrace_559674 : CollatzResearch.WordTrace tailWord_559674 prefixEnd_559674 4730564145260057721829 := by
  unfold tailWord_559674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103246943601039388605519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13608658516269438369614717 5103246943601039388605519)
  ·
    refine ⟨7654870415401559082908279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5103246943601039388605519 7654870415401559082908279)
    ·
      refine ⟨11482305623102338624362419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7654870415401559082908279 11482305623102338624362419)
      ·
        refine ⟨17223458434653507936543629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11482305623102338624362419 17223458434653507936543629)
        ·
          refine ⟨6458796912995065476203861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17223458434653507936543629 6458796912995065476203861)
          ·
            refine ⟨4730564145260057721829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6458796912995065476203861 4730564145260057721829)
            ·
              rfl

theorem cell21_559674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 12].length) (baseStart_559674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559674 prefixEnd_559674 := by exact prefixLift 559674
  have htrace : WordTrace (prefixWord ++ tailWord_559674) baseStart_559674 baseEnd_559674 := by
    simpa [prefixWord, tailWord_559674, baseEnd_559674] using wordTrace_append hprefix tailTrace_559674
  have hstable : (prefixWord ++ tailWord_559674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559674).length < 2 ^ (prefixWord ++ tailWord_559674).sum := by decide
  have hdescent : baseEnd_559674 < baseStart_559674 := by decide
  rcases family_descends (prefixWord ++ tailWord_559674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559677 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_559677 : Nat := 118140960795 + 559677 * 2 ^ 59
def prefixEnd_559677 : Nat := 4983230072969 + 3 ^ 40 * 559677 * 2
def baseEnd_559677 : Nat := 127725916562894219939377

theorem tailTrace_559677 : CollatzResearch.WordTrace tailWord_559677 prefixEnd_559677 127725916562894219939377 := by
  unfold tailWord_559677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20413097193393289066781285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13608731462262192711187523 20413097193393289066781285)
  ·
    refine ⟨3827455723761241700021491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20413097193393289066781285 3827455723761241700021491)
    ·
      refine ⟨5741183585641862550032237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3827455723761241700021491 5741183585641862550032237)
      ·
        refine ⟨2152943844615698456262089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5741183585641862550032237 2152943844615698456262089)
        ·
          refine ⟨1614707883461773842196567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2152943844615698456262089 1614707883461773842196567)
          ·
            refine ⟨2422061825192660763294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614707883461773842196567 2422061825192660763294851)
            ·
              refine ⟨3633092737788991144942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422061825192660763294851 3633092737788991144942277)
              ·
                refine ⟨681204888335435839676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3633092737788991144942277 681204888335435839676677)
                ·
                  refine ⟨127725916562894219939377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681204888335435839676677 127725916562894219939377)
                  ·
                    rfl

theorem cell21_559677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_559677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559677 prefixEnd_559677 := by exact prefixLift 559677
  have htrace : WordTrace (prefixWord ++ tailWord_559677) baseStart_559677 baseEnd_559677 := by
    simpa [prefixWord, tailWord_559677, baseEnd_559677] using wordTrace_append hprefix tailTrace_559677
  have hstable : (prefixWord ++ tailWord_559677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559677).length < 2 ^ (prefixWord ++ tailWord_559677).sum := by decide
  have hdescent : baseEnd_559677 < baseStart_559677 := by decide
  rcases family_descends (prefixWord ++ tailWord_559677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559857 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_559857 : Nat := 118140960795 + 559857 * 2 ^ 59
def prefixEnd_559857 : Nat := 4983230072969 + 3 ^ 40 * 559857 * 2
def baseEnd_559857 : Nat := 127766995015253906939009

theorem tailTrace_559857 : CollatzResearch.WordTrace tailWord_559857 prefixEnd_559857 127766995015253906939009 := by
  unfold tailWord_559857
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419662332741179808333825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13613108221827453205555883 20419662332741179808333825)
  ·
    refine ⟨15314746749555884856250369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20419662332741179808333825 15314746749555884856250369)
    ·
      refine ⟨11486060062166913642187777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15314746749555884856250369 11486060062166913642187777)
      ·
        refine ⟨8614545046625185231640833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11486060062166913642187777 8614545046625185231640833)
        ·
          refine ⟨6460908784968888923730625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8614545046625185231640833 6460908784968888923730625)
          ·
            refine ⟨4845681588726666692797969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6460908784968888923730625 4845681588726666692797969)
            ·
              refine ⟨3634261191545000019598477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845681588726666692797969 3634261191545000019598477)
              ·
                refine ⟨1362847946829375007349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634261191545000019598477 1362847946829375007349429)
                ·
                  refine ⟨127766995015253906939009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1362847946829375007349429 127766995015253906939009)
                  ·
                    rfl

theorem cell21_559857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_559857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559857 prefixEnd_559857 := by exact prefixLift 559857
  have htrace : WordTrace (prefixWord ++ tailWord_559857) baseStart_559857 baseEnd_559857 := by
    simpa [prefixWord, tailWord_559857, baseEnd_559857] using wordTrace_append hprefix tailTrace_559857
  have hstable : (prefixWord ++ tailWord_559857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559857).length < 2 ^ (prefixWord ++ tailWord_559857).sum := by decide
  have hdescent : baseEnd_559857 < baseStart_559857 := by decide
  rcases family_descends (prefixWord ++ tailWord_559857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559871 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_559871 : Nat := 118140960795 + 559871 * 2 ^ 59
def prefixEnd_559871 : Nat := 4983230072969 + 3 ^ 40 * 559871 * 2
def baseEnd_559871 : Nat := 127770190005992993705647

theorem tailTrace_559871 : CollatzResearch.WordTrace tailWord_559871 prefixEnd_559871 127770190005992993705647 := by
  unfold tailWord_559871
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420172954690460199343467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13613448636460306799562311 20420172954690460199343467)
  ·
    refine ⟨30630259432035690299015201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20420172954690460199343467 30630259432035690299015201)
    ·
      refine ⟨22972694574026767724261401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30630259432035690299015201 22972694574026767724261401)
      ·
        refine ⟨17229520930520075793196051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22972694574026767724261401 17229520930520075793196051)
        ·
          refine ⟨25844281395780113689794077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17229520930520075793196051 25844281395780113689794077)
          ·
            refine ⟨9691605523417542633672779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25844281395780113689794077 9691605523417542633672779)
            ·
              refine ⟨14537408285126313950509169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9691605523417542633672779 14537408285126313950509169)
              ·
                refine ⟨10903056213844735462881877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14537408285126313950509169 10903056213844735462881877)
                ·
                  refine ⟨127770190005992993705647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10903056213844735462881877 127770190005992993705647)
                  ·
                    rfl

theorem cell21_559871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_559871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559871 prefixEnd_559871 := by exact prefixLift 559871
  have htrace : WordTrace (prefixWord ++ tailWord_559871) baseStart_559871 baseEnd_559871 := by
    simpa [prefixWord, tailWord_559871, baseEnd_559871] using wordTrace_append hprefix tailTrace_559871
  have hstable : (prefixWord ++ tailWord_559871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559871).length < 2 ^ (prefixWord ++ tailWord_559871).sum := by decide
  have hdescent : baseEnd_559871 < baseStart_559871 := by decide
  rcases family_descends (prefixWord ++ tailWord_559871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559874 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_559874 : Nat := 118140960795 + 559874 * 2 ^ 59
def prefixEnd_559874 : Nat := 4983230072969 + 3 ^ 40 * 559874 * 2
def baseEnd_559874 : Nat := 127770874646865655155641

theorem tailTrace_559874 : CollatzResearch.WordTrace tailWord_559874 prefixEnd_559874 127770874646865655155641 := by
  unfold tailWord_559874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5105070593419897927925669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13613521582453061141135117 5105070593419897927925669)
  ·
    refine ⟨957200736266230861486063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5105070593419897927925669 957200736266230861486063)
    ·
      refine ⟨1435801104399346292229095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957200736266230861486063 1435801104399346292229095)
      ·
        refine ⟨2153701656599019438343643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435801104399346292229095 2153701656599019438343643)
        ·
          refine ⟨3230552484898529157515465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2153701656599019438343643 3230552484898529157515465)
          ·
            refine ⟨2422914363673896868136599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3230552484898529157515465 2422914363673896868136599)
            ·
              refine ⟨3634371545510845302204899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422914363673896868136599 3634371545510845302204899)
              ·
                refine ⟨5451557318266267953307349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3634371545510845302204899 5451557318266267953307349)
                ·
                  refine ⟨127770874646865655155641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5451557318266267953307349 127770874646865655155641)
                  ·
                    rfl

theorem cell21_559874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_559874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559874 prefixEnd_559874 := by exact prefixLift 559874
  have htrace : WordTrace (prefixWord ++ tailWord_559874) baseStart_559874 baseEnd_559874 := by
    simpa [prefixWord, tailWord_559874, baseEnd_559874] using wordTrace_append hprefix tailTrace_559874
  have hstable : (prefixWord ++ tailWord_559874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559874).length < 2 ^ (prefixWord ++ tailWord_559874).sum := by decide
  have hdescent : baseEnd_559874 < baseStart_559874 := by decide
  rcases family_descends (prefixWord ++ tailWord_559874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559942 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_559942 : Nat := 118140960795 + 559942 * 2 ^ 59
def prefixEnd_559942 : Nat := 4983230072969 + 3 ^ 40 * 559942 * 2
def baseEnd_559942 : Nat := 127786393173312648022169

theorem tailTrace_559942 : CollatzResearch.WordTrace tailWord_559942 prefixEnd_559942 127786393173312648022169 := by
  unfold tailWord_559942
  simp only [CollatzResearch.WordTrace]
  refine ⟨638211329294788728911815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13615175024955492883452053 638211329294788728911815)
  ·
    refine ⟨957316993942183093367723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638211329294788728911815 957316993942183093367723)
    ·
      refine ⟨1435975490913274640051585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957316993942183093367723 1435975490913274640051585)
      ·
        refine ⟨1076981618184955980038689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1435975490913274640051585 1076981618184955980038689)
        ·
          refine ⟨807736213638716985029017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1076981618184955980038689 807736213638716985029017)
          ·
            refine ⟨605802160229037738771763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807736213638716985029017 605802160229037738771763)
            ·
              refine ⟨908703240343556608157645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605802160229037738771763 908703240343556608157645)
              ·
                refine ⟨340763715128833728059117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908703240343556608157645 340763715128833728059117)
                ·
                  refine ⟨127786393173312648022169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340763715128833728059117 127786393173312648022169)
                  ·
                    rfl

theorem cell21_559942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_559942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559942 prefixEnd_559942 := by exact prefixLift 559942
  have htrace : WordTrace (prefixWord ++ tailWord_559942) baseStart_559942 baseEnd_559942 := by
    simpa [prefixWord, tailWord_559942, baseEnd_559942] using wordTrace_append hprefix tailTrace_559942
  have hstable : (prefixWord ++ tailWord_559942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559942).length < 2 ^ (prefixWord ++ tailWord_559942).sum := by decide
  have hdescent : baseEnd_559942 < baseStart_559942 := by decide
  rcases family_descends (prefixWord ++ tailWord_559942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_559967 : List Nat := [1, 1, 2, 3, 1, 3, 5, 2, 3]
def baseStart_559967 : Nat := 118140960795 + 559967 * 2 ^ 59
def prefixEnd_559967 : Nat := 4983230072969 + 3 ^ 40 * 559967 * 2
def baseEnd_559967 : Nat := 127792098513918160105451

theorem tailTrace_559967 : CollatzResearch.WordTrace tailWord_559967 prefixEnd_559967 127792098513918160105451 := by
  unfold tailWord_559967
  simp only [CollatzResearch.WordTrace]
  refine ⟨20423674362342668594838155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13615782908228445729892103 20423674362342668594838155)
  ·
    refine ⟨30635511543514002892257233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20423674362342668594838155 30635511543514002892257233)
    ·
      refine ⟨22976633657635502169192925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30635511543514002892257233 22976633657635502169192925)
      ·
        refine ⟨8616237621613313313447347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22976633657635502169192925 8616237621613313313447347)
        ·
          refine ⟨12924356432419969970171021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8616237621613313313447347 12924356432419969970171021)
          ·
            refine ⟨4846633662157488738814133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12924356432419969970171021 4846633662157488738814133)
            ·
              refine ⟨454371905827264569263825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4846633662157488738814133 454371905827264569263825)
              ·
                refine ⟨340778929370448426947869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454371905827264569263825 340778929370448426947869)
                ·
                  refine ⟨127792098513918160105451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340778929370448426947869 127792098513918160105451)
                  ·
                    rfl

theorem cell21_559967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].length) (baseStart_559967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_559967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_559967 prefixEnd_559967 := by exact prefixLift 559967
  have htrace : WordTrace (prefixWord ++ tailWord_559967) baseStart_559967 baseEnd_559967 := by
    simpa [prefixWord, tailWord_559967, baseEnd_559967] using wordTrace_append hprefix tailTrace_559967
  have hstable : (prefixWord ++ tailWord_559967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_559967).length < 2 ^ (prefixWord ++ tailWord_559967).sum := by decide
  have hdescent : baseEnd_559967 < baseStart_559967 := by decide
  rcases family_descends (prefixWord ++ tailWord_559967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560018 : List Nat := [3, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_560018 : Nat := 118140960795 + 560018 * 2 ^ 59
def prefixEnd_560018 : Nat := 4983230072969 + 3 ^ 40 * 560018 * 2
def baseEnd_560018 : Nat := 127803737408753404755347

theorem tailTrace_560018 : CollatzResearch.WordTrace tailWord_560018 prefixEnd_560018 127803737408753404755347 := by
  unfold tailWord_560018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106383621289476076236177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13617022990105269536629805 5106383621289476076236177)
  ·
    refine ⟨3829787715967107057177133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5106383621289476076236177 3829787715967107057177133)
    ·
      refine ⟨1436170393487665146441425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3829787715967107057177133 1436170393487665146441425)
      ·
        refine ⟨1077127795115748859831069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1436170393487665146441425 1077127795115748859831069)
        ·
          refine ⟨403922923168405822436651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1077127795115748859831069 403922923168405822436651)
          ·
            refine ⟨605884384752608733654977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403922923168405822436651 605884384752608733654977)
            ·
              refine ⟨454413288564456550241233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605884384752608733654977 454413288564456550241233)
              ·
                refine ⟨340809966423342412680925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454413288564456550241233 340809966423342412680925)
                ·
                  refine ⟨127803737408753404755347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340809966423342412680925 127803737408753404755347)
                  ·
                    rfl

theorem cell21_560018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_560018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560018 prefixEnd_560018 := by exact prefixLift 560018
  have htrace : WordTrace (prefixWord ++ tailWord_560018) baseStart_560018 baseEnd_560018 := by
    simpa [prefixWord, tailWord_560018, baseEnd_560018] using wordTrace_append hprefix tailTrace_560018
  have hstable : (prefixWord ++ tailWord_560018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560018).length < 2 ^ (prefixWord ++ tailWord_560018).sum := by decide
  have hdescent : baseEnd_560018 < baseStart_560018 := by decide
  rcases family_descends (prefixWord ++ tailWord_560018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560077 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 5]
def baseStart_560077 : Nat := 118140960795 + 560077 * 2 ^ 59
def prefixEnd_560077 : Nat := 4983230072969 + 3 ^ 40 * 560077 * 2
def baseEnd_560077 : Nat := 127817202012582413271893

theorem tailTrace_560077 : CollatzResearch.WordTrace tailWord_560077 prefixEnd_560077 127817202012582413271893 := by
  unfold tailWord_560077
  simp only [CollatzResearch.WordTrace]
  refine ⟨20427686391944157381342485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13618457594629438254228323 20427686391944157381342485)
  ·
    refine ⟨957547799622382377250429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20427686391944157381342485 957547799622382377250429)
    ·
      refine ⟨359080424858393391468911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 957547799622382377250429 359080424858393391468911)
      ·
        refine ⟨538620637287590087203367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359080424858393391468911 538620637287590087203367)
        ·
          refine ⟨807930955931385130805051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538620637287590087203367 807930955931385130805051)
          ·
            refine ⟨1211896433897077696207577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807930955931385130805051 1211896433897077696207577)
            ·
              refine ⟨908922325422808272155683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211896433897077696207577 908922325422808272155683)
              ·
                refine ⟨1363383488134212408233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908922325422808272155683 1363383488134212408233525)
                ·
                  refine ⟨127817202012582413271893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363383488134212408233525 127817202012582413271893)
                  ·
                    rfl

theorem cell21_560077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_560077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560077 prefixEnd_560077 := by exact prefixLift 560077
  have htrace : WordTrace (prefixWord ++ tailWord_560077) baseStart_560077 baseEnd_560077 := by
    simpa [prefixWord, tailWord_560077, baseEnd_560077] using wordTrace_append hprefix tailTrace_560077
  have hstable : (prefixWord ++ tailWord_560077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560077).length < 2 ^ (prefixWord ++ tailWord_560077).sum := by decide
  have hdescent : baseEnd_560077 < baseStart_560077 := by decide
  rcases family_descends (prefixWord ++ tailWord_560077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560178 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_560178 : Nat := 118140960795 + 560178 * 2 ^ 59
def prefixEnd_560178 : Nat := 4983230072969 + 3 ^ 40 * 560178 * 2
def baseEnd_560178 : Nat := 127840251588628682088353

theorem tailTrace_560178 : CollatzResearch.WordTrace tailWord_560178 prefixEnd_560178 127840251588628682088353 := by
  unfold tailWord_560178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107842541144562907692297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13620913443052167753846125 5107842541144562907692297)
  ·
    refine ⟨3830881905858422180769223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5107842541144562907692297 3830881905858422180769223)
    ·
      refine ⟨5746322858787633271153835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830881905858422180769223 5746322858787633271153835)
      ·
        refine ⟨8619484288181449906730753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746322858787633271153835 8619484288181449906730753)
        ·
          refine ⟨6464613216136087430048065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8619484288181449906730753 6464613216136087430048065)
          ·
            refine ⟨4848459912102065572536049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6464613216136087430048065 4848459912102065572536049)
            ·
              refine ⟨3636344934076549179402037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4848459912102065572536049 3636344934076549179402037)
              ·
                refine ⟨340907337569676485568941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3636344934076549179402037 340907337569676485568941)
                ·
                  refine ⟨127840251588628682088353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340907337569676485568941 127840251588628682088353)
                  ·
                    rfl

theorem cell21_560178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_560178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560178 prefixEnd_560178 := by exact prefixLift 560178
  have htrace : WordTrace (prefixWord ++ tailWord_560178) baseStart_560178 baseEnd_560178 := by
    simpa [prefixWord, tailWord_560178, baseEnd_560178] using wordTrace_append hprefix tailTrace_560178
  have hstable : (prefixWord ++ tailWord_560178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560178).length < 2 ^ (prefixWord ++ tailWord_560178).sum := by decide
  have hdescent : baseEnd_560178 < baseStart_560178 := by decide
  rcases family_descends (prefixWord ++ tailWord_560178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560192 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_560192 : Nat := 118140960795 + 560192 * 2 ^ 59
def prefixEnd_560192 : Nat := 4983230072969 + 3 ^ 40 * 560192 * 2
def baseEnd_560192 : Nat := 127843446579367768854991

theorem tailTrace_560192 : CollatzResearch.WordTrace tailWord_560192 prefixEnd_560192 127843446579367768854991 := by
  unfold tailWord_560192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10215940393263766010889415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13621253857685021347852553 10215940393263766010889415)
  ·
    refine ⟨15323910589895649016334123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10215940393263766010889415 15323910589895649016334123)
    ·
      refine ⟨22985865884843473524501185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15323910589895649016334123 22985865884843473524501185)
      ·
        refine ⟨17239399413632605143375889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22985865884843473524501185 17239399413632605143375889)
        ·
          refine ⟨12929549560224453857531917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17239399413632605143375889 12929549560224453857531917)
          ·
            refine ⟨4848581085084170196574469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12929549560224453857531917 4848581085084170196574469)
            ·
              refine ⟨909108953453281911857713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4848581085084170196574469 909108953453281911857713)
              ·
                refine ⟨681831715089961433893285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909108953453281911857713 681831715089961433893285)
                ·
                  refine ⟨127843446579367768854991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681831715089961433893285 127843446579367768854991)
                  ·
                    rfl

theorem cell21_560192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_560192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560192 prefixEnd_560192 := by exact prefixLift 560192
  have htrace : WordTrace (prefixWord ++ tailWord_560192) baseStart_560192 baseEnd_560192 := by
    simpa [prefixWord, tailWord_560192, baseEnd_560192] using wordTrace_append hprefix tailTrace_560192
  have hstable : (prefixWord ++ tailWord_560192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560192).length < 2 ^ (prefixWord ++ tailWord_560192).sum := by decide
  have hdescent : baseEnd_560192 < baseStart_560192 := by decide
  rcases family_descends (prefixWord ++ tailWord_560192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560313 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_560313 : Nat := 118140960795 + 560313 * 2 ^ 59
def prefixEnd_560313 : Nat := 4983230072969 + 3 ^ 40 * 560313 * 2
def baseEnd_560313 : Nat := 127871060427898447338077

theorem tailTrace_560313 : CollatzResearch.WordTrace tailWord_560313 prefixEnd_560313 127871060427898447338077 := by
  unfold tailWord_560313
  simp only [CollatzResearch.WordTrace]
  refine ⟨20436294019089169686933593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13624196012726113124622395 20436294019089169686933593)
  ·
    refine ⟨15327220514316877265200195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20436294019089169686933593 15327220514316877265200195)
    ·
      refine ⟨22990830771475315897800293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15327220514316877265200195 22990830771475315897800293)
      ·
        refine ⟨4310780769651621730837555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22990830771475315897800293 4310780769651621730837555)
        ·
          refine ⟨6466171154477432596256333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4310780769651621730837555 6466171154477432596256333)
          ·
            refine ⟨2424814182929037223596125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6466171154477432596256333 2424814182929037223596125)
            ·
              refine ⟨909305318598388958848547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2424814182929037223596125 909305318598388958848547)
              ·
                refine ⟨1363957977897583438272821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909305318598388958848547 1363957977897583438272821)
                ·
                  refine ⟨127871060427898447338077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363957977897583438272821 127871060427898447338077)
                  ·
                    rfl

theorem cell21_560313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_560313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560313 prefixEnd_560313 := by exact prefixLift 560313
  have htrace : WordTrace (prefixWord ++ tailWord_560313) baseStart_560313 baseEnd_560313 := by
    simpa [prefixWord, tailWord_560313, baseEnd_560313] using wordTrace_append hprefix tailTrace_560313
  have hstable : (prefixWord ++ tailWord_560313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560313).length < 2 ^ (prefixWord ++ tailWord_560313).sum := by decide
  have hdescent : baseEnd_560313 < baseStart_560313 := by decide
  rcases family_descends (prefixWord ++ tailWord_560313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560437 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 4]
def baseStart_560437 : Nat := 118140960795 + 560437 * 2 ^ 59
def prefixEnd_560437 : Nat := 4983230072969 + 3 ^ 40 * 560437 * 2
def baseEnd_560437 : Nat := 127899358917301787271157

theorem tailTrace_560437 : CollatzResearch.WordTrace tailWord_560437 prefixEnd_560437 127899358917301787271157 := by
  unfold tailWord_560437
  simp only [CollatzResearch.WordTrace]
  refine ⟨20440816670639938864447565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13627211113759959242965043 20440816670639938864447565)
  ·
    refine ⟨7665306251489977074167837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20440816670639938864447565 7665306251489977074167837)
    ·
      refine ⟨2874489844308741402812939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7665306251489977074167837 2874489844308741402812939)
      ·
        refine ⟨4311734766463112104219409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874489844308741402812939 4311734766463112104219409)
        ·
          refine ⟨3233801074847334078164557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4311734766463112104219409 3233801074847334078164557)
          ·
            refine ⟨1212675403067750279311709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3233801074847334078164557 1212675403067750279311709)
            ·
              refine ⟨454753276150406354741891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212675403067750279311709 454753276150406354741891)
              ·
                refine ⟨682129914225609532112837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454753276150406354741891 682129914225609532112837)
                ·
                  refine ⟨127899358917301787271157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682129914225609532112837 127899358917301787271157)
                  ·
                    rfl

theorem cell21_560437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_560437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560437 prefixEnd_560437 := by exact prefixLift 560437
  have htrace : WordTrace (prefixWord ++ tailWord_560437) baseStart_560437 baseEnd_560437 := by
    simpa [prefixWord, tailWord_560437, baseEnd_560437] using wordTrace_append hprefix tailTrace_560437
  have hstable : (prefixWord ++ tailWord_560437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560437).length < 2 ^ (prefixWord ++ tailWord_560437).sum := by decide
  have hdescent : baseEnd_560437 < baseStart_560437 := by decide
  rcases family_descends (prefixWord ++ tailWord_560437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560448 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_560448 : Nat := 118140960795 + 560448 * 2 ^ 59
def prefixEnd_560448 : Nat := 4983230072969 + 3 ^ 40 * 560448 * 2
def baseEnd_560448 : Nat := 127901869267168212587801

theorem tailTrace_560448 : CollatzResearch.WordTrace tailWord_560448 prefixEnd_560448 127901869267168212587801 := by
  unfold tailWord_560448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10220608936800043871548999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13627478582400058495398665 10220608936800043871548999)
  ·
    refine ⟨15330913405200065807323499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10220608936800043871548999 15330913405200065807323499)
    ·
      refine ⟨22996370107800098710985249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15330913405200065807323499 22996370107800098710985249)
      ·
        refine ⟨17247277580850074033238937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22996370107800098710985249 17247277580850074033238937)
        ·
          refine ⟨12935458185637555524929203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17247277580850074033238937 12935458185637555524929203)
          ·
            refine ⟨19403187278456333287393805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12935458185637555524929203 19403187278456333287393805)
            ·
              refine ⟨7276195229421124982772677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19403187278456333287393805 7276195229421124982772677)
              ·
                refine ⟨1364286605516460934269877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7276195229421124982772677 1364286605516460934269877)
                ·
                  refine ⟨127901869267168212587801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1364286605516460934269877 127901869267168212587801)
                  ·
                    rfl

theorem cell21_560448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_560448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560448 prefixEnd_560448 := by exact prefixLift 560448
  have htrace : WordTrace (prefixWord ++ tailWord_560448) baseStart_560448 baseEnd_560448 := by
    simpa [prefixWord, tailWord_560448, baseEnd_560448] using wordTrace_append hprefix tailTrace_560448
  have hstable : (prefixWord ++ tailWord_560448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560448).length < 2 ^ (prefixWord ++ tailWord_560448).sum := by decide
  have hdescent : baseEnd_560448 < baseStart_560448 := by decide
  rcases family_descends (prefixWord ++ tailWord_560448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560479 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_560479 : Nat := 118140960795 + 560479 * 2 ^ 59
def prefixEnd_560479 : Nat := 4983230072969 + 3 ^ 40 * 560479 * 2
def baseEnd_560479 : Nat := 127908943889519047571071

theorem tailTrace_560479 : CollatzResearch.WordTrace tailWord_560479 prefixEnd_560479 127908943889519047571071 := by
  unfold tailWord_560479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20442348536487780037476491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13628232357658520024984327 20442348536487780037476491)
  ·
    refine ⟨30663522804731670056214737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20442348536487780037476491 30663522804731670056214737)
    ·
      refine ⟨22997642103548752542161053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30663522804731670056214737 22997642103548752542161053)
      ·
        refine ⟨8624115788830782203310395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22997642103548752542161053 8624115788830782203310395)
        ·
          refine ⟨12936173683246173304965593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624115788830782203310395 12936173683246173304965593)
          ·
            refine ⟨9702130262434629978724195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936173683246173304965593 9702130262434629978724195)
            ·
              refine ⟨14553195393651944968086293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9702130262434629978724195 14553195393651944968086293)
              ·
                refine ⟨682181034077434920379045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14553195393651944968086293 682181034077434920379045)
                ·
                  refine ⟨127908943889519047571071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682181034077434920379045 127908943889519047571071)
                  ·
                    rfl

theorem cell21_560479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_560479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560479 prefixEnd_560479 := by exact prefixLift 560479
  have htrace : WordTrace (prefixWord ++ tailWord_560479) baseStart_560479 baseEnd_560479 := by
    simpa [prefixWord, tailWord_560479, baseEnd_560479] using wordTrace_append hprefix tailTrace_560479
  have hstable : (prefixWord ++ tailWord_560479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560479).length < 2 ^ (prefixWord ++ tailWord_560479).sum := by decide
  have hdescent : baseEnd_560479 < baseStart_560479 := by decide
  rcases family_descends (prefixWord ++ tailWord_560479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560530 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_560530 : Nat := 118140960795 + 560530 * 2 ^ 59
def prefixEnd_560530 : Nat := 4983230072969 + 3 ^ 40 * 560530 * 2
def baseEnd_560530 : Nat := 127920582784354292220967

theorem tailTrace_560530 : CollatzResearch.WordTrace tailWord_560530 prefixEnd_560530 127920582784354292220967 := by
  unfold tailWord_560530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111052164825753936895761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13629472439535343831722029 5111052164825753936895761)
  ·
    refine ⟨3833289123619315452671821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5111052164825753936895761 3833289123619315452671821)
    ·
      refine ⟨1437483421357243294751933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3833289123619315452671821 1437483421357243294751933)
      ·
        refine ⟨539056283008966235531975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1437483421357243294751933 539056283008966235531975)
        ·
          refine ⟨808584424513449353297963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539056283008966235531975 808584424513449353297963)
          ·
            refine ⟨1212876636770174029946945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808584424513449353297963 1212876636770174029946945)
            ·
              refine ⟨909657477577630522460209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212876636770174029946945 909657477577630522460209)
              ·
                refine ⟨682243108183222891845157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909657477577630522460209 682243108183222891845157)
                ·
                  refine ⟨127920582784354292220967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682243108183222891845157 127920582784354292220967)
                  ·
                    rfl

theorem cell21_560530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_560530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560530 prefixEnd_560530 := by exact prefixLift 560530
  have htrace : WordTrace (prefixWord ++ tailWord_560530) baseStart_560530 baseEnd_560530 := by
    simpa [prefixWord, tailWord_560530, baseEnd_560530] using wordTrace_append hprefix tailTrace_560530
  have hstable : (prefixWord ++ tailWord_560530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560530).length < 2 ^ (prefixWord ++ tailWord_560530).sum := by decide
  have hdescent : baseEnd_560530 < baseStart_560530 := by decide
  rcases family_descends (prefixWord ++ tailWord_560530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560600 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_560600 : Nat := 118140960795 + 560600 * 2 ^ 59
def prefixEnd_560600 : Nat := 4983230072969 + 3 ^ 40 * 560600 * 2
def baseEnd_560600 : Nat := 127936557738049726054157

theorem tailTrace_560600 : CollatzResearch.WordTrace tailWord_560600 prefixEnd_560600 127936557738049726054157 := by
  unfold tailWord_560600
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223380884524708851315627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13631174512699611801754169 10223380884524708851315627)
  ·
    refine ⟨15335071326787063276973441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10223380884524708851315627 15335071326787063276973441)
    ·
      refine ⟨11501303495090297457730081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15335071326787063276973441 11501303495090297457730081)
      ·
        refine ⟨8625977621317723093297561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11501303495090297457730081 8625977621317723093297561)
        ·
          refine ⟨6469483215988292319973171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625977621317723093297561 6469483215988292319973171)
          ·
            refine ⟨9704224823982438479959757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469483215988292319973171 9704224823982438479959757)
            ·
              refine ⟨3639084308993414429984909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9704224823982438479959757 3639084308993414429984909)
              ·
                refine ⟨1364656615872530411244341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3639084308993414429984909 1364656615872530411244341)
                ·
                  refine ⟨127936557738049726054157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1364656615872530411244341 127936557738049726054157)
                  ·
                    rfl

theorem cell21_560600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_560600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560600 prefixEnd_560600 := by exact prefixLift 560600
  have htrace : WordTrace (prefixWord ++ tailWord_560600) baseStart_560600 baseEnd_560600 := by
    simpa [prefixWord, tailWord_560600, baseEnd_560600] using wordTrace_append hprefix tailTrace_560600
  have hstable : (prefixWord ++ tailWord_560600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560600).length < 2 ^ (prefixWord ++ tailWord_560600).sum := by decide
  have hdescent : baseEnd_560600 < baseStart_560600 := by decide
  rcases family_descends (prefixWord ++ tailWord_560600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560651 : List Nat := [1, 1, 1, 1, 8, 1, 3, 2, 3]
def baseStart_560651 : Nat := 118140960795 + 560651 * 2 ^ 59
def prefixEnd_560651 : Nat := 4983230072969 + 3 ^ 40 * 560651 * 2
def baseEnd_560651 : Nat := 127948196632884970704053

theorem tailTrace_560651 : CollatzResearch.WordTrace tailWord_560651 prefixEnd_560651 127948196632884970704053 := by
  unfold tailWord_560651
  simp only [CollatzResearch.WordTrace]
  refine ⟨20448621891864653412737807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13632414594576435608491871 20448621891864653412737807)
  ·
    refine ⟨30672932837796980119106711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20448621891864653412737807 30672932837796980119106711)
    ·
      refine ⟨46009399256695470178660067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30672932837796980119106711 46009399256695470178660067)
      ·
        refine ⟨69014098885043205267990101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46009399256695470178660067 69014098885043205267990101)
        ·
          refine ⟨808758971309100061734259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 69014098885043205267990101 808758971309100061734259)
          ·
            refine ⟨1213138456963650092601389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808758971309100061734259 1213138456963650092601389)
            ·
              refine ⟨454926921361368784725521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1213138456963650092601389 454926921361368784725521)
              ·
                refine ⟨341195191021026588544141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454926921361368784725521 341195191021026588544141)
                ·
                  refine ⟨127948196632884970704053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341195191021026588544141 127948196632884970704053)
                  ·
                    rfl

theorem cell21_560651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].length) (baseStart_560651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560651 prefixEnd_560651 := by exact prefixLift 560651
  have htrace : WordTrace (prefixWord ++ tailWord_560651) baseStart_560651 baseEnd_560651 := by
    simpa [prefixWord, tailWord_560651, baseEnd_560651] using wordTrace_append hprefix tailTrace_560651
  have hstable : (prefixWord ++ tailWord_560651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560651).length < 2 ^ (prefixWord ++ tailWord_560651).sum := by decide
  have hdescent : baseEnd_560651 < baseStart_560651 := by decide
  rcases family_descends (prefixWord ++ tailWord_560651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560769 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_560769 : Nat := 118140960795 + 560769 * 2 ^ 59
def prefixEnd_560769 : Nat := 4983230072969 + 3 ^ 40 * 560769 * 2
def baseEnd_560769 : Nat := 127975125840542987737145

theorem tailTrace_560769 : CollatzResearch.WordTrace tailWord_560769 prefixEnd_560769 127975125840542987737145 := by
  unfold tailWord_560769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20452925705437159565533361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13635283803624773043688907 20452925705437159565533361)
  ·
    refine ⟨15339694279077869674150021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20452925705437159565533361 15339694279077869674150021)
    ·
      refine ⟨2876192677327100563903129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15339694279077869674150021 2876192677327100563903129)
      ·
        refine ⟨2157144507995325422927347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2876192677327100563903129 2157144507995325422927347)
        ·
          refine ⟨3235716761992988134391021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2157144507995325422927347 3235716761992988134391021)
          ·
            refine ⟨1213393785747370550396633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3235716761992988134391021 1213393785747370550396633)
            ·
              refine ⟨910045339310527912797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213393785747370550396633 910045339310527912797475)
              ·
                refine ⟨1365068008965791869196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910045339310527912797475 1365068008965791869196213)
                ·
                  refine ⟨127975125840542987737145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1365068008965791869196213 127975125840542987737145)
                  ·
                    rfl

theorem cell21_560769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_560769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560769 prefixEnd_560769 := by exact prefixLift 560769
  have htrace : WordTrace (prefixWord ++ tailWord_560769) baseStart_560769 baseEnd_560769 := by
    simpa [prefixWord, tailWord_560769, baseEnd_560769] using wordTrace_append hprefix tailTrace_560769
  have hstable : (prefixWord ++ tailWord_560769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560769).length < 2 ^ (prefixWord ++ tailWord_560769).sum := by decide
  have hdescent : baseEnd_560769 < baseStart_560769 := by decide
  rcases family_descends (prefixWord ++ tailWord_560769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560904 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_560904 : Nat := 118140960795 + 560904 * 2 ^ 59
def prefixEnd_560904 : Nat := 4983230072969 + 3 ^ 40 * 560904 * 2
def baseEnd_560904 : Nat := 128005934679812752986869

theorem tailTrace_560904 : CollatzResearch.WordTrace tailWord_560904 prefixEnd_560904 128005934679812752986869 := by
  unfold tailWord_560904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228924779974038810848883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13638566373298718414465177 10228924779974038810848883)
  ·
    refine ⟨15343387169961058216273325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10228924779974038810848883 15343387169961058216273325)
    ·
      refine ⟨5753770188735396831102497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15343387169961058216273325 5753770188735396831102497)
      ·
        refine ⟨4315327641551547623326873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5753770188735396831102497 4315327641551547623326873)
        ·
          refine ⟨3236495731163660717495155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315327641551547623326873 3236495731163660717495155)
          ·
            refine ⟨4854743596745491076242733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236495731163660717495155 4854743596745491076242733)
            ·
              refine ⟨1820528848779559153591025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854743596745491076242733 1820528848779559153591025)
              ·
                refine ⟨1365396636584669365193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820528848779559153591025 1365396636584669365193269)
                ·
                  refine ⟨128005934679812752986869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1365396636584669365193269 128005934679812752986869)
                  ·
                    rfl

theorem cell21_560904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_560904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560904 prefixEnd_560904 := by exact prefixLift 560904
  have htrace : WordTrace (prefixWord ++ tailWord_560904) baseStart_560904 baseEnd_560904 := by
    simpa [prefixWord, tailWord_560904, baseEnd_560904] using wordTrace_append hprefix tailTrace_560904
  have hstable : (prefixWord ++ tailWord_560904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560904).length < 2 ^ (prefixWord ++ tailWord_560904).sum := by decide
  have hdescent : baseEnd_560904 < baseStart_560904 := by decide
  rcases family_descends (prefixWord ++ tailWord_560904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560952 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_560952 : Nat := 118140960795 + 560952 * 2 ^ 59
def prefixEnd_560952 : Nat := 4983230072969 + 3 ^ 40 * 560952 * 2
def baseEnd_560952 : Nat := 128016888933775336186771

theorem tailTrace_560952 : CollatzResearch.WordTrace tailWord_560952 prefixEnd_560952 128016888933775336186771 := by
  unfold tailWord_560952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229800131887090909722555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13639733509182787879630073 10229800131887090909722555)
  ·
    refine ⟨15344700197830636364583833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10229800131887090909722555 15344700197830636364583833)
    ·
      refine ⟨11508525148372977273437875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15344700197830636364583833 11508525148372977273437875)
      ·
        refine ⟨17262787722559465910156813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508525148372977273437875 17262787722559465910156813)
        ·
          refine ⟨6473545395959799716308805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17262787722559465910156813 6473545395959799716308805)
          ·
            refine ⟨1213789761742462446807901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6473545395959799716308805 1213789761742462446807901)
            ·
              refine ⟨455171160653423417552963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1213789761742462446807901 455171160653423417552963)
              ·
                refine ⟨682756740980135126329445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455171160653423417552963 682756740980135126329445)
                ·
                  refine ⟨128016888933775336186771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682756740980135126329445 128016888933775336186771)
                  ·
                    rfl

theorem cell21_560952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_560952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_560952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_560952 prefixEnd_560952 := by exact prefixLift 560952
  have htrace : WordTrace (prefixWord ++ tailWord_560952) baseStart_560952 baseEnd_560952 := by
    simpa [prefixWord, tailWord_560952, baseEnd_560952] using wordTrace_append hprefix tailTrace_560952
  have hstable : (prefixWord ++ tailWord_560952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560952).length < 2 ^ (prefixWord ++ tailWord_560952).sum := by decide
  have hdescent : baseEnd_560952 < baseStart_560952 := by decide
  rcases family_descends (prefixWord ++ tailWord_560952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561048 : List Nat := [2, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_561048 : Nat := 118140960795 + 561048 * 2 ^ 59
def prefixEnd_561048 : Nat := 4983230072969 + 3 ^ 40 * 561048 * 2
def baseEnd_561048 : Nat := 128038797441700502586575

theorem tailTrace_561048 : CollatzResearch.WordTrace tailWord_561048 prefixEnd_561048 128038797441700502586575 := by
  unfold tailWord_561048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231550835713195107469899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13642067780950926809959865 10231550835713195107469899)
  ·
    refine ⟨15347326253569792661204849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10231550835713195107469899 15347326253569792661204849)
    ·
      refine ⟨11510494690177344495903637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15347326253569792661204849 11510494690177344495903637)
      ·
        refine ⟨539554438602063023245483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11510494690177344495903637 539554438602063023245483)
        ·
          refine ⟨809331657903094534868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539554438602063023245483 809331657903094534868225)
          ·
            refine ⟨606998743427320901151169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809331657903094534868225 606998743427320901151169)
            ·
              refine ⟨455249057570490675863377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606998743427320901151169 455249057570490675863377)
              ·
                refine ⟨341436793177868006897533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455249057570490675863377 341436793177868006897533)
                ·
                  refine ⟨128038797441700502586575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341436793177868006897533 128038797441700502586575)
                  ·
                    rfl

theorem cell21_561048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_561048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561048 prefixEnd_561048 := by exact prefixLift 561048
  have htrace : WordTrace (prefixWord ++ tailWord_561048) baseStart_561048 baseEnd_561048 := by
    simpa [prefixWord, tailWord_561048, baseEnd_561048] using wordTrace_append hprefix tailTrace_561048
  have hstable : (prefixWord ++ tailWord_561048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561048).length < 2 ^ (prefixWord ++ tailWord_561048).sum := by decide
  have hdescent : baseEnd_561048 < baseStart_561048 := by decide
  rcases family_descends (prefixWord ++ tailWord_561048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561076 : List Nat := [2, 5, 2, 1, 2, 1, 3, 5]
def baseStart_561076 : Nat := 118140960795 + 561076 * 2 ^ 59
def prefixEnd_561076 : Nat := 4983230072969 + 3 ^ 40 * 561076 * 2
def baseEnd_561076 : Nat := 42681729141059558706617

theorem tailTrace_561076 : CollatzResearch.WordTrace tailWord_561076 prefixEnd_561076 42681729141059558706617 := by
  unfold tailWord_561076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232061457662475498479541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13642748610216633997972721 10232061457662475498479541)
  ·
    refine ⟨959255761655857077982457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10232061457662475498479541 959255761655857077982457)
    ·
      refine ⟨719441821241892808486843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959255761655857077982457 719441821241892808486843)
      ·
        refine ⟨1079162731862839212730265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719441821241892808486843 1079162731862839212730265)
        ·
          refine ⟨809372048897129409547699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079162731862839212730265 809372048897129409547699)
          ·
            refine ⟨1214058073345694114321549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809372048897129409547699 1214058073345694114321549)
            ·
              refine ⟨455271777504635292870581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1214058073345694114321549 455271777504635292870581)
              ·
                refine ⟨42681729141059558706617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 455271777504635292870581 42681729141059558706617)
                ·
                  rfl

theorem cell21_561076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_561076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561076 prefixEnd_561076 := by exact prefixLift 561076
  have htrace : WordTrace (prefixWord ++ tailWord_561076) baseStart_561076 baseEnd_561076 := by
    simpa [prefixWord, tailWord_561076, baseEnd_561076] using wordTrace_append hprefix tailTrace_561076
  have hstable : (prefixWord ++ tailWord_561076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561076).length < 2 ^ (prefixWord ++ tailWord_561076).sum := by decide
  have hdescent : baseEnd_561076 < baseStart_561076 := by decide
  rcases family_descends (prefixWord ++ tailWord_561076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561149 : List Nat := [1, 4, 1, 1, 1, 2, 5, 3, 3]
def baseStart_561149 : Nat := 118140960795 + 561149 * 2 ^ 59
def prefixEnd_561149 : Nat := 4983230072969 + 3 ^ 40 * 561149 * 2
def baseEnd_561149 : Nat := 128061847017746771403035

theorem tailTrace_561149 : CollatzResearch.WordTrace tailWord_561149 prefixEnd_561149 128061847017746771403035 := by
  unfold tailWord_561149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466785444060484464366501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13644523629373656309577667 20466785444060484464366501)
  ·
    refine ⟨3837522270761340837068719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20466785444060484464366501 3837522270761340837068719)
    ·
      refine ⟨5756283406142011255603079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837522270761340837068719 5756283406142011255603079)
      ·
        refine ⟨8634425109213016883404619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5756283406142011255603079 8634425109213016883404619)
        ·
          refine ⟨12951637663819525325106929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634425109213016883404619 12951637663819525325106929)
          ·
            refine ⟨9713728247864643993830197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12951637663819525325106929 9713728247864643993830197)
            ·
              refine ⟨910662023237310374421581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9713728247864643993830197 910662023237310374421581)
              ·
                refine ⟨341498258713991390408093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 910662023237310374421581 341498258713991390408093)
                ·
                  refine ⟨128061847017746771403035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341498258713991390408093 128061847017746771403035)
                  ·
                    rfl

theorem cell21_561149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_561149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561149 prefixEnd_561149 := by exact prefixLift 561149
  have htrace : WordTrace (prefixWord ++ tailWord_561149) baseStart_561149 baseEnd_561149 := by
    simpa [prefixWord, tailWord_561149, baseEnd_561149] using wordTrace_append hprefix tailTrace_561149
  have hstable : (prefixWord ++ tailWord_561149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561149).length < 2 ^ (prefixWord ++ tailWord_561149).sum := by decide
  have hdescent : baseEnd_561149 < baseStart_561149 := by decide
  rcases family_descends (prefixWord ++ tailWord_561149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561158 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_561158 : Nat := 118140960795 + 561158 * 2 ^ 59
def prefixEnd_561158 : Nat := 4983230072969 + 3 ^ 40 * 561158 * 2
def baseEnd_561158 : Nat := 128063900940364755753017

theorem tailTrace_561158 : CollatzResearch.WordTrace tailWord_561158 prefixEnd_561158 128063900940364755753017 := by
  unfold tailWord_561158
  simp only [CollatzResearch.WordTrace]
  refine ⟨639597303157121218795129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13644742467351919334296085 639597303157121218795129)
  ·
    refine ⟨479697977367840914096347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 639597303157121218795129 479697977367840914096347)
    ·
      refine ⟨719546966051761371144521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479697977367840914096347 719546966051761371144521)
      ·
        refine ⟨539660224538821028358391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 719546966051761371144521 539660224538821028358391)
        ·
          refine ⟨809490336808231542537587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539660224538821028358391 809490336808231542537587)
          ·
            refine ⟨1214235505212347313806381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809490336808231542537587 1214235505212347313806381)
            ·
              refine ⟨455338314454630242677393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1214235505212347313806381 455338314454630242677393)
              ·
                refine ⟨341503735840972682008045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455338314454630242677393 341503735840972682008045)
                ·
                  refine ⟨128063900940364755753017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341503735840972682008045 128063900940364755753017)
                  ·
                    rfl

theorem cell21_561158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_561158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561158 prefixEnd_561158 := by exact prefixLift 561158
  have htrace : WordTrace (prefixWord ++ tailWord_561158) baseStart_561158 baseEnd_561158 := by
    simpa [prefixWord, tailWord_561158, baseEnd_561158] using wordTrace_append hprefix tailTrace_561158
  have hstable : (prefixWord ++ tailWord_561158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561158).length < 2 ^ (prefixWord ++ tailWord_561158).sum := by decide
  have hdescent : baseEnd_561158 < baseStart_561158 := by decide
  rcases family_descends (prefixWord ++ tailWord_561158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561166 : List Nat := [4, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_561166 : Nat := 118140960795 + 561166 * 2 ^ 59
def prefixEnd_561166 : Nat := 4983230072969 + 3 ^ 40 * 561166 * 2
def baseEnd_561166 : Nat := 128065726649358519619667

theorem tailTrace_561166 : CollatzResearch.WordTrace tailWord_561166 prefixEnd_561166 128065726649358519619667 := by
  unfold tailWord_561166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2558425685624862045966919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13644936989999264245156901 2558425685624862045966919)
  ·
    refine ⟨3837638528437293068950379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2558425685624862045966919 3837638528437293068950379)
    ·
      refine ⟨5756457792655939603425569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3837638528437293068950379 5756457792655939603425569)
      ·
        refine ⟨4317343344491954702569177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5756457792655939603425569 4317343344491954702569177)
        ·
          refine ⟨3238007508368966026926883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4317343344491954702569177 3238007508368966026926883)
          ·
            refine ⟨4857011262553449040390325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238007508368966026926883 4857011262553449040390325)
            ·
              refine ⟨455344805864385847536593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4857011262553449040390325 455344805864385847536593)
              ·
                refine ⟨341508604398289385652445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455344805864385847536593 341508604398289385652445)
                ·
                  refine ⟨128065726649358519619667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341508604398289385652445 128065726649358519619667)
                  ·
                    rfl

theorem cell21_561166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_561166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561166 prefixEnd_561166 := by exact prefixLift 561166
  have htrace : WordTrace (prefixWord ++ tailWord_561166) baseStart_561166 baseEnd_561166 := by
    simpa [prefixWord, tailWord_561166, baseEnd_561166] using wordTrace_append hprefix tailTrace_561166
  have hstable : (prefixWord ++ tailWord_561166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561166).length < 2 ^ (prefixWord ++ tailWord_561166).sum := by decide
  have hdescent : baseEnd_561166 < baseStart_561166 := by decide
  rcases family_descends (prefixWord ++ tailWord_561166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561180 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_561180 : Nat := 118140960795 + 561180 * 2 ^ 59
def prefixEnd_561180 : Nat := 4983230072969 + 3 ^ 40 * 561180 * 2
def baseEnd_561180 : Nat := 128068921640097606386305

theorem tailTrace_561180 : CollatzResearch.WordTrace tailWord_561180 prefixEnd_561180 128068921640097606386305 := by
  unfold tailWord_561180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233958053474088379372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13645277404632117839163329 10233958053474088379372497)
  ·
    refine ⟨7675468540105566284529373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10233958053474088379372497 7675468540105566284529373)
    ·
      refine ⟨2878300702539587356698515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7675468540105566284529373 2878300702539587356698515)
      ·
        refine ⟨4317451053809381035047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878300702539587356698515 4317451053809381035047773)
        ·
          refine ⟨1619044145178517888142915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4317451053809381035047773 1619044145178517888142915)
          ·
            refine ⟨2428566217767776832214373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619044145178517888142915 2428566217767776832214373)
            ·
              refine ⟨455356165831458156040195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2428566217767776832214373 455356165831458156040195)
              ·
                refine ⟨683034248747187234060293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455356165831458156040195 683034248747187234060293)
                ·
                  refine ⟨128068921640097606386305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683034248747187234060293 128068921640097606386305)
                  ·
                    rfl

theorem cell21_561180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_561180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561180 prefixEnd_561180 := by exact prefixLift 561180
  have htrace : WordTrace (prefixWord ++ tailWord_561180) baseStart_561180 baseEnd_561180 := by
    simpa [prefixWord, tailWord_561180, baseEnd_561180] using wordTrace_append hprefix tailTrace_561180
  have hstable : (prefixWord ++ tailWord_561180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561180).length < 2 ^ (prefixWord ++ tailWord_561180).sum := by decide
  have hdescent : baseEnd_561180 < baseStart_561180 := by decide
  rcases family_descends (prefixWord ++ tailWord_561180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561284 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_561284 : Nat := 118140960795 + 561284 * 2 ^ 59
def prefixEnd_561284 : Nat := 4983230072969 + 3 ^ 40 * 561284 * 2
def baseEnd_561284 : Nat := 128092655857016536652759

theorem tailTrace_561284 : CollatzResearch.WordTrace tailWord_561284 prefixEnd_561284 128092655857016536652759 := by
  unfold tailWord_561284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235854649285701260265453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13647806199047601680353937 10235854649285701260265453)
  ·
    refine ⟨3838445493482137972599545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10235854649285701260265453 3838445493482137972599545)
    ·
      refine ⟨2878834120111603479449659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3838445493482137972599545 2878834120111603479449659)
      ·
        refine ⟨4318251180167405219174489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2878834120111603479449659 4318251180167405219174489)
        ·
          refine ⟨3238688385125553914380867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4318251180167405219174489 3238688385125553914380867)
          ·
            refine ⟨4858032577688330871571301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238688385125553914380867 4858032577688330871571301)
            ·
              refine ⟨910881108316562038419619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4858032577688330871571301 910881108316562038419619)
              ·
                refine ⟨1366321662474843057629429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910881108316562038419619 1366321662474843057629429)
                ·
                  refine ⟨128092655857016536652759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366321662474843057629429 128092655857016536652759)
                  ·
                    rfl

theorem cell21_561284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_561284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561284 prefixEnd_561284 := by exact prefixLift 561284
  have htrace : WordTrace (prefixWord ++ tailWord_561284) baseStart_561284 baseEnd_561284 := by
    simpa [prefixWord, tailWord_561284, baseEnd_561284] using wordTrace_append hprefix tailTrace_561284
  have hstable : (prefixWord ++ tailWord_561284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561284).length < 2 ^ (prefixWord ++ tailWord_561284).sum := by decide
  have hdescent : baseEnd_561284 < baseStart_561284 := by decide
  rcases family_descends (prefixWord ++ tailWord_561284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561391 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_561391 : Nat := 118140960795 + 561391 * 2 ^ 59
def prefixEnd_561391 : Nat := 4983230072969 + 3 ^ 40 * 561391 * 2
def baseEnd_561391 : Nat := 128117074714808128369207

theorem tailTrace_561391 : CollatzResearch.WordTrace tailWord_561391 prefixEnd_561391 128117074714808128369207 := by
  unfold tailWord_561391
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475611909183759794676027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650407939455839863117351 20475611909183759794676027)
  ·
    refine ⟨30713417863775639692014041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20475611909183759794676027 30713417863775639692014041)
    ·
      refine ⟨23035063397831729769010531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30713417863775639692014041 23035063397831729769010531)
      ·
        refine ⟨34552595096747594653515797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23035063397831729769010531 34552595096747594653515797)
        ·
          refine ⟨1619652895160043499383553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34552595096747594653515797 1619652895160043499383553)
          ·
            refine ⟨1214739671370032624537665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619652895160043499383553 1214739671370032624537665)
            ·
              refine ⟨911054753527524468403249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214739671370032624537665 911054753527524468403249)
              ·
                refine ⟨683291065145643351302437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911054753527524468403249 683291065145643351302437)
                ·
                  refine ⟨128117074714808128369207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683291065145643351302437 128117074714808128369207)
                  ·
                    rfl

theorem cell21_561391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_561391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561391 prefixEnd_561391 := by exact prefixLift 561391
  have htrace : WordTrace (prefixWord ++ tailWord_561391) baseStart_561391 baseEnd_561391 := by
    simpa [prefixWord, tailWord_561391, baseEnd_561391] using wordTrace_append hprefix tailTrace_561391
  have hstable : (prefixWord ++ tailWord_561391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561391).length < 2 ^ (prefixWord ++ tailWord_561391).sum := by decide
  have hdescent : baseEnd_561391 < baseStart_561391 := by decide
  rcases family_descends (prefixWord ++ tailWord_561391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561394 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_561394 : Nat := 118140960795 + 561394 * 2 ^ 59
def prefixEnd_561394 : Nat := 4983230072969 + 3 ^ 40 * 561394 * 2
def baseEnd_561394 : Nat := 128117759355680789819201

theorem tailTrace_561394 : CollatzResearch.WordTrace tailWord_561394 prefixEnd_561394 128117759355680789819201 := by
  unfold tailWord_561394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118930332043222826758809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13650480885448594204690157 5118930332043222826758809)
  ·
    refine ⟨3839197749032417120069107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5118930332043222826758809 3839197749032417120069107)
    ·
      refine ⟨5758796623548625680103661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839197749032417120069107 5758796623548625680103661)
      ·
        refine ⟨2159548733830734630038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5758796623548625680103661 2159548733830734630038873)
        ·
          refine ⟨1619661550373050972529155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159548733830734630038873 1619661550373050972529155)
          ·
            refine ⟨2429492325559576458793733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619661550373050972529155 2429492325559576458793733)
            ·
              refine ⟨455529811042420586023825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2429492325559576458793733 455529811042420586023825)
              ·
                refine ⟨341647358281815439517869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455529811042420586023825 341647358281815439517869)
                ·
                  refine ⟨128117759355680789819201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341647358281815439517869 128117759355680789819201)
                  ·
                    rfl

theorem cell21_561394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_561394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561394 prefixEnd_561394 := by exact prefixLift 561394
  have htrace : WordTrace (prefixWord ++ tailWord_561394) baseStart_561394 baseEnd_561394 := by
    simpa [prefixWord, tailWord_561394, baseEnd_561394] using wordTrace_append hprefix tailTrace_561394
  have hstable : (prefixWord ++ tailWord_561394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561394).length < 2 ^ (prefixWord ++ tailWord_561394).sum := by decide
  have hdescent : baseEnd_561394 < baseStart_561394 := by decide
  rcases family_descends (prefixWord ++ tailWord_561394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561419 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_561419 : Nat := 118140960795 + 561419 * 2 ^ 59
def prefixEnd_561419 : Nat := 4983230072969 + 3 ^ 40 * 561419 * 2
def baseEnd_561419 : Nat := 128123464696286301902483

theorem tailTrace_561419 : CollatzResearch.WordTrace tailWord_561419 prefixEnd_561419 128123464696286301902483 := by
  unfold tailWord_561419
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476633153082320576695311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13651088768721547051130207 20476633153082320576695311)
  ·
    refine ⟨30714949729623480865042967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20476633153082320576695311 30714949729623480865042967)
    ·
      refine ⟨46072424594435221297564451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30714949729623480865042967 46072424594435221297564451)
      ·
        refine ⟨69108636891652831946346677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46072424594435221297564451 69108636891652831946346677)
        ·
          refine ⟨6478934708592452994970001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69108636891652831946346677 6478934708592452994970001)
          ·
            refine ⟨4859201031444339746227501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478934708592452994970001 4859201031444339746227501)
            ·
              refine ⟨1822200386791627404835313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4859201031444339746227501 1822200386791627404835313)
              ·
                refine ⟨1366650290093720553626485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822200386791627404835313 1366650290093720553626485)
                ·
                  refine ⟨128123464696286301902483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366650290093720553626485 128123464696286301902483)
                  ·
                    rfl

theorem cell21_561419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_561419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561419 prefixEnd_561419 := by exact prefixLift 561419
  have htrace : WordTrace (prefixWord ++ tailWord_561419) baseStart_561419 baseEnd_561419 := by
    simpa [prefixWord, tailWord_561419, baseEnd_561419] using wordTrace_append hprefix tailTrace_561419
  have hstable : (prefixWord ++ tailWord_561419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561419).length < 2 ^ (prefixWord ++ tailWord_561419).sum := by decide
  have hdescent : baseEnd_561419 < baseStart_561419 := by decide
  rcases family_descends (prefixWord ++ tailWord_561419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561512 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_561512 : Nat := 118140960795 + 561512 * 2 ^ 59
def prefixEnd_561512 : Nat := 4983230072969 + 3 ^ 40 * 561512 * 2
def baseEnd_561512 : Nat := 128144688563338806852293

theorem tailTrace_561512 : CollatzResearch.WordTrace tailWord_561512 prefixEnd_561512 128144688563338806852293 := by
  unfold tailWord_561512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240012570872698729915395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13653350094496931639887193 10240012570872698729915395)
  ·
    refine ⟨15360018856309048094873093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10240012570872698729915395 15360018856309048094873093)
    ·
      refine ⟨2880003535557946517788705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15360018856309048094873093 2880003535557946517788705)
      ·
        refine ⟨2160002651668459888341529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880003535557946517788705 2160002651668459888341529)
        ·
          refine ⟨1620001988751344916256147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160002651668459888341529 1620001988751344916256147)
          ·
            refine ⟨2430002983127017374384221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620001988751344916256147 2430002983127017374384221)
            ·
              refine ⟨911251118672631515394083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2430002983127017374384221 911251118672631515394083)
              ·
                refine ⟨1366876678008947273091125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911251118672631515394083 1366876678008947273091125)
                ·
                  refine ⟨128144688563338806852293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366876678008947273091125 128144688563338806852293)
                  ·
                    rfl

theorem cell21_561512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_561512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561512 prefixEnd_561512 := by exact prefixLift 561512
  have htrace : WordTrace (prefixWord ++ tailWord_561512) baseStart_561512 baseEnd_561512 := by
    simpa [prefixWord, tailWord_561512, baseEnd_561512] using wordTrace_append hprefix tailTrace_561512
  have hstable : (prefixWord ++ tailWord_561512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561512).length < 2 ^ (prefixWord ++ tailWord_561512).sum := by decide
  have hdescent : baseEnd_561512 < baseStart_561512 := by decide
  rcases family_descends (prefixWord ++ tailWord_561512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561540 : List Nat := [2, 3, 2, 1, 1, 2, 1, 9]
def baseStart_561540 : Nat := 118140960795 + 561540 * 2 ^ 59
def prefixEnd_561540 : Nat := 4983230072969 + 3 ^ 40 * 561540 * 2
def baseEnd_561540 : Nat := 42717026181605660128523

theorem tailTrace_561540 : CollatzResearch.WordTrace tailWord_561540 prefixEnd_561540 42717026181605660128523 := by
  unfold tailWord_561540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240523192821979120925037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13654030923762638827900049 10240523192821979120925037)
  ·
    refine ⟨3840196197308242170346889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10240523192821979120925037 3840196197308242170346889)
    ·
      refine ⟨2880147147981181627760167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3840196197308242170346889 2880147147981181627760167)
      ·
        refine ⟨4320220721971772441640251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880147147981181627760167 4320220721971772441640251)
        ·
          refine ⟨6480331082957658662460377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320220721971772441640251 6480331082957658662460377)
          ·
            refine ⟨4860248312218243996845283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480331082957658662460377 4860248312218243996845283)
            ·
              refine ⟨7290372468327365995267925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860248312218243996845283 7290372468327365995267925)
              ·
                refine ⟨42717026181605660128523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7290372468327365995267925 42717026181605660128523)
                ·
                  rfl

theorem cell21_561540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_561540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561540 prefixEnd_561540 := by exact prefixLift 561540
  have htrace : WordTrace (prefixWord ++ tailWord_561540) baseStart_561540 baseEnd_561540 := by
    simpa [prefixWord, tailWord_561540, baseEnd_561540] using wordTrace_append hprefix tailTrace_561540
  have hstable : (prefixWord ++ tailWord_561540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561540).length < 2 ^ (prefixWord ++ tailWord_561540).sum := by decide
  have hdescent : baseEnd_561540 < baseStart_561540 := by decide
  rcases family_descends (prefixWord ++ tailWord_561540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561661 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_561661 : Nat := 118140960795 + 561661 * 2 ^ 59
def prefixEnd_561661 : Nat := 4983230072969 + 3 ^ 40 * 561661 * 2
def baseEnd_561661 : Nat := 128178692393347658868655

theorem tailTrace_561661 : CollatzResearch.WordTrace tailWord_561661 prefixEnd_561661 128178692393347658868655 := by
  unfold tailWord_561661
  simp only [CollatzResearch.WordTrace]
  refine ⟨20485459618205595907004837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13656973078803730604669891 20485459618205595907004837)
  ·
    refine ⟨3841023678413549232563407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20485459618205595907004837 3841023678413549232563407)
    ·
      refine ⟨5761535517620323848845111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841023678413549232563407 5761535517620323848845111)
      ·
        refine ⟨8642303276430485773267667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761535517620323848845111 8642303276430485773267667)
        ·
          refine ⟨12963454914645728659901501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642303276430485773267667 12963454914645728659901501)
          ·
            refine ⟨4861295592992148247463063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12963454914645728659901501 4861295592992148247463063)
            ·
              refine ⟨7291943389488222371194595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861295592992148247463063 7291943389488222371194595)
              ·
                refine ⟨10937915084232333556791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7291943389488222371194595 10937915084232333556791893)
                ·
                  refine ⟨128178692393347658868655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10937915084232333556791893 128178692393347658868655)
                  ·
                    rfl

theorem cell21_561661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_561661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561661 prefixEnd_561661 := by exact prefixLift 561661
  have htrace : WordTrace (prefixWord ++ tailWord_561661) baseStart_561661 baseEnd_561661 := by
    simpa [prefixWord, tailWord_561661, baseEnd_561661] using wordTrace_append hprefix tailTrace_561661
  have hstable : (prefixWord ++ tailWord_561661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561661).length < 2 ^ (prefixWord ++ tailWord_561661).sum := by decide
  have hdescent : baseEnd_561661 < baseStart_561661 := by decide
  rcases family_descends (prefixWord ++ tailWord_561661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561678 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_561678 : Nat := 118140960795 + 561678 * 2 ^ 59
def prefixEnd_561678 : Nat := 4983230072969 + 3 ^ 40 * 561678 * 2
def baseEnd_561678 : Nat := 128182572024959407085287

theorem tailTrace_561678 : CollatzResearch.WordTrace tailWord_561678 prefixEnd_561678 128182572024959407085287 := by
  unfold tailWord_561678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560759957393000976296711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13657386439429338540249125 2560759957393000976296711)
  ·
    refine ⟨3841139936089501464445067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560759957393000976296711 3841139936089501464445067)
    ·
      refine ⟨5761709904134252196667601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841139936089501464445067 5761709904134252196667601)
      ·
        refine ⟨4321282428100689147500701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761709904134252196667601 4321282428100689147500701)
        ·
          refine ⟨1620480910537758430312763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4321282428100689147500701 1620480910537758430312763)
          ·
            refine ⟨2430721365806637645469145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620480910537758430312763 2430721365806637645469145)
            ·
              refine ⟨1823041024354978234101859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430721365806637645469145 1823041024354978234101859)
              ·
                refine ⟨2734561536532467351152789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823041024354978234101859 2734561536532467351152789)
                ·
                  refine ⟨128182572024959407085287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2734561536532467351152789 128182572024959407085287)
                  ·
                    rfl

theorem cell21_561678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_561678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561678 prefixEnd_561678 := by exact prefixLift 561678
  have htrace : WordTrace (prefixWord ++ tailWord_561678) baseStart_561678 baseEnd_561678 := by
    simpa [prefixWord, tailWord_561678, baseEnd_561678] using wordTrace_append hprefix tailTrace_561678
  have hstable : (prefixWord ++ tailWord_561678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561678).length < 2 ^ (prefixWord ++ tailWord_561678).sum := by decide
  have hdescent : baseEnd_561678 < baseStart_561678 := by decide
  rcases family_descends (prefixWord ++ tailWord_561678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561692 : List Nat := [2, 2, 3, 1, 2, 2, 1, 8]
def baseStart_561692 : Nat := 118140960795 + 561692 * 2 ^ 59
def prefixEnd_561692 : Nat := 4983230072969 + 3 ^ 40 * 561692 * 2
def baseEnd_561692 : Nat := 42728589005232831283975

theorem tailTrace_561692 : CollatzResearch.WordTrace tailWord_561692 prefixEnd_561692 42728589005232831283975 := by
  unfold tailWord_561692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243295140546644100691665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13657726854062192134255553 10243295140546644100691665)
  ·
    refine ⟨7682471355409983075518749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10243295140546644100691665 7682471355409983075518749)
    ·
      refine ⟨2880926758278743653319531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7682471355409983075518749 2880926758278743653319531)
      ·
        refine ⟨4321390137418115479979297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880926758278743653319531 4321390137418115479979297)
        ·
          refine ⟨3241042603063586609984473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321390137418115479979297 3241042603063586609984473)
          ·
            refine ⟨2430781952297689957488355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241042603063586609984473 2430781952297689957488355)
            ·
              refine ⟨3646172928446534936232533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430781952297689957488355 3646172928446534936232533)
              ·
                refine ⟨42728589005232831283975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3646172928446534936232533 42728589005232831283975)
                ·
                  rfl

theorem cell21_561692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_561692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561692 prefixEnd_561692 := by exact prefixLift 561692
  have htrace : WordTrace (prefixWord ++ tailWord_561692) baseStart_561692 baseEnd_561692 := by
    simpa [prefixWord, tailWord_561692, baseEnd_561692] using wordTrace_append hprefix tailTrace_561692
  have hstable : (prefixWord ++ tailWord_561692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561692).length < 2 ^ (prefixWord ++ tailWord_561692).sum := by decide
  have hdescent : baseEnd_561692 < baseStart_561692 := by decide
  rcases family_descends (prefixWord ++ tailWord_561692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561726 : List Nat := [4, 2, 1, 4, 2, 8]
def baseStart_561726 : Nat := 118140960795 + 561726 * 2 ^ 59
def prefixEnd_561726 : Nat := 4983230072969 + 3 ^ 40 * 561726 * 2
def baseEnd_561726 : Nat := 4747908380700814455007

theorem tailTrace_561726 : CollatzResearch.WordTrace tailWord_561726 prefixEnd_561726 4747908380700814455007 := by
  unfold tailWord_561726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560978795371264001015129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13658553575313408005414021 2560978795371264001015129)
  ·
    refine ⟨1920734096528448000761347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560978795371264001015129 1920734096528448000761347)
    ·
      refine ⟨2881101144792672001142021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920734096528448000761347 2881101144792672001142021)
      ·
        refine ⟨540206464648626000214129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2881101144792672001142021 540206464648626000214129)
        ·
          refine ⟨405154848486469500160597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540206464648626000214129 405154848486469500160597)
          ·
            refine ⟨4747908380700814455007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 405154848486469500160597 4747908380700814455007)
            ·
              rfl

theorem cell21_561726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 8].length) (baseStart_561726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561726 prefixEnd_561726 := by exact prefixLift 561726
  have htrace : WordTrace (prefixWord ++ tailWord_561726) baseStart_561726 baseEnd_561726 := by
    simpa [prefixWord, tailWord_561726, baseEnd_561726] using wordTrace_append hprefix tailTrace_561726
  have hstable : (prefixWord ++ tailWord_561726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561726).length < 2 ^ (prefixWord ++ tailWord_561726).sum := by decide
  have hdescent : baseEnd_561726 < baseStart_561726 := by decide
  rcases family_descends (prefixWord ++ tailWord_561726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561740 : List Nat := [2, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_561740 : Nat := 118140960795 + 561740 * 2 ^ 59
def prefixEnd_561740 : Nat := 4983230072969 + 3 ^ 40 * 561740 * 2
def baseEnd_561740 : Nat := 128196721269661077051827

theorem tailTrace_561740 : CollatzResearch.WordTrace tailWord_561740 prefixEnd_561740 128196721269661077051827 := by
  unfold tailWord_561740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10244170492459696199565337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13658893989946261599420449 10244170492459696199565337)
  ·
    refine ⟨7683127869344772149674003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10244170492459696199565337 7683127869344772149674003)
    ·
      refine ⟨11524691804017158224511005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7683127869344772149674003 11524691804017158224511005)
      ·
        refine ⟨4321759426506434334191627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11524691804017158224511005 4321759426506434334191627)
        ·
          refine ⟨6482639139759651501287441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321759426506434334191627 6482639139759651501287441)
          ·
            refine ⟨4861979354819738625965581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6482639139759651501287441 4861979354819738625965581)
            ·
              refine ⟨1823242258057401984737093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4861979354819738625965581 1823242258057401984737093)
              ·
                refine ⟨341857923385762872138205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1823242258057401984737093 341857923385762872138205)
                ·
                  refine ⟨128196721269661077051827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341857923385762872138205 128196721269661077051827)
                  ·
                    rfl

theorem cell21_561740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_561740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561740 prefixEnd_561740 := by exact prefixLift 561740
  have htrace : WordTrace (prefixWord ++ tailWord_561740) baseStart_561740 baseEnd_561740 := by
    simpa [prefixWord, tailWord_561740, baseEnd_561740] using wordTrace_append hprefix tailTrace_561740
  have hstable : (prefixWord ++ tailWord_561740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561740).length < 2 ^ (prefixWord ++ tailWord_561740).sum := by decide
  have hdescent : baseEnd_561740 < baseStart_561740 := by decide
  rcases family_descends (prefixWord ++ tailWord_561740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561799 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_561799 : Nat := 118140960795 + 561799 * 2 ^ 59
def prefixEnd_561799 : Nat := 4983230072969 + 3 ^ 40 * 561799 * 2
def baseEnd_561799 : Nat := 128210185873490085568373

theorem tailTrace_561799 : CollatzResearch.WordTrace tailWord_561799 prefixEnd_561799 128210185873490085568373 := by
  unfold tailWord_561799
  simp only [CollatzResearch.WordTrace]
  refine ⟨20490492891705645475528451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13660328594470430317018967 20490492891705645475528451)
  ·
    refine ⟨30735739337558468213292677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20490492891705645475528451 30735739337558468213292677)
    ·
      refine ⟨5762951125792212789992377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30735739337558468213292677 5762951125792212789992377)
      ·
        refine ⟨4322213344344159592494283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762951125792212789992377 4322213344344159592494283)
        ·
          refine ⟨6483320016516239388741425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322213344344159592494283 6483320016516239388741425)
          ·
            refine ⟨4862490012387179541556069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6483320016516239388741425 4862490012387179541556069)
            ·
              refine ⟨911716877322596164041763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4862490012387179541556069 911716877322596164041763)
              ·
                refine ⟨1367575315983894246062645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911716877322596164041763 1367575315983894246062645)
                ·
                  refine ⟨128210185873490085568373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367575315983894246062645 128210185873490085568373)
                  ·
                    rfl

theorem cell21_561799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_561799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561799 prefixEnd_561799 := by exact prefixLift 561799
  have htrace : WordTrace (prefixWord ++ tailWord_561799) baseStart_561799 baseEnd_561799 := by
    simpa [prefixWord, tailWord_561799, baseEnd_561799] using wordTrace_append hprefix tailTrace_561799
  have hstable : (prefixWord ++ tailWord_561799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561799).length < 2 ^ (prefixWord ++ tailWord_561799).sum := by decide
  have hdescent : baseEnd_561799 < baseStart_561799 := by decide
  rcases family_descends (prefixWord ++ tailWord_561799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561903 : List Nat := [1, 1, 2, 1, 5, 11]
def baseStart_561903 : Nat := 118140960795 + 561903 * 2 ^ 59
def prefixEnd_561903 : Nat := 4983230072969 + 3 ^ 40 * 561903 * 2
def baseEnd_561903 : Nat := 4749404447792926512401

theorem tailTrace_561903 : CollatzResearch.WordTrace tailWord_561903 prefixEnd_561903 4749404447792926512401 := by
  unfold tailWord_561903
  simp only [CollatzResearch.WordTrace]
  refine ⟨20494286083328871237314363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13662857388885914158209575 20494286083328871237314363)
  ·
    refine ⟨30741429124993306855971545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20494286083328871237314363 30741429124993306855971545)
    ·
      refine ⟨23056071843744980141978659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30741429124993306855971545 23056071843744980141978659)
      ·
        refine ⟨34584107765617470212967989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23056071843744980141978659 34584107765617470212967989)
        ·
          refine ⟨3242260103026637832465749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34584107765617470212967989 3242260103026637832465749)
          ·
            refine ⟨4749404447792926512401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3242260103026637832465749 4749404447792926512401)
            ·
              rfl

theorem cell21_561903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 11].length) (baseStart_561903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561903 prefixEnd_561903 := by exact prefixLift 561903
  have htrace : WordTrace (prefixWord ++ tailWord_561903) baseStart_561903 baseEnd_561903 := by
    simpa [prefixWord, tailWord_561903, baseEnd_561903] using wordTrace_append hprefix tailTrace_561903
  have hstable : (prefixWord ++ tailWord_561903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561903).length < 2 ^ (prefixWord ++ tailWord_561903).sum := by decide
  have hdescent : baseEnd_561903 < baseStart_561903 := by decide
  rcases family_descends (prefixWord ++ tailWord_561903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561906 : List Nat := [3, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_561906 : Nat := 118140960795 + 561906 * 2 ^ 59
def prefixEnd_561906 : Nat := 4983230072969 + 3 ^ 40 * 561906 * 2
def baseEnd_561906 : Nat := 128234604731281677284821

theorem tailTrace_561906 : CollatzResearch.WordTrace tailWord_561906 prefixEnd_561906 128234604731281677284821 := by
  unfold tailWord_561906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123598875579500687418393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13662930334878668499782381 5123598875579500687418393)
  ·
    refine ⟨3842699156684625515563795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5123598875579500687418393 3842699156684625515563795)
    ·
      refine ⟨5764048735026938273345693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842699156684625515563795 5764048735026938273345693)
      ·
        refine ⟨2161518275635101852504635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5764048735026938273345693 2161518275635101852504635)
        ·
          refine ⟨3242277413452652778756953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161518275635101852504635 3242277413452652778756953)
          ·
            refine ⟨2431708060089489584067715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242277413452652778756953 2431708060089489584067715)
            ·
              refine ⟨3647562090134234376101573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431708060089489584067715 3647562090134234376101573)
              ·
                refine ⟨683917891900168945519045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3647562090134234376101573 683917891900168945519045)
                ·
                  refine ⟨128234604731281677284821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683917891900168945519045 128234604731281677284821)
                  ·
                    rfl

theorem cell21_561906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_561906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561906 prefixEnd_561906 := by exact prefixLift 561906
  have htrace : WordTrace (prefixWord ++ tailWord_561906) baseStart_561906 baseEnd_561906 := by
    simpa [prefixWord, tailWord_561906, baseEnd_561906] using wordTrace_append hprefix tailTrace_561906
  have hstable : (prefixWord ++ tailWord_561906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561906).length < 2 ^ (prefixWord ++ tailWord_561906).sum := by decide
  have hdescent : baseEnd_561906 < baseStart_561906 := by decide
  rcases family_descends (prefixWord ++ tailWord_561906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561988 : List Nat := [2, 3, 4, 2, 2, 1, 2, 5]
def baseStart_561988 : Nat := 118140960795 + 561988 * 2 ^ 59
def prefixEnd_561988 : Nat := 4983230072969 + 3 ^ 40 * 561988 * 2
def baseEnd_561988 : Nat := 42751106082822585639329

theorem tailTrace_561988 : CollatzResearch.WordTrace tailWord_561988 prefixEnd_561988 42751106082822585639329 := by
  unfold tailWord_561988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10248693144010465377079309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13664924192013953836105745 10248693144010465377079309)
  ·
    refine ⟨3843259929003924516404741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10248693144010465377079309 3843259929003924516404741)
    ·
      refine ⟨720611236688235846825889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3843259929003924516404741 720611236688235846825889)
      ·
        refine ⟨540458427516176885119417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720611236688235846825889 540458427516176885119417)
        ·
          refine ⟨405343820637132663839563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540458427516176885119417 405343820637132663839563)
          ·
            refine ⟨608015730955698995759345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405343820637132663839563 608015730955698995759345)
            ·
              refine ⟨456011798216774246819509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608015730955698995759345 456011798216774246819509)
              ·
                refine ⟨42751106082822585639329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456011798216774246819509 42751106082822585639329)
                ·
                  rfl

theorem cell21_561988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_561988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561988 prefixEnd_561988 := by exact prefixLift 561988
  have htrace : WordTrace (prefixWord ++ tailWord_561988) baseStart_561988 baseEnd_561988 := by
    simpa [prefixWord, tailWord_561988, baseEnd_561988] using wordTrace_append hprefix tailTrace_561988
  have hstable : (prefixWord ++ tailWord_561988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561988).length < 2 ^ (prefixWord ++ tailWord_561988).sum := by decide
  have hdescent : baseEnd_561988 < baseStart_561988 := by decide
  rcases family_descends (prefixWord ++ tailWord_561988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561996 : List Nat := [2, 2, 1, 3, 3, 2, 1, 7]
def baseStart_561996 : Nat := 118140960795 + 561996 * 2 ^ 59
def prefixEnd_561996 : Nat := 4983230072969 + 3 ^ 40 * 561996 * 2
def baseEnd_561996 : Nat := 42751714652487173594879

theorem tailTrace_561996 : CollatzResearch.WordTrace tailWord_561996 prefixEnd_561996 42751714652487173594879 := by
  unfold tailWord_561996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10248839035995974060224921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13665118714661298746966561 10248839035995974060224921)
  ·
    refine ⟨7686629276996980545168691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10248839035995974060224921 7686629276996980545168691)
    ·
      refine ⟨11529943915495470817753037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7686629276996980545168691 11529943915495470817753037)
      ·
        refine ⟨4323728968310801556657389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11529943915495470817753037 4323728968310801556657389)
        ·
          refine ⟨1621398363116550583746521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4323728968310801556657389 1621398363116550583746521)
          ·
            refine ⟨1216048772337412937809891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621398363116550583746521 1216048772337412937809891)
            ·
              refine ⟨1824073158506119406714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216048772337412937809891 1824073158506119406714837)
              ·
                refine ⟨42751714652487173594879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1824073158506119406714837 42751714652487173594879)
                ·
                  rfl

theorem cell21_561996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_561996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_561996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_561996 prefixEnd_561996 := by exact prefixLift 561996
  have htrace : WordTrace (prefixWord ++ tailWord_561996) baseStart_561996 baseEnd_561996 := by
    simpa [prefixWord, tailWord_561996, baseEnd_561996] using wordTrace_append hprefix tailTrace_561996
  have hstable : (prefixWord ++ tailWord_561996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561996).length < 2 ^ (prefixWord ++ tailWord_561996).sum := by decide
  have hdescent : baseEnd_561996 < baseStart_561996 := by decide
  rcases family_descends (prefixWord ++ tailWord_561996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562027 : List Nat := [1, 1, 1, 1, 2, 2, 4, 6, 3]
def baseStart_562027 : Nat := 118140960795 + 562027 * 2 ^ 59
def prefixEnd_562027 : Nat := 4983230072969 + 3 ^ 40 * 562027 * 2
def baseEnd_562027 : Nat := 128262218579812355767907

theorem tailTrace_562027 : CollatzResearch.WordTrace tailWord_562027 prefixEnd_562027 128262218579812355767907 := by
  unfold tailWord_562027
  simp only [CollatzResearch.WordTrace]
  refine ⟨20498808734879640414828335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13665872489919760276552223 20498808734879640414828335)
  ·
    refine ⟨30748213102319460622242503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20498808734879640414828335 30748213102319460622242503)
    ·
      refine ⟨46122319653479190933363755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30748213102319460622242503 46122319653479190933363755)
      ·
        refine ⟨69183479480218786400045633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46122319653479190933363755 69183479480218786400045633)
        ·
          refine ⟨51887609610164089800034225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69183479480218786400045633 51887609610164089800034225)
          ·
            refine ⟨38915707207623067350025669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51887609610164089800034225 38915707207623067350025669)
            ·
              refine ⟨7296695101429325128129813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38915707207623067350025669 7296695101429325128129813)
              ·
                refine ⟨342032582879499615381085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7296695101429325128129813 342032582879499615381085)
                ·
                  refine ⟨128262218579812355767907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342032582879499615381085 128262218579812355767907)
                  ·
                    rfl

theorem cell21_562027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 3].length) (baseStart_562027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562027 prefixEnd_562027 := by exact prefixLift 562027
  have htrace : WordTrace (prefixWord ++ tailWord_562027) baseStart_562027 baseEnd_562027 := by
    simpa [prefixWord, tailWord_562027, baseEnd_562027] using wordTrace_append hprefix tailTrace_562027
  have hstable : (prefixWord ++ tailWord_562027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562027).length < 2 ^ (prefixWord ++ tailWord_562027).sum := by decide
  have hdescent : baseEnd_562027 < baseStart_562027 := by decide
  rcases family_descends (prefixWord ++ tailWord_562027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562151 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 4]
def baseStart_562151 : Nat := 118140960795 + 562151 * 2 ^ 59
def prefixEnd_562151 : Nat := 4983230072969 + 3 ^ 40 * 562151 * 2
def baseEnd_562151 : Nat := 128290517069215695700987

theorem tailTrace_562151 : CollatzResearch.WordTrace tailWord_562151 prefixEnd_562151 128290517069215695700987 := by
  unfold tailWord_562151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20503331386430409592342307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13668887590953606394894871 20503331386430409592342307)
  ·
    refine ⟨30754997079645614388513461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20503331386430409592342307 30754997079645614388513461)
    ·
      refine ⟨2883280976216776348923137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30754997079645614388513461 2883280976216776348923137)
      ·
        refine ⟨2162460732162582261692353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883280976216776348923137 2162460732162582261692353)
        ·
          refine ⟨1621845549121936696269265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162460732162582261692353 1621845549121936696269265)
          ·
            refine ⟨1216384161841452522201949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1621845549121936696269265 1216384161841452522201949)
            ·
              refine ⟨456144060690544695825731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216384161841452522201949 456144060690544695825731)
              ·
                refine ⟨684216091035817043738597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456144060690544695825731 684216091035817043738597)
                ·
                  refine ⟨128290517069215695700987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684216091035817043738597 128290517069215695700987)
                  ·
                    rfl

theorem cell21_562151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_562151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562151 prefixEnd_562151 := by exact prefixLift 562151
  have htrace : WordTrace (prefixWord ++ tailWord_562151) baseStart_562151 baseEnd_562151 := by
    simpa [prefixWord, tailWord_562151, baseEnd_562151] using wordTrace_append hprefix tailTrace_562151
  have hstable : (prefixWord ++ tailWord_562151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562151).length < 2 ^ (prefixWord ++ tailWord_562151).sum := by decide
  have hdescent : baseEnd_562151 < baseStart_562151 := by decide
  rcases family_descends (prefixWord ++ tailWord_562151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562207 : List Nat := [1, 1, 2, 4, 1, 3, 1, 8]
def baseStart_562207 : Nat := 118140960795 + 562207 * 2 ^ 59
def prefixEnd_562207 : Nat := 4983230072969 + 3 ^ 40 * 562207 * 2
def baseEnd_562207 : Nat := 42767765677390680922513

theorem tailTrace_562207 : CollatzResearch.WordTrace tailWord_562207 prefixEnd_562207 42767765677390680922513 := by
  unfold tailWord_562207
  simp only [CollatzResearch.WordTrace]
  refine ⟨20505373874227531156380875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13670249249485020770920583 20505373874227531156380875)
  ·
    refine ⟨30758060811341296734571313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20505373874227531156380875 30758060811341296734571313)
    ·
      refine ⟨23068545608505972550928485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30758060811341296734571313 23068545608505972550928485)
      ·
        refine ⟨4325352301594869853299091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23068545608505972550928485 4325352301594869853299091)
        ·
          refine ⟨6488028452392304779948637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325352301594869853299091 6488028452392304779948637)
          ·
            refine ⟨2433010669647114292480739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6488028452392304779948637 2433010669647114292480739)
            ·
              refine ⟨3649516004470671438721109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433010669647114292480739 3649516004470671438721109)
              ·
                refine ⟨42767765677390680922513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3649516004470671438721109 42767765677390680922513)
                ·
                  rfl

theorem cell21_562207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_562207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562207 prefixEnd_562207 := by exact prefixLift 562207
  have htrace : WordTrace (prefixWord ++ tailWord_562207) baseStart_562207 baseEnd_562207 := by
    simpa [prefixWord, tailWord_562207, baseEnd_562207] using wordTrace_append hprefix tailTrace_562207
  have hstable : (prefixWord ++ tailWord_562207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562207).length < 2 ^ (prefixWord ++ tailWord_562207).sum := by decide
  have hdescent : baseEnd_562207 < baseStart_562207 := by decide
  rcases family_descends (prefixWord ++ tailWord_562207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562210 : List Nat := [3, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_562210 : Nat := 118140960795 + 562210 * 2 ^ 59
def prefixEnd_562210 : Nat := 4983230072969 + 3 ^ 40 * 562210 * 2
def baseEnd_562210 : Nat := 128303981673044704217533

theorem tailTrace_562210 : CollatzResearch.WordTrace tailWord_562210 prefixEnd_562210 128303981673044704217533 := by
  unfold tailWord_562210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126370823304165667185021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13670322195477775112493389 5126370823304165667185021)
  ·
    refine ⟨1922389058739062125194383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5126370823304165667185021 1922389058739062125194383)
    ·
      refine ⟨2883583588108593187791575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922389058739062125194383 2883583588108593187791575)
      ·
        refine ⟨4325375382162889781687363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883583588108593187791575 4325375382162889781687363)
        ·
          refine ⟨6488063073244334672531045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325375382162889781687363 6488063073244334672531045)
          ·
            refine ⟨1216511826233312751099571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6488063073244334672531045 1216511826233312751099571)
            ·
              refine ⟨1824767739349969126649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216511826233312751099571 1824767739349969126649357)
              ·
                refine ⟨684287902256238422493509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1824767739349969126649357 684287902256238422493509)
                ·
                  refine ⟨128303981673044704217533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684287902256238422493509 128303981673044704217533)
                  ·
                    rfl

theorem cell21_562210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_562210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562210 prefixEnd_562210 := by exact prefixLift 562210
  have htrace : WordTrace (prefixWord ++ tailWord_562210) baseStart_562210 baseEnd_562210 := by
    simpa [prefixWord, tailWord_562210, baseEnd_562210] using wordTrace_append hprefix tailTrace_562210
  have hstable : (prefixWord ++ tailWord_562210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562210).length < 2 ^ (prefixWord ++ tailWord_562210).sum := by decide
  have hdescent : baseEnd_562210 < baseStart_562210 := by decide
  rcases family_descends (prefixWord ++ tailWord_562210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562334 : List Nat := [4, 3, 1, 1, 2, 3, 2, 5]
def baseStart_562334 : Nat := 118140960795 + 562334 * 2 ^ 59
def prefixEnd_562334 : Nat := 4983230072969 + 3 ^ 40 * 562334 * 2
def baseEnd_562334 : Nat := 42777426720816014716871

theorem tailTrace_562334 : CollatzResearch.WordTrace tailWord_562334 prefixEnd_562334 42777426720816014716871 := by
  unfold tailWord_562334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563750743095928980781757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13673337296511621230836037 2563750743095928980781757)
  ·
    refine ⟨961406528660973367793159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2563750743095928980781757 961406528660973367793159)
    ·
      refine ⟨1442109792991460051689739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961406528660973367793159 1442109792991460051689739)
      ·
        refine ⟨2163164689487190077534609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442109792991460051689739 2163164689487190077534609)
        ·
          refine ⟨1622373517115392558150957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2163164689487190077534609 1622373517115392558150957)
          ·
            refine ⟨608390068918272209306609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1622373517115392558150957 608390068918272209306609)
            ·
              refine ⟨456292551688704156979957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608390068918272209306609 456292551688704156979957)
              ·
                refine ⟨42777426720816014716871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456292551688704156979957 42777426720816014716871)
                ·
                  rfl

theorem cell21_562334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_562334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562334 prefixEnd_562334 := by exact prefixLift 562334
  have htrace : WordTrace (prefixWord ++ tailWord_562334) baseStart_562334 baseEnd_562334 := by
    simpa [prefixWord, tailWord_562334, baseEnd_562334] using wordTrace_append hprefix tailTrace_562334
  have hstable : (prefixWord ++ tailWord_562334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562334).length < 2 ^ (prefixWord ++ tailWord_562334).sum := by decide
  have hdescent : baseEnd_562334 < baseStart_562334 := by decide
  rcases family_descends (prefixWord ++ tailWord_562334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562404 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_562404 : Nat := 118140960795 + 562404 * 2 ^ 59
def prefixEnd_562404 : Nat := 4983230072969 + 3 ^ 40 * 562404 * 2
def baseEnd_562404 : Nat := 128348255116143477983803

theorem tailTrace_562404 : CollatzResearch.WordTrace tailWord_562404 prefixEnd_562404 128348255116143477983803 := by
  unfold tailWord_562404
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256279527256916900651133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13675039369675889200868177 10256279527256916900651133)
  ·
    refine ⟨3846104822721343837744175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10256279527256916900651133 3846104822721343837744175)
    ·
      refine ⟨5769157234082015756616263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3846104822721343837744175 5769157234082015756616263)
      ·
        refine ⟨8653735851123023634924395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769157234082015756616263 8653735851123023634924395)
        ·
          refine ⟨12980603776684535452386593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8653735851123023634924395 12980603776684535452386593)
          ·
            refine ⟨9735452832513401589289945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12980603776684535452386593 9735452832513401589289945)
            ·
              refine ⟨7301589624385051191967459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735452832513401589289945 7301589624385051191967459)
              ·
                refine ⟨10952384436577576787951189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7301589624385051191967459 10952384436577576787951189)
                ·
                  refine ⟨128348255116143477983803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10952384436577576787951189 128348255116143477983803)
                  ·
                    rfl

theorem cell21_562404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_562404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562404 prefixEnd_562404 := by exact prefixLift 562404
  have htrace : WordTrace (prefixWord ++ tailWord_562404) baseStart_562404 baseEnd_562404 := by
    simpa [prefixWord, tailWord_562404, baseEnd_562404] using wordTrace_append hprefix tailTrace_562404
  have hstable : (prefixWord ++ tailWord_562404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562404).length < 2 ^ (prefixWord ++ tailWord_562404).sum := by decide
  have hdescent : baseEnd_562404 < baseStart_562404 := by decide
  rcases family_descends (prefixWord ++ tailWord_562404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562435 : List Nat := [1, 1, 1, 3, 2, 4, 3, 6]
def baseStart_562435 : Nat := 118140960795 + 562435 * 2 ^ 59
def prefixEnd_562435 : Nat := 4983230072969 + 3 ^ 40 * 562435 * 2
def baseEnd_562435 : Nat := 42785109912831437655691

theorem tailTrace_562435 : CollatzResearch.WordTrace tailWord_562435 prefixEnd_562435 42785109912831437655691 := by
  unfold tailWord_562435
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513689717401526095680759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13675793144934350730453839 20513689717401526095680759)
  ·
    refine ⟨30770534576102289143521139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20513689717401526095680759 30770534576102289143521139)
    ·
      refine ⟨46155801864153433715281709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30770534576102289143521139 46155801864153433715281709)
      ·
        refine ⟨17308425699057537643230641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46155801864153433715281709 17308425699057537643230641)
        ·
          refine ⟨12981319274293153232422981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17308425699057537643230641 12981319274293153232422981)
          ·
            refine ⟨2433997363929966231079309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12981319274293153232422981 2433997363929966231079309)
            ·
              refine ⟨912749011473737336654741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2433997363929966231079309 912749011473737336654741)
              ·
                refine ⟨42785109912831437655691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 912749011473737336654741 42785109912831437655691)
                ·
                  rfl

theorem cell21_562435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_562435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562435 prefixEnd_562435 := by exact prefixLift 562435
  have htrace : WordTrace (prefixWord ++ tailWord_562435) baseStart_562435 baseEnd_562435 := by
    simpa [prefixWord, tailWord_562435, baseEnd_562435] using wordTrace_append hprefix tailTrace_562435
  have hstable : (prefixWord ++ tailWord_562435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562435).length < 2 ^ (prefixWord ++ tailWord_562435).sum := by decide
  have hdescent : baseEnd_562435 < baseStart_562435 := by decide
  rcases family_descends (prefixWord ++ tailWord_562435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562480 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_562480 : Nat := 118140960795 + 562480 * 2 ^ 59
def prefixEnd_562480 : Nat := 4983230072969 + 3 ^ 40 * 562480 * 2
def baseEnd_562480 : Nat := 128365599351584234716981

theorem tailTrace_562480 : CollatzResearch.WordTrace tailWord_562480 prefixEnd_562480 128365599351584234716981 := by
  unfold tailWord_562480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257665501119249390534447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13676887334825665854045929 10257665501119249390534447)
  ·
    refine ⟨15386498251678874085801671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10257665501119249390534447 15386498251678874085801671)
    ·
      refine ⟨23079747377518311128702507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15386498251678874085801671 23079747377518311128702507)
      ·
        refine ⟨34619621066277466693053761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23079747377518311128702507 34619621066277466693053761)
        ·
          refine ⟨25964715799708100019790321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34619621066277466693053761 25964715799708100019790321)
          ·
            refine ⟨19473536849781075014842741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25964715799708100019790321 19473536849781075014842741)
            ·
              refine ⟨1825644079666975782641507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19473536849781075014842741 1825644079666975782641507)
              ·
                refine ⟨2738466119500463673962261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825644079666975782641507 2738466119500463673962261)
                ·
                  refine ⟨128365599351584234716981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2738466119500463673962261 128365599351584234716981)
                  ·
                    rfl

theorem cell21_562480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_562480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562480 prefixEnd_562480 := by exact prefixLift 562480
  have htrace : WordTrace (prefixWord ++ tailWord_562480) baseStart_562480 baseEnd_562480 := by
    simpa [prefixWord, tailWord_562480, baseEnd_562480] using wordTrace_append hprefix tailTrace_562480
  have hstable : (prefixWord ++ tailWord_562480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562480).length < 2 ^ (prefixWord ++ tailWord_562480).sum := by decide
  have hdescent : baseEnd_562480 < baseStart_562480 := by decide
  rcases family_descends (prefixWord ++ tailWord_562480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562483 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 3]
def baseStart_562483 : Nat := 118140960795 + 562483 * 2 ^ 59
def prefixEnd_562483 : Nat := 4983230072969 + 3 ^ 40 * 562483 * 2
def baseEnd_562483 : Nat := 128366283992456896166975

theorem tailTrace_562483 : CollatzResearch.WordTrace tailWord_562483 prefixEnd_562483 128366283992456896166975 := by
  unfold tailWord_562483
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515440421227630293428103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13676960280818420195618735 20515440421227630293428103)
  ·
    refine ⟨30773160631841445440142155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20515440421227630293428103 30773160631841445440142155)
    ·
      refine ⟨46159740947762168160213233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30773160631841445440142155 46159740947762168160213233)
      ·
        refine ⟨34619805710821626120159925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46159740947762168160213233 34619805710821626120159925)
        ·
          refine ⟨3245606785389527448764993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34619805710821626120159925 3245606785389527448764993)
          ·
            refine ⟨2434205089042145586573745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245606785389527448764993 2434205089042145586573745)
            ·
              refine ⟨1825653816781609189930309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2434205089042145586573745 1825653816781609189930309)
              ·
                refine ⟨342310090646551723111933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1825653816781609189930309 342310090646551723111933)
                ·
                  refine ⟨128366283992456896166975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342310090646551723111933 128366283992456896166975)
                  ·
                    rfl

theorem cell21_562483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].length) (baseStart_562483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562483 prefixEnd_562483 := by exact prefixLift 562483
  have htrace : WordTrace (prefixWord ++ tailWord_562483) baseStart_562483 baseEnd_562483 := by
    simpa [prefixWord, tailWord_562483, baseEnd_562483] using wordTrace_append hprefix tailTrace_562483
  have hstable : (prefixWord ++ tailWord_562483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562483).length < 2 ^ (prefixWord ++ tailWord_562483).sum := by decide
  have hdescent : baseEnd_562483 < baseStart_562483 := by decide
  rcases family_descends (prefixWord ++ tailWord_562483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562632 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_562632 : Nat := 118140960795 + 562632 * 2 ^ 59
def prefixEnd_562632 : Nat := 4983230072969 + 3 ^ 40 * 562632 * 2
def baseEnd_562632 : Nat := 128400287822465748183337

theorem tailTrace_562632 : CollatzResearch.WordTrace tailWord_562632 prefixEnd_562632 128400287822465748183337 := by
  unfold tailWord_562632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10260437448843914370301075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13680583265125219160401433 10260437448843914370301075)
  ·
    refine ⟨15390656173265871555451613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10260437448843914370301075 15390656173265871555451613)
    ·
      refine ⟨5771496064974701833294355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15390656173265871555451613 5771496064974701833294355)
      ·
        refine ⟨8657244097462052749941533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5771496064974701833294355 8657244097462052749941533)
        ·
          refine ⟨3246466536548269781228075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8657244097462052749941533 3246466536548269781228075)
          ·
            refine ⟨4869699804822404671842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246466536548269781228075 4869699804822404671842113)
            ·
              refine ⟨3652274853616803503881585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869699804822404671842113 3652274853616803503881585)
              ·
                refine ⟨2739206140212602627911189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652274853616803503881585 2739206140212602627911189)
                ·
                  refine ⟨128400287822465748183337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2739206140212602627911189 128400287822465748183337)
                  ·
                    rfl

theorem cell21_562632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_562632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562632 prefixEnd_562632 := by exact prefixLift 562632
  have htrace : WordTrace (prefixWord ++ tailWord_562632) baseStart_562632 baseEnd_562632 := by
    simpa [prefixWord, tailWord_562632, baseEnd_562632] using wordTrace_append hprefix tailTrace_562632
  have hstable : (prefixWord ++ tailWord_562632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562632).length < 2 ^ (prefixWord ++ tailWord_562632).sum := by decide
  have hdescent : baseEnd_562632 < baseStart_562632 := by decide
  rcases family_descends (prefixWord ++ tailWord_562632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562649 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_562649 : Nat := 118140960795 + 562649 * 2 ^ 59
def prefixEnd_562649 : Nat := 4983230072969 + 3 ^ 40 * 562649 * 2
def baseEnd_562649 : Nat := 128404167454077496399969

theorem tailTrace_562649 : CollatzResearch.WordTrace tailWord_562649 prefixEnd_562649 128404167454077496399969 := by
  unfold tailWord_562649
  simp only [CollatzResearch.WordTrace]
  refine ⟨20521494938626240643971001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13680996625750827095980667 20521494938626240643971001)
  ·
    refine ⟨15391121203969680482978251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20521494938626240643971001 15391121203969680482978251)
    ·
      refine ⟨23086681805954520724467377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15391121203969680482978251 23086681805954520724467377)
      ·
        refine ⟨17315011354465890543350533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23086681805954520724467377 17315011354465890543350533)
        ·
          refine ⟨3246564628962354476878225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17315011354465890543350533 3246564628962354476878225)
          ·
            refine ⟨2434923471721765857658669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246564628962354476878225 2434923471721765857658669)
            ·
              refine ⟨913096301895662196622001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2434923471721765857658669 913096301895662196622001)
              ·
                refine ⟨684822226421746647466501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913096301895662196622001 684822226421746647466501)
                ·
                  refine ⟨128404167454077496399969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684822226421746647466501 128404167454077496399969)
                  ·
                    rfl

theorem cell21_562649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_562649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562649 prefixEnd_562649 := by exact prefixLift 562649
  have htrace : WordTrace (prefixWord ++ tailWord_562649) baseStart_562649 baseEnd_562649 := by
    simpa [prefixWord, tailWord_562649, baseEnd_562649] using wordTrace_append hprefix tailTrace_562649
  have hstable : (prefixWord ++ tailWord_562649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562649).length < 2 ^ (prefixWord ++ tailWord_562649).sum := by decide
  have hdescent : baseEnd_562649 < baseStart_562649 := by decide
  rcases family_descends (prefixWord ++ tailWord_562649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562680 : List Nat := [2, 1, 2, 1, 1, 7, 2, 5]
def baseStart_562680 : Nat := 118140960795 + 562680 * 2 ^ 59
def prefixEnd_562680 : Nat := 4983230072969 + 3 ^ 40 * 562680 * 2
def baseEnd_562680 : Nat := 42803747358809443794413

theorem tailTrace_562680 : CollatzResearch.WordTrace tailWord_562680 prefixEnd_562680 42803747358809443794413 := by
  unfold tailWord_562680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261312800756966469174747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13681750401009288625566329 10261312800756966469174747)
  ·
    refine ⟨15391969201135449703762121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261312800756966469174747 15391969201135449703762121)
    ·
      refine ⟨11543976900851587277821591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15391969201135449703762121 11543976900851587277821591)
      ·
        refine ⟨17315965351277380916732387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11543976900851587277821591 17315965351277380916732387)
        ·
          refine ⟨25973948026916071375098581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17315965351277380916732387 25973948026916071375098581)
          ·
            refine ⟨608764406880845422853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25973948026916071375098581 608764406880845422853873)
            ·
              refine ⟨456573305160634067140405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608764406880845422853873 456573305160634067140405)
              ·
                refine ⟨42803747358809443794413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456573305160634067140405 42803747358809443794413)
                ·
                  rfl

theorem cell21_562680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_562680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562680 prefixEnd_562680 := by exact prefixLift 562680
  have htrace : WordTrace (prefixWord ++ tailWord_562680) baseStart_562680 baseEnd_562680 := by
    simpa [prefixWord, tailWord_562680, baseEnd_562680] using wordTrace_append hprefix tailTrace_562680
  have hstable : (prefixWord ++ tailWord_562680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562680).length < 2 ^ (prefixWord ++ tailWord_562680).sum := by decide
  have hdescent : baseEnd_562680 < baseStart_562680 := by decide
  rcases family_descends (prefixWord ++ tailWord_562680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562686 : List Nat := [4, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_562686 : Nat := 118140960795 + 562686 * 2 ^ 59
def prefixEnd_562686 : Nat := 4983230072969 + 3 ^ 40 * 562686 * 2
def baseEnd_562686 : Nat := 128412611358173654283227

theorem tailTrace_562686 : CollatzResearch.WordTrace tailWord_562686 prefixEnd_562686 128412611358173654283227 := by
  unfold tailWord_562686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565355554936524495383489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13681896292994797308711941 2565355554936524495383489)
  ·
    refine ⟨1924016666202393371537617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2565355554936524495383489 1924016666202393371537617)
    ·
      refine ⟨1443012499651795028653213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1924016666202393371537617 1443012499651795028653213)
      ·
        refine ⟨541129687369423135744955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1443012499651795028653213 541129687369423135744955)
        ·
          refine ⟨811694531054134703617433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541129687369423135744955 811694531054134703617433)
          ·
            refine ⟨608770898290601027713075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811694531054134703617433 608770898290601027713075)
            ·
              refine ⟨913156347435901541569613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608770898290601027713075 913156347435901541569613)
              ·
                refine ⟨342433630288463078088605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913156347435901541569613 342433630288463078088605)
                ·
                  refine ⟨128412611358173654283227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342433630288463078088605 128412611358173654283227)
                  ·
                    rfl

theorem cell21_562686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_562686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562686 prefixEnd_562686 := by exact prefixLift 562686
  have htrace : WordTrace (prefixWord ++ tailWord_562686) baseStart_562686 baseEnd_562686 := by
    simpa [prefixWord, tailWord_562686, baseEnd_562686] using wordTrace_append hprefix tailTrace_562686
  have hstable : (prefixWord ++ tailWord_562686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562686).length < 2 ^ (prefixWord ++ tailWord_562686).sum := by decide
  have hdescent : baseEnd_562686 < baseStart_562686 := by decide
  rcases family_descends (prefixWord ++ tailWord_562686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562874 : List Nat := [3, 1, 1, 1, 2, 4, 9]
def baseStart_562874 : Nat := 118140960795 + 562874 * 2 ^ 59
def prefixEnd_562874 : Nat := 4983230072969 + 3 ^ 40 * 562874 * 2
def baseEnd_562874 : Nat := 14272835057725233905501

theorem tailTrace_562874 : CollatzResearch.WordTrace tailWord_562874 prefixEnd_562874 14272835057725233905501 := by
  unfold tailWord_562874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132425340702776017727919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13686467575207402713941117 5132425340702776017727919)
  ·
    refine ⟨7698638011054164026591879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5132425340702776017727919 7698638011054164026591879)
    ·
      refine ⟨11547957016581246039887819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698638011054164026591879 11547957016581246039887819)
      ·
        refine ⟨17321935524871869059831729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11547957016581246039887819 17321935524871869059831729)
        ·
          refine ⟨12991451643653901794873797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17321935524871869059831729 12991451643653901794873797)
          ·
            refine ⟨2435897183185106586538837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12991451643653901794873797 2435897183185106586538837)
            ·
              refine ⟨14272835057725233905501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2435897183185106586538837 14272835057725233905501)
              ·
                rfl

theorem cell21_562874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 9].length) (baseStart_562874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_562874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_562874 prefixEnd_562874 := by exact prefixLift 562874
  have htrace : WordTrace (prefixWord ++ tailWord_562874) baseStart_562874 baseEnd_562874 := by
    simpa [prefixWord, tailWord_562874, baseEnd_562874] using wordTrace_append hprefix tailTrace_562874
  have hstable : (prefixWord ++ tailWord_562874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562874).length < 2 ^ (prefixWord ++ tailWord_562874).sum := by decide
  have hdescent : baseEnd_562874 < baseStart_562874 := by decide
  rcases family_descends (prefixWord ++ tailWord_562874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563043 : List Nat := [1, 1, 1, 5, 4, 2, 7]
def baseStart_563043 : Nat := 118140960795 + 563043 * 2 ^ 59
def prefixEnd_563043 : Nat := 4983230072969 + 3 ^ 40 * 563043 * 2
def baseEnd_563043 : Nat := 14277120402446707425833

theorem tailTrace_563043 : CollatzResearch.WordTrace tailWord_563043 prefixEnd_563043 14277120402446707425833 := by
  unfold tailWord_563043
  simp only [CollatzResearch.WordTrace]
  refine ⟨20535865299198845933813783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13690576866132563955875855 20535865299198845933813783)
  ·
    refine ⟨30803797948798268900720675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20535865299198845933813783 30803797948798268900720675)
    ·
      refine ⟨46205696923197403351081013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30803797948798268900720675 46205696923197403351081013)
      ·
        refine ⟨4331784086549756564163845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46205696923197403351081013 4331784086549756564163845)
        ·
          refine ⟨812209516228079355780721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4331784086549756564163845 812209516228079355780721)
          ·
            refine ⟨609157137171059516835541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812209516228079355780721 609157137171059516835541)
            ·
              refine ⟨14277120402446707425833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 609157137171059516835541 14277120402446707425833)
              ·
                rfl

theorem cell21_563043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 7].length) (baseStart_563043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563043 prefixEnd_563043 := by exact prefixLift 563043
  have htrace : WordTrace (prefixWord ++ tailWord_563043) baseStart_563043 baseEnd_563043 := by
    simpa [prefixWord, tailWord_563043, baseEnd_563043] using wordTrace_append hprefix tailTrace_563043
  have hstable : (prefixWord ++ tailWord_563043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563043).length < 2 ^ (prefixWord ++ tailWord_563043).sum := by decide
  have hdescent : baseEnd_563043 < baseStart_563043 := by decide
  rcases family_descends (prefixWord ++ tailWord_563043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563108 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_563108 : Nat := 118140960795 + 563108 * 2 ^ 59
def prefixEnd_563108 : Nat := 4983230072969 + 3 ^ 40 * 563108 * 2
def baseEnd_563108 : Nat := 128508917507594698249031

theorem tailTrace_563108 : CollatzResearch.WordTrace tailWord_563108 prefixEnd_563108 128508917507594698249031 := by
  unfold tailWord_563108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269118021981681017464989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13692157362642241356619985 10269118021981681017464989)
  ·
    refine ⟨3850919258243130381549371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10269118021981681017464989 3850919258243130381549371)
    ·
      refine ⟨5776378887364695572324057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3850919258243130381549371 5776378887364695572324057)
      ·
        refine ⟨4332284165523521679243043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5776378887364695572324057 4332284165523521679243043)
        ·
          refine ⟨6498426248285282518864565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332284165523521679243043 6498426248285282518864565)
          ·
            refine ⟨609227460776745236143553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6498426248285282518864565 609227460776745236143553)
            ·
              refine ⟨456920595582558927107665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609227460776745236143553 456920595582558927107665)
              ·
                refine ⟨342690446686919195330749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456920595582558927107665 342690446686919195330749)
                ·
                  refine ⟨128508917507594698249031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342690446686919195330749 128508917507594698249031)
                  ·
                    rfl

theorem cell21_563108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_563108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563108 prefixEnd_563108 := by exact prefixLift 563108
  have htrace : WordTrace (prefixWord ++ tailWord_563108) baseStart_563108 baseEnd_563108 := by
    simpa [prefixWord, tailWord_563108, baseEnd_563108] using wordTrace_append hprefix tailTrace_563108
  have hstable : (prefixWord ++ tailWord_563108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563108).length < 2 ^ (prefixWord ++ tailWord_563108).sum := by decide
  have hdescent : baseEnd_563108 < baseStart_563108 := by decide
  rcases family_descends (prefixWord ++ tailWord_563108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563133 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_563133 : Nat := 118140960795 + 563133 * 2 ^ 59
def prefixEnd_563133 : Nat := 4983230072969 + 3 ^ 40 * 563133 * 2
def baseEnd_563133 : Nat := 128514622848200210332313

theorem tailTrace_563133 : CollatzResearch.WordTrace tailWord_563133 prefixEnd_563133 128514622848200210332313 := by
  unfold tailWord_563133
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539147868872791304590053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13692765245915194203060035 20539147868872791304590053)
  ·
    refine ⟨3851090225413648369610635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20539147868872791304590053 3851090225413648369610635)
    ·
      refine ⟨5776635338120472554415953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3851090225413648369610635 5776635338120472554415953)
      ·
        refine ⟨4332476503590354415811965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5776635338120472554415953 4332476503590354415811965)
        ·
          refine ⟨1624678688846382905929487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4332476503590354415811965 1624678688846382905929487)
          ·
            refine ⟨2437018033269574358894231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624678688846382905929487 2437018033269574358894231)
            ·
              refine ⟨3655527049904361538341347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437018033269574358894231 3655527049904361538341347)
              ·
                refine ⟨5483290574856542307512021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655527049904361538341347 5483290574856542307512021)
                ·
                  refine ⟨128514622848200210332313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5483290574856542307512021 128514622848200210332313)
                  ·
                    rfl

theorem cell21_563133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_563133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563133 prefixEnd_563133 := by exact prefixLift 563133
  have htrace : WordTrace (prefixWord ++ tailWord_563133) baseStart_563133 baseEnd_563133 := by
    simpa [prefixWord, tailWord_563133, baseEnd_563133] using wordTrace_append hprefix tailTrace_563133
  have hstable : (prefixWord ++ tailWord_563133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563133).length < 2 ^ (prefixWord ++ tailWord_563133).sum := by decide
  have hdescent : baseEnd_563133 < baseStart_563133 := by decide
  rcases family_descends (prefixWord ++ tailWord_563133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563147 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_563147 : Nat := 118140960795 + 563147 * 2 ^ 59
def prefixEnd_563147 : Nat := 4983230072969 + 3 ^ 40 * 563147 * 2
def baseEnd_563147 : Nat := 128517817838939297098951

theorem tailTrace_563147 : CollatzResearch.WordTrace tailWord_563147 prefixEnd_563147 128517817838939297098951 := by
  unfold tailWord_563147
  simp only [CollatzResearch.WordTrace]
  refine ⟨20539658490822071695599695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13693105660548047797066463 20539658490822071695599695)
  ·
    refine ⟨30809487736233107543399543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20539658490822071695599695 30809487736233107543399543)
    ·
      refine ⟨46214231604349661315099315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30809487736233107543399543 46214231604349661315099315)
      ·
        refine ⟨69321347406524491972648973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46214231604349661315099315 69321347406524491972648973)
        ·
          refine ⟨25995505277446684489743365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69321347406524491972648973 25995505277446684489743365)
          ·
            refine ⟨4874157239521253341826881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25995505277446684489743365 4874157239521253341826881)
            ·
              refine ⟨3655617929640940006370161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4874157239521253341826881 3655617929640940006370161)
              ·
                refine ⟨2741713447230705004777621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655617929640940006370161 2741713447230705004777621)
                ·
                  refine ⟨128517817838939297098951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2741713447230705004777621 128517817838939297098951)
                  ·
                    rfl

theorem cell21_563147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_563147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563147 prefixEnd_563147 := by exact prefixLift 563147
  have htrace : WordTrace (prefixWord ++ tailWord_563147) baseStart_563147 baseEnd_563147 := by
    simpa [prefixWord, tailWord_563147, baseEnd_563147] using wordTrace_append hprefix tailTrace_563147
  have hstable : (prefixWord ++ tailWord_563147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563147).length < 2 ^ (prefixWord ++ tailWord_563147).sum := by decide
  have hdescent : baseEnd_563147 < baseStart_563147 := by decide
  rcases family_descends (prefixWord ++ tailWord_563147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563178 : List Nat := [3, 1, 3, 1, 2, 1, 2, 8]
def baseStart_563178 : Nat := 118140960795 + 563178 * 2 ^ 59
def prefixEnd_563178 : Nat := 4983230072969 + 3 ^ 40 * 563178 * 2
def baseEnd_563178 : Nat := 42841630820430044027407

theorem tailTrace_563178 : CollatzResearch.WordTrace tailWord_563178 prefixEnd_563178 42841630820430044027407 := by
  unfold tailWord_563178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135197288427440997494547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13693859435806509326652125 5135197288427440997494547)
  ·
    refine ⟨7702795932641161496241821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135197288427440997494547 7702795932641161496241821)
    ·
      refine ⟨2888548474740435561090683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7702795932641161496241821 2888548474740435561090683)
      ·
        refine ⟨4332822712110653341636025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888548474740435561090683 4332822712110653341636025)
        ·
          refine ⟨3249617034082990006227019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4332822712110653341636025 3249617034082990006227019)
          ·
            refine ⟨4874425551124485009340529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249617034082990006227019 4874425551124485009340529)
            ·
              refine ⟨3655819163343363757005397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4874425551124485009340529 3655819163343363757005397)
              ·
                refine ⟨42841630820430044027407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3655819163343363757005397 42841630820430044027407)
                ·
                  rfl

theorem cell21_563178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_563178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563178 prefixEnd_563178 := by exact prefixLift 563178
  have htrace : WordTrace (prefixWord ++ tailWord_563178) baseStart_563178 baseEnd_563178 := by
    simpa [prefixWord, tailWord_563178, baseEnd_563178] using wordTrace_append hprefix tailTrace_563178
  have hstable : (prefixWord ++ tailWord_563178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563178).length < 2 ^ (prefixWord ++ tailWord_563178).sum := by decide
  have hdescent : baseEnd_563178 < baseStart_563178 := by decide
  rcases family_descends (prefixWord ++ tailWord_563178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563226 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_563226 : Nat := 118140960795 + 563226 * 2 ^ 59
def prefixEnd_563226 : Nat := 4983230072969 + 3 ^ 40 * 563226 * 2
def baseEnd_563226 : Nat := 128535846715252715282123

theorem tailTrace_563226 : CollatzResearch.WordTrace tailWord_563226 prefixEnd_563226 128535846715252715282123 := by
  unfold tailWord_563226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5135634964383967046931383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13695026571690578791817021 5135634964383967046931383)
  ·
    refine ⟨7703452446575950570397075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5135634964383967046931383 7703452446575950570397075)
    ·
      refine ⟨11555178669863925855595613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7703452446575950570397075 11555178669863925855595613)
      ·
        refine ⟨4333192001198972195848355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11555178669863925855595613 4333192001198972195848355)
        ·
          refine ⟨6499788001798458293772533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333192001198972195848355 6499788001798458293772533)
          ·
            refine ⟨609355125168605465041175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6499788001798458293772533 609355125168605465041175)
            ·
              refine ⟨914032687752908197561763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609355125168605465041175 914032687752908197561763)
              ·
                refine ⟨1371049031629362296342645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914032687752908197561763 1371049031629362296342645)
                ·
                  refine ⟨128535846715252715282123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371049031629362296342645 128535846715252715282123)
                  ·
                    rfl

theorem cell21_563226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_563226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563226 prefixEnd_563226 := by exact prefixLift 563226
  have htrace : WordTrace (prefixWord ++ tailWord_563226) baseStart_563226 baseEnd_563226 := by
    simpa [prefixWord, tailWord_563226, baseEnd_563226] using wordTrace_append hprefix tailTrace_563226
  have hstable : (prefixWord ++ tailWord_563226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563226).length < 2 ^ (prefixWord ++ tailWord_563226).sum := by decide
  have hdescent : baseEnd_563226 < baseStart_563226 := by decide
  rcases family_descends (prefixWord ++ tailWord_563226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563333 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_563333 : Nat := 118140960795 + 563333 * 2 ^ 59
def prefixEnd_563333 : Nat := 4983230072969 + 3 ^ 40 * 563333 * 2
def baseEnd_563333 : Nat := 128560265573044306998571

theorem tailTrace_563333 : CollatzResearch.WordTrace tailWord_563333 prefixEnd_563333 128560265573044306998571 := by
  unfold tailWord_563333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546442468148225461870653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697628312098816974580435 20546442468148225461870653)
  ·
    refine ⟨7704915925555584548201495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20546442468148225461870653 7704915925555584548201495)
    ·
      refine ⟨11557373888333376822302243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704915925555584548201495 11557373888333376822302243)
      ·
        refine ⟨17336060832500065233453365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11557373888333376822302243 17336060832500065233453365)
        ·
          refine ⟨1625255703046881115636253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17336060832500065233453365 1625255703046881115636253)
          ·
            refine ⟨609470888642580418363595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1625255703046881115636253 609470888642580418363595)
            ·
              refine ⟨914206332963870627545393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609470888642580418363595 914206332963870627545393)
              ·
                refine ⟨685654749722902970659045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914206332963870627545393 685654749722902970659045)
                ·
                  refine ⟨128560265573044306998571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 685654749722902970659045 128560265573044306998571)
                  ·
                    rfl

theorem cell21_563333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_563333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563333 prefixEnd_563333 := by exact prefixLift 563333
  have htrace : WordTrace (prefixWord ++ tailWord_563333) baseStart_563333 baseEnd_563333 := by
    simpa [prefixWord, tailWord_563333, baseEnd_563333] using wordTrace_append hprefix tailTrace_563333
  have hstable : (prefixWord ++ tailWord_563333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563333).length < 2 ^ (prefixWord ++ tailWord_563333).sum := by decide
  have hdescent : baseEnd_563333 < baseStart_563333 := by decide
  rcases family_descends (prefixWord ++ tailWord_563333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563361 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_563361 : Nat := 118140960795 + 563361 * 2 ^ 59
def prefixEnd_563361 : Nat := 4983230072969 + 3 ^ 40 * 563361 * 2
def baseEnd_563361 : Nat := 128566655554522480531847

theorem tailTrace_563361 : CollatzResearch.WordTrace tailWord_563361 prefixEnd_563361 128566655554522480531847 := by
  unfold tailWord_563361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547463712046786243889937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13698309141364524162593291 20547463712046786243889937)
  ·
    refine ⟨15410597784035089682917453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20547463712046786243889937 15410597784035089682917453)
    ·
      refine ⟨5778974169013158631094045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15410597784035089682917453 5778974169013158631094045)
      ·
        refine ⟨2167115313379934486660267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5778974169013158631094045 2167115313379934486660267)
        ·
          refine ⟨3250672970069901729990401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167115313379934486660267 3250672970069901729990401)
          ·
            refine ⟨2438004727552426297492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3250672970069901729990401 2438004727552426297492801)
            ·
              refine ⟨1828503545664319723119601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438004727552426297492801 1828503545664319723119601)
              ·
                refine ⟨1371377659248239792339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1828503545664319723119601 1371377659248239792339701)
                ·
                  refine ⟨128566655554522480531847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371377659248239792339701 128566655554522480531847)
                  ·
                    rfl

theorem cell21_563361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_563361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563361 prefixEnd_563361 := by exact prefixLift 563361
  have htrace : WordTrace (prefixWord ++ tailWord_563361) baseStart_563361 baseEnd_563361 := by
    simpa [prefixWord, tailWord_563361, baseEnd_563361] using wordTrace_append hprefix tailTrace_563361
  have hstable : (prefixWord ++ tailWord_563361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563361).length < 2 ^ (prefixWord ++ tailWord_563361).sum := by decide
  have hdescent : baseEnd_563361 < baseStart_563361 := by decide
  rcases family_descends (prefixWord ++ tailWord_563361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563364 : List Nat := [2, 3, 1, 2, 4, 2, 2, 5]
def baseStart_563364 : Nat := 118140960795 + 563364 * 2 ^ 59
def prefixEnd_563364 : Nat := 4983230072969 + 3 ^ 40 * 563364 * 2
def baseEnd_563364 : Nat := 42855780065131713993947

theorem tailTrace_563364 : CollatzResearch.WordTrace tailWord_563364 prefixEnd_563364 42855780065131713993947 := by
  unfold tailWord_563364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10273786565517958878124573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13698382087357278504166097 10273786565517958878124573)
  ·
    refine ⟨3852669962069234579296715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10273786565517958878124573 3852669962069234579296715)
    ·
      refine ⟨5779004943103851868945073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852669962069234579296715 5779004943103851868945073)
      ·
        refine ⟨4334253707327888901708805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5779004943103851868945073 4334253707327888901708805)
        ·
          refine ⟨812672570123979169070401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4334253707327888901708805 812672570123979169070401)
          ·
            refine ⟨609504427592984376802801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812672570123979169070401 609504427592984376802801)
            ·
              refine ⟨457128320694738282602101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609504427592984376802801 457128320694738282602101)
              ·
                refine ⟨42855780065131713993947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457128320694738282602101 42855780065131713993947)
                ·
                  rfl

theorem cell21_563364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_563364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563364 prefixEnd_563364 := by exact prefixLift 563364
  have htrace : WordTrace (prefixWord ++ tailWord_563364) baseStart_563364 baseEnd_563364 := by
    simpa [prefixWord, tailWord_563364, baseEnd_563364] using wordTrace_append hprefix tailTrace_563364
  have hstable : (prefixWord ++ tailWord_563364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563364).length < 2 ^ (prefixWord ++ tailWord_563364).sum := by decide
  have hdescent : baseEnd_563364 < baseStart_563364 := by decide
  rcases family_descends (prefixWord ++ tailWord_563364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563406 : List Nat := [4, 1, 1, 1, 4, 1, 1, 8]
def baseStart_563406 : Nat := 118140960795 + 563406 * 2 ^ 59
def prefixEnd_563406 : Nat := 4983230072969 + 3 ^ 40 * 563406 * 2
def baseEnd_563406 : Nat := 42858975055870800760585

theorem tailTrace_563406 : CollatzResearch.WordTrace tailWord_563406 prefixEnd_563406 42858975055870800760585 := by
  unfold tailWord_563406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568638124610469866159759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13699403331255839286185381 2568638124610469866159759)
  ·
    refine ⟨3852957186915704799239639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568638124610469866159759 3852957186915704799239639)
    ·
      refine ⟨5779435780373557198859459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852957186915704799239639 5779435780373557198859459)
      ·
        refine ⟨8669153670560335798289189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779435780373557198859459 8669153670560335798289189)
        ·
          refine ⟨1625466313230062962179223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8669153670560335798289189 1625466313230062962179223)
          ·
            refine ⟨2438199469845094443268835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625466313230062962179223 2438199469845094443268835)
            ·
              refine ⟨3657299204767641664903253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438199469845094443268835 3657299204767641664903253)
              ·
                refine ⟨42858975055870800760585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3657299204767641664903253 42858975055870800760585)
                ·
                  rfl

theorem cell21_563406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_563406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563406 prefixEnd_563406 := by exact prefixLift 563406
  have htrace : WordTrace (prefixWord ++ tailWord_563406) baseStart_563406 baseEnd_563406 := by
    simpa [prefixWord, tailWord_563406, baseEnd_563406] using wordTrace_append hprefix tailTrace_563406
  have hstable : (prefixWord ++ tailWord_563406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563406).length < 2 ^ (prefixWord ++ tailWord_563406).sum := by decide
  have hdescent : baseEnd_563406 < baseStart_563406 := by decide
  rcases family_descends (prefixWord ++ tailWord_563406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563513 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_563513 : Nat := 118140960795 + 563513 * 2 ^ 59
def prefixEnd_563513 : Nat := 4983230072969 + 3 ^ 40 * 563513 * 2
def baseEnd_563513 : Nat := 128601344025403993998203

theorem tailTrace_563513 : CollatzResearch.WordTrace tailWord_563513 prefixEnd_563513 128601344025403993998203 := by
  unfold tailWord_563513
  simp only [CollatzResearch.WordTrace]
  refine ⟨20553007607496116203423193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13702005071664077468948795 20553007607496116203423193)
  ·
    refine ⟨15414755705622087152567395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20553007607496116203423193 15414755705622087152567395)
    ·
      refine ⟨23122133558433130728851093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15414755705622087152567395 23122133558433130728851093)
      ·
        refine ⟨1083850010551553002914895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23122133558433130728851093 1083850010551553002914895)
        ·
          refine ⟨1625775015827329504372343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083850010551553002914895 1625775015827329504372343)
          ·
            refine ⟨2438662523740994256558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625775015827329504372343 2438662523740994256558515)
            ·
              refine ⟨3657993785611491384837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438662523740994256558515 3657993785611491384837773)
              ·
                refine ⟨1371747669604309269314165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657993785611491384837773 1371747669604309269314165)
                ·
                  refine ⟨128601344025403993998203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371747669604309269314165 128601344025403993998203)
                  ·
                    rfl

theorem cell21_563513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_563513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563513 prefixEnd_563513 := by exact prefixLift 563513
  have htrace : WordTrace (prefixWord ++ tailWord_563513) baseStart_563513 baseEnd_563513 := by
    simpa [prefixWord, tailWord_563513, baseEnd_563513] using wordTrace_append hprefix tailTrace_563513
  have hstable : (prefixWord ++ tailWord_563513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563513).length < 2 ^ (prefixWord ++ tailWord_563513).sum := by decide
  have hdescent : baseEnd_563513 < baseStart_563513 := by decide
  rcases family_descends (prefixWord ++ tailWord_563513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563550 : List Nat := [4, 4, 2, 1, 1, 2, 7]
def baseStart_563550 : Nat := 118140960795 + 563550 * 2 ^ 59
def prefixEnd_563550 : Nat := 4983230072969 + 3 ^ 40 * 563550 * 2
def baseEnd_563550 : Nat := 14289976436611127986829

theorem tailTrace_563550 : CollatzResearch.WordTrace tailWord_563550 prefixEnd_563550 14289976436611127986829 := by
  unfold tailWord_563550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569294638545258940315013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13702904738908047681680069 2569294638545258940315013)
  ·
    refine ⟨481742744727236051309065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2569294638545258940315013 481742744727236051309065)
    ·
      refine ⟨361307058545427038481799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 481742744727236051309065 361307058545427038481799)
      ·
        refine ⟨541960587818140557722699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361307058545427038481799 541960587818140557722699)
        ·
          refine ⟨812940881727210836584049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541960587818140557722699 812940881727210836584049)
          ·
            refine ⟨609705661295408127438037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812940881727210836584049 609705661295408127438037)
            ·
              refine ⟨14289976436611127986829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 609705661295408127438037 14289976436611127986829)
              ·
                rfl

theorem cell21_563550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 7].length) (baseStart_563550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563550 prefixEnd_563550 := by exact prefixLift 563550
  have htrace : WordTrace (prefixWord ++ tailWord_563550) baseStart_563550 baseEnd_563550 := by
    simpa [prefixWord, tailWord_563550, baseEnd_563550] using wordTrace_append hprefix tailTrace_563550
  have hstable : (prefixWord ++ tailWord_563550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563550).length < 2 ^ (prefixWord ++ tailWord_563550).sum := by decide
  have hdescent : baseEnd_563550 < baseStart_563550 := by decide
  rcases family_descends (prefixWord ++ tailWord_563550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563623 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 3]
def baseStart_563623 : Nat := 118140960795 + 563623 * 2 ^ 59
def prefixEnd_563623 : Nat := 4983230072969 + 3 ^ 40 * 563623 * 2
def baseEnd_563623 : Nat := 128626447524068247164645

theorem tailTrace_563623 : CollatzResearch.WordTrace tailWord_563623 prefixEnd_563623 128626447524068247164645 := by
  unfold tailWord_563623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20557019637097604989927523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13704679758065069993285015 20557019637097604989927523)
  ·
    refine ⟨30835529455646407484891285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20557019637097604989927523 30835529455646407484891285)
    ·
      refine ⟨1445415443233425350854279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30835529455646407484891285 1445415443233425350854279)
      ·
        refine ⟨2168123164850138026281419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445415443233425350854279 2168123164850138026281419)
        ·
          refine ⟨3252184747275207039422129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168123164850138026281419 3252184747275207039422129)
          ·
            refine ⟨2439138560456405279566597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252184747275207039422129 2439138560456405279566597)
            ·
              refine ⟨457338480085575989918737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2439138560456405279566597 457338480085575989918737)
              ·
                refine ⟨343003860064181992439053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457338480085575989918737 343003860064181992439053)
                ·
                  refine ⟨128626447524068247164645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343003860064181992439053 128626447524068247164645)
                  ·
                    rfl

theorem cell21_563623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 3].length) (baseStart_563623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563623 prefixEnd_563623 := by exact prefixLift 563623
  have htrace : WordTrace (prefixWord ++ tailWord_563623) baseStart_563623 baseEnd_563623 := by
    simpa [prefixWord, tailWord_563623, baseEnd_563623] using wordTrace_append hprefix tailTrace_563623
  have hstable : (prefixWord ++ tailWord_563623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563623).length < 2 ^ (prefixWord ++ tailWord_563623).sum := by decide
  have hdescent : baseEnd_563623 < baseStart_563623 := by decide
  rcases family_descends (prefixWord ++ tailWord_563623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563626 : List Nat := [3, 1, 6, 1, 2, 1, 1, 6]
def baseStart_563626 : Nat := 118140960795 + 563626 * 2 ^ 59
def prefixEnd_563626 : Nat := 4983230072969 + 3 ^ 40 * 563626 * 2
def baseEnd_563626 : Nat := 42875710721646969538213

theorem tailTrace_563626 : CollatzResearch.WordTrace tailWord_563626 prefixEnd_563626 42875710721646969538213 := by
  unfold tailWord_563626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139282264021684125571683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13704752704057824334857821 5139282264021684125571683)
  ·
    refine ⟨7708923396032526188357525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5139282264021684125571683 7708923396032526188357525)
    ·
      refine ⟨361355784189024665079259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7708923396032526188357525 361355784189024665079259)
      ·
        refine ⟨542033676283536997618889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361355784189024665079259 542033676283536997618889)
        ·
          refine ⟨406525257212652748214167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542033676283536997618889 406525257212652748214167)
          ·
            refine ⟨609787885818979122321251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406525257212652748214167 609787885818979122321251)
            ·
              refine ⟨914681828728468683481877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609787885818979122321251 914681828728468683481877)
              ·
                refine ⟨42875710721646969538213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 914681828728468683481877 42875710721646969538213)
                ·
                  rfl

theorem cell21_563626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_563626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563626 prefixEnd_563626 := by exact prefixLift 563626
  have htrace : WordTrace (prefixWord ++ tailWord_563626) baseStart_563626 baseEnd_563626 := by
    simpa [prefixWord, tailWord_563626, baseEnd_563626] using wordTrace_append hprefix tailTrace_563626
  have hstable : (prefixWord ++ tailWord_563626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563626).length < 2 ^ (prefixWord ++ tailWord_563626).sum := by decide
  have hdescent : baseEnd_563626 < baseStart_563626 := by decide
  rcases family_descends (prefixWord ++ tailWord_563626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563679 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_563679 : Nat := 118140960795 + 563679 * 2 ^ 59
def prefixEnd_563679 : Nat := 4983230072969 + 3 ^ 40 * 563679 * 2
def baseEnd_563679 : Nat := 128639227487024594231197

theorem tailTrace_563679 : CollatzResearch.WordTrace tailWord_563679 prefixEnd_563679 128639227487024594231197 := by
  unfold tailWord_563679
  simp only [CollatzResearch.WordTrace]
  refine ⟨20559062124894726553966091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13706041416596484369310727 20559062124894726553966091)
  ·
    refine ⟨30838593187342089830949137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20559062124894726553966091 30838593187342089830949137)
    ·
      refine ⟨23128944890506567373211853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30838593187342089830949137 23128944890506567373211853)
      ·
        refine ⟨8673354333939962764954445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23128944890506567373211853 8673354333939962764954445)
        ·
          refine ⟨3252507875227486036857917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8673354333939962764954445 3252507875227486036857917)
          ·
            refine ⟨1219690453210307263821719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3252507875227486036857917 1219690453210307263821719)
            ·
              refine ⟨1829535679815460895732579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219690453210307263821719 1829535679815460895732579)
              ·
                refine ⟨2744303519723191343598869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829535679815460895732579 2744303519723191343598869)
                ·
                  refine ⟨128639227487024594231197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2744303519723191343598869 128639227487024594231197)
                  ·
                    rfl

theorem cell21_563679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_563679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563679 prefixEnd_563679 := by exact prefixLift 563679
  have htrace : WordTrace (prefixWord ++ tailWord_563679) baseStart_563679 baseEnd_563679 := by
    simpa [prefixWord, tailWord_563679, baseEnd_563679] using wordTrace_append hprefix tailTrace_563679
  have hstable : (prefixWord ++ tailWord_563679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563679).length < 2 ^ (prefixWord ++ tailWord_563679).sum := by decide
  have hdescent : baseEnd_563679 < baseStart_563679 := by decide
  rcases family_descends (prefixWord ++ tailWord_563679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563696 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_563696 : Nat := 118140960795 + 563696 * 2 ^ 59
def prefixEnd_563696 : Nat := 4983230072969 + 3 ^ 40 * 563696 * 2
def baseEnd_563696 : Nat := 128643107118636342447829

theorem tailTrace_563696 : CollatzResearch.WordTrace tailWord_563696 prefixEnd_563696 128643107118636342447829 := by
  unfold tailWord_563696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10279841082916569228667471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13706454777222092304889961 10279841082916569228667471)
  ·
    refine ⟨15419761624374853843001207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10279841082916569228667471 15419761624374853843001207)
    ·
      refine ⟨23129642436562280764501811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15419761624374853843001207 23129642436562280764501811)
      ·
        refine ⟨34694463654843421146752717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23129642436562280764501811 34694463654843421146752717)
        ·
          refine ⟨13010423870566282930032269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34694463654843421146752717 13010423870566282930032269)
          ·
            refine ⟨4878908951462356098762101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13010423870566282930032269 4878908951462356098762101)
            ·
              refine ⟨457397714199595884258947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4878908951462356098762101 457397714199595884258947)
              ·
                refine ⟨686096571299393826388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457397714199595884258947 686096571299393826388421)
                ·
                  refine ⟨128643107118636342447829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686096571299393826388421 128643107118636342447829)
                  ·
                    rfl

theorem cell21_563696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_563696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563696 prefixEnd_563696 := by exact prefixLift 563696
  have htrace : WordTrace (prefixWord ++ tailWord_563696) baseStart_563696 baseEnd_563696 := by
    simpa [prefixWord, tailWord_563696, baseEnd_563696] using wordTrace_append hprefix tailTrace_563696
  have hstable : (prefixWord ++ tailWord_563696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563696).length < 2 ^ (prefixWord ++ tailWord_563696).sum := by decide
  have hdescent : baseEnd_563696 < baseStart_563696 := by decide
  rcases family_descends (prefixWord ++ tailWord_563696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563741 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_563741 : Nat := 118140960795 + 563741 * 2 ^ 59
def prefixEnd_563741 : Nat := 4983230072969 + 3 ^ 40 * 563741 * 2
def baseEnd_563741 : Nat := 128653376731726264197737

theorem tailTrace_563741 : CollatzResearch.WordTrace tailWord_563741 prefixEnd_563741 128653376731726264197737 := by
  unfold tailWord_563741
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561323450670111142723077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13707548967113407428482051 20561323450670111142723077)
  ·
    refine ⟨3855248147000645839260577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20561323450670111142723077 3855248147000645839260577)
    ·
      refine ⟨2891436110250484379445433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3855248147000645839260577 2891436110250484379445433)
      ·
        refine ⟨2168577082687863284584075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2891436110250484379445433 2168577082687863284584075)
        ·
          refine ⟨3252865624031794926876113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168577082687863284584075 3252865624031794926876113)
          ·
            refine ⟨2439649218023846195157085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252865624031794926876113 2439649218023846195157085)
            ·
              refine ⟨914868456758942323183907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2439649218023846195157085 914868456758942323183907)
              ·
                refine ⟨1372302685138413484775861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914868456758942323183907 1372302685138413484775861)
                ·
                  refine ⟨128653376731726264197737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1372302685138413484775861 128653376731726264197737)
                  ·
                    rfl

theorem cell21_563741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_563741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563741 prefixEnd_563741 := by exact prefixLift 563741
  have htrace : WordTrace (prefixWord ++ tailWord_563741) baseStart_563741 baseEnd_563741 := by
    simpa [prefixWord, tailWord_563741, baseEnd_563741] using wordTrace_append hprefix tailTrace_563741
  have hstable : (prefixWord ++ tailWord_563741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563741).length < 2 ^ (prefixWord ++ tailWord_563741).sum := by decide
  have hdescent : baseEnd_563741 < baseStart_563741 := by decide
  rcases family_descends (prefixWord ++ tailWord_563741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563769 : List Nat := [1, 2, 1, 5, 1, 1, 1, 9]
def baseStart_563769 : Nat := 118140960795 + 563769 * 2 ^ 59
def prefixEnd_563769 : Nat := 4983230072969 + 3 ^ 40 * 563769 * 2
def baseEnd_563769 : Nat := 42886588904401479243671

theorem tailTrace_563769 : CollatzResearch.WordTrace tailWord_563769 prefixEnd_563769 42886588904401479243671 := by
  unfold tailWord_563769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20562344694568671924742361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13708229796379114616494907 20562344694568671924742361)
  ·
    refine ⟨15421758520926503943556771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20562344694568671924742361 15421758520926503943556771)
    ·
      refine ⟨23132637781389755915335157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15421758520926503943556771 23132637781389755915335157)
      ·
        refine ⟨2168684792005289617062671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23132637781389755915335157 2168684792005289617062671)
        ·
          refine ⟨3253027188007934425594007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168684792005289617062671 3253027188007934425594007)
          ·
            refine ⟨4879540782011901638391011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253027188007934425594007 4879540782011901638391011)
            ·
              refine ⟨7319311173017852457586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879540782011901638391011 7319311173017852457586517)
              ·
                refine ⟨42886588904401479243671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7319311173017852457586517 42886588904401479243671)
                ·
                  rfl

theorem cell21_563769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_563769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563769 prefixEnd_563769 := by exact prefixLift 563769
  have htrace : WordTrace (prefixWord ++ tailWord_563769) baseStart_563769 baseEnd_563769 := by
    simpa [prefixWord, tailWord_563769, baseEnd_563769] using wordTrace_append hprefix tailTrace_563769
  have hstable : (prefixWord ++ tailWord_563769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563769).length < 2 ^ (prefixWord ++ tailWord_563769).sum := by decide
  have hdescent : baseEnd_563769 < baseStart_563769 := by decide
  rcases family_descends (prefixWord ++ tailWord_563769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563789 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_563789 : Nat := 118140960795 + 563789 * 2 ^ 59
def prefixEnd_563789 : Nat := 4983230072969 + 3 ^ 40 * 563789 * 2
def baseEnd_563789 : Nat := 128664330985688847397639

theorem tailTrace_563789 : CollatzResearch.WordTrace tailWord_563789 prefixEnd_563789 128664330985688847397639 := by
  unfold tailWord_563789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563074154496215340470421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13708716102997476893646947 20563074154496215340470421)
  ·
    refine ⟨963894100992010094084551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20563074154496215340470421 963894100992010094084551)
    ·
      refine ⟨1445841151488015141126827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963894100992010094084551 1445841151488015141126827)
      ·
        refine ⟨2168761727232022711690241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445841151488015141126827 2168761727232022711690241)
        ·
          refine ⟨1626571295424017033767681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2168761727232022711690241 1626571295424017033767681)
          ·
            refine ⟨1219928471568012775325761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626571295424017033767681 1219928471568012775325761)
            ·
              refine ⟨914946353676009581494321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219928471568012775325761 914946353676009581494321)
              ·
                refine ⟨686209765257007186120741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914946353676009581494321 686209765257007186120741)
                ·
                  refine ⟨128664330985688847397639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686209765257007186120741 128664330985688847397639)
                  ·
                    rfl

theorem cell21_563789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_563789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563789 prefixEnd_563789 := by exact prefixLift 563789
  have htrace : WordTrace (prefixWord ++ tailWord_563789) baseStart_563789 baseEnd_563789 := by
    simpa [prefixWord, tailWord_563789, baseEnd_563789] using wordTrace_append hprefix tailTrace_563789
  have hstable : (prefixWord ++ tailWord_563789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563789).length < 2 ^ (prefixWord ++ tailWord_563789).sum := by decide
  have hdescent : baseEnd_563789 < baseStart_563789 := by decide
  rcases family_descends (prefixWord ++ tailWord_563789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563845 : List Nat := [1, 3, 1, 1, 4, 3, 8]
def baseStart_563845 : Nat := 118140960795 + 563845 * 2 ^ 59
def prefixEnd_563845 : Nat := 4983230072969 + 3 ^ 40 * 563845 * 2
def baseEnd_563845 : Nat := 14297456772071688273799

theorem tailTrace_563845 : CollatzResearch.WordTrace tailWord_563845 prefixEnd_563845 14297456772071688273799 := by
  unfold tailWord_563845
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565116642293336904508989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13710077761528891269672659 20565116642293336904508989)
  ·
    refine ⟨7711918740860001339190871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20565116642293336904508989 7711918740860001339190871)
    ·
      refine ⟨11567878111290002008786307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711918740860001339190871 11567878111290002008786307)
      ·
        refine ⟨17351817166935003013179461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567878111290002008786307 17351817166935003013179461)
        ·
          refine ⟨3253465718800313064971149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17351817166935003013179461 3253465718800313064971149)
          ·
            refine ⟨1220049644550117399364181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3253465718800313064971149 1220049644550117399364181)
            ·
              refine ⟨14297456772071688273799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1220049644550117399364181 14297456772071688273799)
              ·
                rfl

theorem cell21_563845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 8].length) (baseStart_563845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563845 prefixEnd_563845 := by exact prefixLift 563845
  have htrace : WordTrace (prefixWord ++ tailWord_563845) baseStart_563845 baseEnd_563845 := by
    simpa [prefixWord, tailWord_563845, baseEnd_563845] using wordTrace_append hprefix tailTrace_563845
  have hstable : (prefixWord ++ tailWord_563845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563845).length < 2 ^ (prefixWord ++ tailWord_563845).sum := by decide
  have hdescent : baseEnd_563845 < baseStart_563845 := by decide
  rcases family_descends (prefixWord ++ tailWord_563845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563859 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_563859 : Nat := 118140960795 + 563859 * 2 ^ 59
def prefixEnd_563859 : Nat := 4983230072969 + 3 ^ 40 * 563859 * 2
def baseEnd_563859 : Nat := 128680305939384281230829

theorem tailTrace_563859 : CollatzResearch.WordTrace tailWord_563859 prefixEnd_563859 128680305939384281230829 := by
  unfold tailWord_563859
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565627264242617295518631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13710418176161744863679087 20565627264242617295518631)
  ·
    refine ⟨30848440896363925943277947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20565627264242617295518631 30848440896363925943277947)
    ·
      refine ⟨46272661344545888914916921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30848440896363925943277947 46272661344545888914916921)
      ·
        refine ⟨34704496008409416686187691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46272661344545888914916921 34704496008409416686187691)
        ·
          refine ⟨52056744012614125029281537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34704496008409416686187691 52056744012614125029281537)
          ·
            refine ⟨39042558009460593771961153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52056744012614125029281537 39042558009460593771961153)
            ·
              refine ⟨29281918507095445328970865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39042558009460593771961153 29281918507095445328970865)
              ·
                refine ⟨21961438880321583996728149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29281918507095445328970865 21961438880321583996728149)
                ·
                  refine ⟨128680305939384281230829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21961438880321583996728149 128680305939384281230829)
                  ·
                    rfl

theorem cell21_563859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_563859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563859 prefixEnd_563859 := by exact prefixLift 563859
  have htrace : WordTrace (prefixWord ++ tailWord_563859) baseStart_563859 baseEnd_563859 := by
    simpa [prefixWord, tailWord_563859, baseEnd_563859] using wordTrace_append hprefix tailTrace_563859
  have hstable : (prefixWord ++ tailWord_563859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563859).length < 2 ^ (prefixWord ++ tailWord_563859).sum := by decide
  have hdescent : baseEnd_563859 < baseStart_563859 := by decide
  rcases family_descends (prefixWord ++ tailWord_563859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563876 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_563876 : Nat := 118140960795 + 563876 * 2 ^ 59
def prefixEnd_563876 : Nat := 4983230072969 + 3 ^ 40 * 563876 * 2
def baseEnd_563876 : Nat := 128684185570996029447461

theorem tailTrace_563876 : CollatzResearch.WordTrace tailWord_563876 prefixEnd_563876 128684185570996029447461 := by
  unfold tailWord_563876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283123652590514599443741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13710831536787352799258321 10283123652590514599443741)
  ·
    refine ⟨3856171369721442974791403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10283123652590514599443741 3856171369721442974791403)
    ·
      refine ⟨5784257054582164462187105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856171369721442974791403 5784257054582164462187105)
      ·
        refine ⟨4338192790936623346640329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5784257054582164462187105 4338192790936623346640329)
        ·
          refine ⟨3253644593202467509980247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4338192790936623346640329 3253644593202467509980247)
          ·
            refine ⟨4880466889803701264970371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253644593202467509980247 4880466889803701264970371)
            ·
              refine ⟨7320700334705551897455557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880466889803701264970371 7320700334705551897455557)
              ·
                refine ⟨1372631312757290980772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7320700334705551897455557 1372631312757290980772917)
                ·
                  refine ⟨128684185570996029447461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1372631312757290980772917 128684185570996029447461)
                  ·
                    rfl

theorem cell21_563876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_563876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563876 prefixEnd_563876 := by exact prefixLift 563876
  have htrace : WordTrace (prefixWord ++ tailWord_563876) baseStart_563876 baseEnd_563876 := by
    simpa [prefixWord, tailWord_563876, baseEnd_563876] using wordTrace_append hprefix tailTrace_563876
  have hstable : (prefixWord ++ tailWord_563876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563876).length < 2 ^ (prefixWord ++ tailWord_563876).sum := by decide
  have hdescent : baseEnd_563876 < baseStart_563876 := by decide
  rcases family_descends (prefixWord ++ tailWord_563876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563879 : List Nat := [1, 1, 6, 3, 1, 1, 1, 7]
def baseStart_563879 : Nat := 118140960795 + 563879 * 2 ^ 59
def prefixEnd_563879 : Nat := 4983230072969 + 3 ^ 40 * 563879 * 2
def baseEnd_563879 : Nat := 42894956737289563632485

theorem tailTrace_563879 : CollatzResearch.WordTrace tailWord_563879 prefixEnd_563879 42894956737289563632485 := by
  unfold tailWord_563879
  simp only [CollatzResearch.WordTrace]
  refine ⟨20566356724170160711246691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13710904482780107140831127 20566356724170160711246691)
  ·
    refine ⟨30849535086255241066870037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20566356724170160711246691 30849535086255241066870037)
    ·
      refine ⟨1446071957168214425009533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30849535086255241066870037 1446071957168214425009533)
      ·
        refine ⟨542276983938080409378575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1446071957168214425009533 542276983938080409378575)
        ·
          refine ⟨813415475907120614067863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542276983938080409378575 813415475907120614067863)
          ·
            refine ⟨1220123213860680921101795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813415475907120614067863 1220123213860680921101795)
            ·
              refine ⟨1830184820791021381652693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220123213860680921101795 1830184820791021381652693)
              ·
                refine ⟨42894956737289563632485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1830184820791021381652693 42894956737289563632485)
                ·
                  rfl

theorem cell21_563879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_563879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563879 prefixEnd_563879 := by exact prefixLift 563879
  have htrace : WordTrace (prefixWord ++ tailWord_563879) baseStart_563879 baseEnd_563879 := by
    simpa [prefixWord, tailWord_563879, baseEnd_563879] using wordTrace_append hprefix tailTrace_563879
  have hstable : (prefixWord ++ tailWord_563879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563879).length < 2 ^ (prefixWord ++ tailWord_563879).sum := by decide
  have hdescent : baseEnd_563879 < baseStart_563879 := by decide
  rcases family_descends (prefixWord ++ tailWord_563879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563921 : List Nat := [1, 2, 2, 1, 2, 3, 4, 6]
def baseStart_563921 : Nat := 118140960795 + 563921 * 2 ^ 59
def prefixEnd_563921 : Nat := 4983230072969 + 3 ^ 40 * 563921 * 2
def baseEnd_563921 : Nat := 42898151728028650399123

theorem tailTrace_563921 : CollatzResearch.WordTrace tailWord_563921 prefixEnd_563921 42898151728028650399123 := by
  unfold tailWord_563921
  simp only [CollatzResearch.WordTrace]
  refine ⟨20567888590018001884275617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13711925726678667922850411 20567888590018001884275617)
  ·
    refine ⟨15425916442513501413206713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20567888590018001884275617 15425916442513501413206713)
    ·
      refine ⟨11569437331885126059905035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15425916442513501413206713 11569437331885126059905035)
      ·
        refine ⟨17354155997827689089857553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11569437331885126059905035 17354155997827689089857553)
        ·
          refine ⟨13015616998370766817393165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17354155997827689089857553 13015616998370766817393165)
          ·
            refine ⟨4880856374389037556522437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13015616998370766817393165 4880856374389037556522437)
            ·
              refine ⟨915160570197944541847957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4880856374389037556522437 915160570197944541847957)
              ·
                refine ⟨42898151728028650399123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 915160570197944541847957 42898151728028650399123)
                ·
                  rfl

theorem cell21_563921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_563921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563921 prefixEnd_563921 := by exact prefixLift 563921
  have htrace : WordTrace (prefixWord ++ tailWord_563921) baseStart_563921 baseEnd_563921 := by
    simpa [prefixWord, tailWord_563921, baseEnd_563921] using wordTrace_append hprefix tailTrace_563921
  have hstable : (prefixWord ++ tailWord_563921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563921).length < 2 ^ (prefixWord ++ tailWord_563921).sum := by decide
  have hdescent : baseEnd_563921 < baseStart_563921 := by decide
  rcases family_descends (prefixWord ++ tailWord_563921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563986 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_563986 : Nat := 118140960795 + 563986 * 2 ^ 59
def prefixEnd_563986 : Nat := 4983230072969 + 3 ^ 40 * 563986 * 2
def baseEnd_563986 : Nat := 128709289069660282613903

theorem tailTrace_563986 : CollatzResearch.WordTrace tailWord_563986 prefixEnd_563986 128709289069660282613903 := by
  unfold tailWord_563986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142564833695629496347953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13713506223188345323594541 5142564833695629496347953)
  ·
    refine ⟨3856923625271722122260965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5142564833695629496347953 3856923625271722122260965)
    ·
      refine ⟨723173179738447897923931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3856923625271722122260965 723173179738447897923931)
      ·
        refine ⟨1084759769607671846885897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723173179738447897923931 1084759769607671846885897)
        ·
          refine ⟨813569827205753885164423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1084759769607671846885897 813569827205753885164423)
          ·
            refine ⟨1220354740808630827746635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813569827205753885164423 1220354740808630827746635)
            ·
              refine ⟨1830532111212946241619953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220354740808630827746635 1830532111212946241619953)
              ·
                refine ⟨1372899083409709681214965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830532111212946241619953 1372899083409709681214965)
                ·
                  refine ⟨128709289069660282613903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1372899083409709681214965 128709289069660282613903)
                  ·
                    rfl

theorem cell21_563986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_563986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_563986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_563986 prefixEnd_563986 := by exact prefixLift 563986
  have htrace : WordTrace (prefixWord ++ tailWord_563986) baseStart_563986 baseEnd_563986 := by
    simpa [prefixWord, tailWord_563986, baseEnd_563986] using wordTrace_append hprefix tailTrace_563986
  have hstable : (prefixWord ++ tailWord_563986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563986).length < 2 ^ (prefixWord ++ tailWord_563986).sum := by decide
  have hdescent : baseEnd_563986 < baseStart_563986 := by decide
  rcases family_descends (prefixWord ++ tailWord_563986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564014 : List Nat := [4, 1, 3, 2, 1, 2, 8]
def baseStart_564014 : Nat := 118140960795 + 564014 * 2 ^ 59
def prefixEnd_564014 : Nat := 4983230072969 + 3 ^ 40 * 564014 * 2
def baseEnd_564014 : Nat := 14301742116793161794131

theorem tailTrace_564014 : CollatzResearch.WordTrace tailWord_564014 prefixEnd_564014 14301742116793161794131 := by
  unfold tailWord_564014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571410072335134845926387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13714187052454052511607397 2571410072335134845926387)
  ·
    refine ⟨3857115108502702268889581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2571410072335134845926387 3857115108502702268889581)
    ·
      refine ⟨1446418165688513350833593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3857115108502702268889581 1446418165688513350833593)
      ·
        refine ⟨1084813624266385013125195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1446418165688513350833593 1084813624266385013125195)
        ·
          refine ⟨1627220436399577519687793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084813624266385013125195 1627220436399577519687793)
          ·
            refine ⟨1220415327299683139765845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627220436399577519687793 1220415327299683139765845)
            ·
              refine ⟨14301742116793161794131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1220415327299683139765845 14301742116793161794131)
              ·
                rfl

theorem cell21_564014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 8].length) (baseStart_564014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564014 prefixEnd_564014 := by exact prefixLift 564014
  have htrace : WordTrace (prefixWord ++ tailWord_564014) baseStart_564014 baseEnd_564014 := by
    simpa [prefixWord, tailWord_564014, baseEnd_564014] using wordTrace_append hprefix tailTrace_564014
  have hstable : (prefixWord ++ tailWord_564014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564014).length < 2 ^ (prefixWord ++ tailWord_564014).sum := by decide
  have hdescent : baseEnd_564014 < baseStart_564014 := by decide
  rcases family_descends (prefixWord ++ tailWord_564014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564163 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_564163 : Nat := 118140960795 + 564163 * 2 ^ 59
def prefixEnd_564163 : Nat := 4983230072969 + 3 ^ 40 * 564163 * 2
def baseEnd_564163 : Nat := 128749682881147308163541

theorem tailTrace_564163 : CollatzResearch.WordTrace tailWord_564163 prefixEnd_564163 128749682881147308163541 := by
  unfold tailWord_564163
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576715055141277214585143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13717810036760851476390095 20576715055141277214585143)
  ·
    refine ⟨30865072582711915821877715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20576715055141277214585143 30865072582711915821877715)
    ·
      refine ⟨46297608874067873732816573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30865072582711915821877715 46297608874067873732816573)
      ·
        refine ⟨17361603327775452649806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46297608874067873732816573 17361603327775452649806215)
        ·
          refine ⟨26042404991663178974709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17361603327775452649806215 26042404991663178974709323)
          ·
            refine ⟨39063607487494768462063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26042404991663178974709323 39063607487494768462063985)
            ·
              refine ⟨29297705615621076346547989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39063607487494768462063985 29297705615621076346547989)
              ·
                refine ⟨1373329950732237953744437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29297705615621076346547989 1373329950732237953744437)
                ·
                  refine ⟨128749682881147308163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373329950732237953744437 128749682881147308163541)
                  ·
                    rfl

theorem cell21_564163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_564163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564163 prefixEnd_564163 := by exact prefixLift 564163
  have htrace : WordTrace (prefixWord ++ tailWord_564163) baseStart_564163 baseEnd_564163 := by
    simpa [prefixWord, tailWord_564163, baseEnd_564163] using wordTrace_append hprefix tailTrace_564163
  have hstable : (prefixWord ++ tailWord_564163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564163).length < 2 ^ (prefixWord ++ tailWord_564163).sum := by decide
  have hdescent : baseEnd_564163 < baseStart_564163 := by decide
  rcases family_descends (prefixWord ++ tailWord_564163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564208 : List Nat := [2, 1, 1, 1, 3, 2, 1, 10]
def baseStart_564208 : Nat := 118140960795 + 564208 * 2 ^ 59
def prefixEnd_564208 : Nat := 4983230072969 + 3 ^ 40 * 564208 * 2
def baseEnd_564208 : Nat := 42919984164745743304483

theorem tailTrace_564208 : CollatzResearch.WordTrace tailWord_564208 prefixEnd_564208 42919984164745743304483 := by
  unfold tailWord_564208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289178169989124949986639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13718904226652166599982185 10289178169989124949986639)
  ·
    refine ⟨15433767254983687424979959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10289178169989124949986639 15433767254983687424979959)
    ·
      refine ⟨23150650882475531137469939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15433767254983687424979959 23150650882475531137469939)
      ·
        refine ⟨34725976323713296706204909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23150650882475531137469939 34725976323713296706204909)
        ·
          refine ⟨13022241121392486264826841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34725976323713296706204909 13022241121392486264826841)
          ·
            refine ⟨9766680841044364698620131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13022241121392486264826841 9766680841044364698620131)
            ·
              refine ⟨14650021261566547047930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9766680841044364698620131 14650021261566547047930197)
              ·
                refine ⟨42919984164745743304483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14650021261566547047930197 42919984164745743304483)
                ·
                  rfl

theorem cell21_564208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_564208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564208 prefixEnd_564208 := by exact prefixLift 564208
  have htrace : WordTrace (prefixWord ++ tailWord_564208) baseStart_564208 baseEnd_564208 := by
    simpa [prefixWord, tailWord_564208, baseEnd_564208] using wordTrace_append hprefix tailTrace_564208
  have hstable : (prefixWord ++ tailWord_564208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564208).length < 2 ^ (prefixWord ++ tailWord_564208).sum := by decide
  have hdescent : baseEnd_564208 < baseStart_564208 := by decide
  rcases family_descends (prefixWord ++ tailWord_564208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564225 : List Nat := [1, 2, 4, 1, 2, 3, 1, 7]
def baseStart_564225 : Nat := 118140960795 + 564225 * 2 ^ 59
def prefixEnd_564225 : Nat := 4983230072969 + 3 ^ 40 * 564225 * 2
def baseEnd_564225 : Nat := 42921277375282992710027

theorem tailTrace_564225 : CollatzResearch.WordTrace tailWord_564225 prefixEnd_564225 42921277375282992710027 := by
  unfold tailWord_564225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20578976380916661803342129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13719317587277774535561419 20578976380916661803342129)
  ·
    refine ⟨15434232285687496352506597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20578976380916661803342129 15434232285687496352506597)
    ·
      refine ⟨2893918553566405566094987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15434232285687496352506597 2893918553566405566094987)
      ·
        refine ⟨4340877830349608349142481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893918553566405566094987 4340877830349608349142481)
        ·
          refine ⟨3255658372762206261856861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340877830349608349142481 3255658372762206261856861)
          ·
            refine ⟨1220871889785827348196323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3255658372762206261856861 1220871889785827348196323)
            ·
              refine ⟨1831307834678741022294485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220871889785827348196323 1831307834678741022294485)
              ·
                refine ⟨42921277375282992710027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1831307834678741022294485 42921277375282992710027)
                ·
                  rfl

theorem cell21_564225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_564225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564225 prefixEnd_564225 := by exact prefixLift 564225
  have htrace : WordTrace (prefixWord ++ tailWord_564225) baseStart_564225 baseEnd_564225 := by
    simpa [prefixWord, tailWord_564225, baseEnd_564225] using wordTrace_append hprefix tailTrace_564225
  have hstable : (prefixWord ++ tailWord_564225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564225).length < 2 ^ (prefixWord ++ tailWord_564225).sum := by decide
  have hdescent : baseEnd_564225 < baseStart_564225 := by decide
  rcases family_descends (prefixWord ++ tailWord_564225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564301 : List Nat := [1, 6, 1, 1, 1, 11]
def baseStart_564301 : Nat := 118140960795 + 564301 * 2 ^ 59
def prefixEnd_564301 : Nat := 4983230072969 + 3 ^ 40 * 564301 * 2
def baseEnd_564301 : Nat := 4769673198566286476417

theorem tailTrace_564301 : CollatzResearch.WordTrace tailWord_564301 prefixEnd_564301 4769673198566286476417 := by
  unfold tailWord_564301
  simp only [CollatzResearch.WordTrace]
  refine ⟨20581748328641326783108757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13721165552427551188739171 20581748328641326783108757)
  ·
    refine ⟨964769452905062192958223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20581748328641326783108757 964769452905062192958223)
    ·
      refine ⟨1447154179357593289437335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964769452905062192958223 1447154179357593289437335)
      ·
        refine ⟨2170731269036389934156003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447154179357593289437335 2170731269036389934156003)
        ·
          refine ⟨3256096903554584901234005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170731269036389934156003 3256096903554584901234005)
          ·
            refine ⟨4769673198566286476417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3256096903554584901234005 4769673198566286476417)
            ·
              rfl

theorem cell21_564301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 11].length) (baseStart_564301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564301 prefixEnd_564301 := by exact prefixLift 564301
  have htrace : WordTrace (prefixWord ++ tailWord_564301) baseStart_564301 baseEnd_564301 := by
    simpa [prefixWord, tailWord_564301, baseEnd_564301] using wordTrace_append hprefix tailTrace_564301
  have hstable : (prefixWord ++ tailWord_564301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564301).length < 2 ^ (prefixWord ++ tailWord_564301).sum := by decide
  have hdescent : baseEnd_564301 < baseStart_564301 := by decide
  rcases family_descends (prefixWord ++ tailWord_564301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564349 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 3]
def baseStart_564349 : Nat := 118140960795 + 564349 * 2 ^ 59
def prefixEnd_564349 : Nat := 4983230072969 + 3 ^ 40 * 564349 * 2
def baseEnd_564349 : Nat := 128792130615252318063161

theorem tailTrace_564349 : CollatzResearch.WordTrace tailWord_564349 prefixEnd_564349 128792130615252318063161 := by
  unfold tailWord_564349
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583499032467430980856101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13722332688311620653904067 20583499032467430980856101)
  ·
    refine ⟨3859406068587643308910519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20583499032467430980856101 3859406068587643308910519)
    ·
      refine ⟨5789109102881464963365779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859406068587643308910519 5789109102881464963365779)
      ·
        refine ⟨8683663654322197445048669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5789109102881464963365779 8683663654322197445048669)
        ·
          refine ⟨3256373870370824041893251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8683663654322197445048669 3256373870370824041893251)
          ·
            refine ⟨4884560805556236062839877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256373870370824041893251 4884560805556236062839877)
            ·
              refine ⟨915855151041794261782477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4884560805556236062839877 915855151041794261782477)
              ·
                refine ⟨343445681640672848168429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915855151041794261782477 343445681640672848168429)
                ·
                  refine ⟨128792130615252318063161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343445681640672848168429 128792130615252318063161)
                  ·
                    rfl

theorem cell21_564349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_564349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564349 prefixEnd_564349 := by exact prefixLift 564349
  have htrace : WordTrace (prefixWord ++ tailWord_564349) baseStart_564349 baseEnd_564349 := by
    simpa [prefixWord, tailWord_564349, baseEnd_564349] using wordTrace_append hprefix tailTrace_564349
  have hstable : (prefixWord ++ tailWord_564349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564349).length < 2 ^ (prefixWord ++ tailWord_564349).sum := by decide
  have hdescent : baseEnd_564349 < baseStart_564349 := by decide
  rcases family_descends (prefixWord ++ tailWord_564349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564380 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_564380 : Nat := 118140960795 + 564380 * 2 ^ 59
def prefixEnd_564380 : Nat := 4983230072969 + 3 ^ 40 * 564380 * 2
def baseEnd_564380 : Nat := 128799205237603153046431

theorem tailTrace_564380 : CollatzResearch.WordTrace tailWord_564380 prefixEnd_564380 128799205237603153046431 := by
  unfold tailWord_564380
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292314847677561637617297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13723086463570082183489729 10292314847677561637617297)
  ·
    refine ⟨7719236135758171228212973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10292314847677561637617297 7719236135758171228212973)
    ·
      refine ⟨2894713550909314210579865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7719236135758171228212973 2894713550909314210579865)
      ·
        refine ⟨2171035163181985657934899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2894713550909314210579865 2171035163181985657934899)
        ·
          refine ⟨3256552744772978486902349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171035163181985657934899 3256552744772978486902349)
          ·
            refine ⟨1221207279289866932588381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3256552744772978486902349 1221207279289866932588381)
            ·
              refine ⟨457952729733700099720643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1221207279289866932588381 457952729733700099720643)
              ·
                refine ⟨686929094600550149580965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457952729733700099720643 686929094600550149580965)
                ·
                  refine ⟨128799205237603153046431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686929094600550149580965 128799205237603153046431)
                  ·
                    rfl

theorem cell21_564380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_564380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564380 prefixEnd_564380 := by exact prefixLift 564380
  have htrace : WordTrace (prefixWord ++ tailWord_564380) baseStart_564380 baseEnd_564380 := by
    simpa [prefixWord, tailWord_564380, baseEnd_564380] using wordTrace_append hprefix tailTrace_564380
  have hstable : (prefixWord ++ tailWord_564380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564380).length < 2 ^ (prefixWord ++ tailWord_564380).sum := by decide
  have hdescent : baseEnd_564380 < baseStart_564380 := by decide
  rcases family_descends (prefixWord ++ tailWord_564380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564394 : List Nat := [3, 1, 5, 1, 1, 2, 1, 7]
def baseStart_564394 : Nat := 118140960795 + 564394 * 2 ^ 59
def prefixEnd_564394 : Nat := 4983230072969 + 3 ^ 40 * 564394 * 2
def baseEnd_564394 : Nat := 42934133409447413271023

theorem tailTrace_564394 : CollatzResearch.WordTrace tailWord_564394 prefixEnd_564394 42934133409447413271023 := by
  unfold tailWord_564394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146285079326100916561059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13723426878202935777496157 5146285079326100916561059)
  ·
    refine ⟨7719427618989151374841589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5146285079326100916561059 7719427618989151374841589)
    ·
      refine ⟨723696339280232941391399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7719427618989151374841589 723696339280232941391399)
      ·
        refine ⟨1085544508920349412087099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723696339280232941391399 1085544508920349412087099)
        ·
          refine ⟨1628316763380524118130649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085544508920349412087099 1628316763380524118130649)
          ·
            refine ⟨1221237572535393088597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628316763380524118130649 1221237572535393088597987)
            ·
              refine ⟨1831856358803089632896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221237572535393088597987 1831856358803089632896981)
              ·
                refine ⟨42934133409447413271023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1831856358803089632896981 42934133409447413271023)
                ·
                  rfl

theorem cell21_564394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_564394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564394 prefixEnd_564394 := by exact prefixLift 564394
  have htrace : WordTrace (prefixWord ++ tailWord_564394) baseStart_564394 baseEnd_564394 := by
    simpa [prefixWord, tailWord_564394, baseEnd_564394] using wordTrace_append hprefix tailTrace_564394
  have hstable : (prefixWord ++ tailWord_564394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564394).length < 2 ^ (prefixWord ++ tailWord_564394).sum := by decide
  have hdescent : baseEnd_564394 < baseStart_564394 := by decide
  rcases family_descends (prefixWord ++ tailWord_564394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564408 : List Nat := [2, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_564408 : Nat := 118140960795 + 564408 * 2 ^ 59
def prefixEnd_564408 : Nat := 4983230072969 + 3 ^ 40 * 564408 * 2
def baseEnd_564408 : Nat := 128805595219081326579707

theorem tailTrace_564408 : CollatzResearch.WordTrace tailWord_564408 prefixEnd_564408 128805595219081326579707 := by
  unfold tailWord_564408
  simp only [CollatzResearch.WordTrace]
  refine ⟨10292825469626842028626939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13723767292835789371502585 10292825469626842028626939)
  ·
    refine ⟨15439238204440263042940409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10292825469626842028626939 15439238204440263042940409)
    ·
      refine ⟨11579428653330197282205307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15439238204440263042940409 11579428653330197282205307)
      ·
        refine ⟨17369142979995295923307961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11579428653330197282205307 17369142979995295923307961)
        ·
          refine ⟨13026857234996471942480971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17369142979995295923307961 13026857234996471942480971)
          ·
            refine ⟨19540285852494707913721457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13026857234996471942480971 19540285852494707913721457)
            ·
              refine ⟨14655214389371030935291093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19540285852494707913721457 14655214389371030935291093)
              ·
                refine ⟨343481587250883537545885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14655214389371030935291093 343481587250883537545885)
                ·
                  refine ⟨128805595219081326579707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343481587250883537545885 128805595219081326579707)
                  ·
                    rfl

theorem cell21_564408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_564408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564408 prefixEnd_564408 := by exact prefixLift 564408
  have htrace : WordTrace (prefixWord ++ tailWord_564408) baseStart_564408 baseEnd_564408 := by
    simpa [prefixWord, tailWord_564408, baseEnd_564408] using wordTrace_append hprefix tailTrace_564408
  have hstable : (prefixWord ++ tailWord_564408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564408).length < 2 ^ (prefixWord ++ tailWord_564408).sum := by decide
  have hdescent : baseEnd_564408 < baseStart_564408 := by decide
  rcases family_descends (prefixWord ++ tailWord_564408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564439 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 4]
def baseStart_564439 : Nat := 118140960795 + 564439 * 2 ^ 59
def prefixEnd_564439 : Nat := 4983230072969 + 3 ^ 40 * 564439 * 2
def baseEnd_564439 : Nat := 128812669841432161562977

theorem tailTrace_564439 : CollatzResearch.WordTrace tailWord_564439 prefixEnd_564439 128812669841432161562977 := by
  unfold tailWord_564439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586781602141376351632371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13724521068094250901088247 20586781602141376351632371)
  ·
    refine ⟨30880172403212064527448557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20586781602141376351632371 30880172403212064527448557)
    ·
      refine ⟨11580064651204524197793209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30880172403212064527448557 11580064651204524197793209)
      ·
        refine ⟨8685048488403393148344907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11580064651204524197793209 8685048488403393148344907)
        ·
          refine ⟨13027572732605089722517361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685048488403393148344907 13027572732605089722517361)
          ·
            refine ⟨9770679549453817291888021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13027572732605089722517361 9770679549453817291888021)
            ·
              refine ⟨458000603880647685557251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9770679549453817291888021 458000603880647685557251)
              ·
                refine ⟨687000905820971528335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458000603880647685557251 687000905820971528335877)
                ·
                  refine ⟨128812669841432161562977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687000905820971528335877 128812669841432161562977)
                  ·
                    rfl

theorem cell21_564439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_564439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564439 prefixEnd_564439 := by exact prefixLift 564439
  have htrace : WordTrace (prefixWord ++ tailWord_564439) baseStart_564439 baseEnd_564439 := by
    simpa [prefixWord, tailWord_564439, baseEnd_564439] using wordTrace_append hprefix tailTrace_564439
  have hstable : (prefixWord ++ tailWord_564439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564439).length < 2 ^ (prefixWord ++ tailWord_564439).sum := by decide
  have hdescent : baseEnd_564439 < baseStart_564439 := by decide
  rcases family_descends (prefixWord ++ tailWord_564439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564543 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 5]
def baseStart_564543 : Nat := 118140960795 + 564543 * 2 ^ 59
def prefixEnd_564543 : Nat := 4983230072969 + 3 ^ 40 * 564543 * 2
def baseEnd_564543 : Nat := 128836404058351091829431

theorem tailTrace_564543 : CollatzResearch.WordTrace tailWord_564543 prefixEnd_564543 128836404058351091829431 := by
  unfold tailWord_564543
  simp only [CollatzResearch.WordTrace]
  refine ⟨20590574793764602113418283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13727049862509734742278855 20590574793764602113418283)
  ·
    refine ⟨30885862190646903170127425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20590574793764602113418283 30885862190646903170127425)
    ·
      refine ⟨23164396642985177377595569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30885862190646903170127425 23164396642985177377595569)
      ·
        refine ⟨17373297482238883033196677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23164396642985177377595569 17373297482238883033196677)
        ·
          refine ⟨3257493277919790568724377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17373297482238883033196677 3257493277919790568724377)
          ·
            refine ⟨2443119958439842926543283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3257493277919790568724377 2443119958439842926543283)
            ·
              refine ⟨3664679937659764389814925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443119958439842926543283 3664679937659764389814925)
              ·
                refine ⟨1374254976622411646180597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3664679937659764389814925 1374254976622411646180597)
                ·
                  refine ⟨128836404058351091829431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1374254976622411646180597 128836404058351091829431)
                  ·
                    rfl

theorem cell21_564543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_564543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564543 prefixEnd_564543 := by exact prefixLift 564543
  have htrace : WordTrace (prefixWord ++ tailWord_564543) baseStart_564543 baseEnd_564543 := by
    simpa [prefixWord, tailWord_564543, baseEnd_564543] using wordTrace_append hprefix tailTrace_564543
  have hstable : (prefixWord ++ tailWord_564543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564543).length < 2 ^ (prefixWord ++ tailWord_564543).sum := by decide
  have hdescent : baseEnd_564543 < baseStart_564543 := by decide
  rcases family_descends (prefixWord ++ tailWord_564543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564588 : List Nat := [2, 2, 1, 1, 5, 1, 9]
def baseStart_564588 : Nat := 118140960795 + 564588 * 2 ^ 59
def prefixEnd_564588 : Nat := 4983230072969 + 3 ^ 40 * 564588 * 2
def baseEnd_564588 : Nat := 14316297074604557064371

theorem tailTrace_564588 : CollatzResearch.WordTrace tailWord_564588 prefixEnd_564588 14316297074604557064371 := by
  unfold tailWord_564588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296108039300787399403209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13728144052401049865870945 10296108039300787399403209)
  ·
    refine ⟨7722081029475590549552407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10296108039300787399403209 7722081029475590549552407)
    ·
      refine ⟨11583121544213385824328611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7722081029475590549552407 11583121544213385824328611)
      ·
        refine ⟨17374682316320078736492917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11583121544213385824328611 17374682316320078736492917)
        ·
          refine ⟨1628876467155007381546211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17374682316320078736492917 1628876467155007381546211)
          ·
            refine ⟨2443314700732511072319317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628876467155007381546211 2443314700732511072319317)
            ·
              refine ⟨14316297074604557064371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2443314700732511072319317 14316297074604557064371)
              ·
                rfl

theorem cell21_564588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 9].length) (baseStart_564588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564588 prefixEnd_564588 := by exact prefixLift 564588
  have htrace : WordTrace (prefixWord ++ tailWord_564588) baseStart_564588 baseEnd_564588 := by
    simpa [prefixWord, tailWord_564588, baseEnd_564588] using wordTrace_append hprefix tailTrace_564588
  have hstable : (prefixWord ++ tailWord_564588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564588).length < 2 ^ (prefixWord ++ tailWord_564588).sum := by decide
  have hdescent : baseEnd_564588 < baseStart_564588 := by decide
  rcases family_descends (prefixWord ++ tailWord_564588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564664 : List Nat := [2, 1, 2, 1, 2, 2, 5, 6]
def baseStart_564664 : Nat := 118140960795 + 564664 * 2 ^ 59
def prefixEnd_564664 : Nat := 4983230072969 + 3 ^ 40 * 564664 * 2
def baseEnd_564664 : Nat := 42954672635627256770839

theorem tailTrace_564664 : CollatzResearch.WordTrace tailWord_564664 prefixEnd_564664 42954672635627256770839 := by
  unfold tailWord_564664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297494013163119889286523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13729992017550826519048697 10297494013163119889286523)
  ·
    refine ⟨15446241019744679833929785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10297494013163119889286523 15446241019744679833929785)
    ·
      refine ⟨11584680764808509875447339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15446241019744679833929785 11584680764808509875447339)
      ·
        refine ⟨17377021147212764813171009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11584680764808509875447339 17377021147212764813171009)
        ·
          refine ⟨13032765860409573609878257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17377021147212764813171009 13032765860409573609878257)
          ·
            refine ⟨9774574395307180207408693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13032765860409573609878257 9774574395307180207408693)
            ·
              refine ⟨916366349560048144444565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9774574395307180207408693 916366349560048144444565)
              ·
                refine ⟨42954672635627256770839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 916366349560048144444565 42954672635627256770839)
                ·
                  rfl

theorem cell21_564664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_564664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564664 prefixEnd_564664 := by exact prefixLift 564664
  have htrace : WordTrace (prefixWord ++ tailWord_564664) baseStart_564664 baseEnd_564664 := by
    simpa [prefixWord, tailWord_564664, baseEnd_564664] using wordTrace_append hprefix tailTrace_564664
  have hstable : (prefixWord ++ tailWord_564664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564664).length < 2 ^ (prefixWord ++ tailWord_564664).sum := by decide
  have hdescent : baseEnd_564664 < baseStart_564664 := by decide
  rcases family_descends (prefixWord ++ tailWord_564664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564712 : List Nat := [2, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_564712 : Nat := 118140960795 + 564712 * 2 ^ 59
def prefixEnd_564712 : Nat := 4983230072969 + 3 ^ 40 * 564712 * 2
def baseEnd_564712 : Nat := 128874972160844353512419

theorem tailTrace_564712 : CollatzResearch.WordTrace tailWord_564712 prefixEnd_564712 128874972160844353512419 := by
  unfold tailWord_564712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10298369365076171988160195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13731159153434895984213593 10298369365076171988160195)
  ·
    refine ⟨15447554047614257982240293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10298369365076171988160195 15447554047614257982240293)
    ·
      refine ⟨2896416383927673371670055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15447554047614257982240293 2896416383927673371670055)
      ·
        refine ⟨4344624575891510057505083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896416383927673371670055 4344624575891510057505083)
        ·
          refine ⟨6516936863837265086257625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344624575891510057505083 6516936863837265086257625)
          ·
            refine ⟨4887702647877948814693219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6516936863837265086257625 4887702647877948814693219)
            ·
              refine ⟨7331553971816923222039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887702647877948814693219 7331553971816923222039829)
              ·
                refine ⟨343666592428918276033117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7331553971816923222039829 343666592428918276033117)
                ·
                  refine ⟨128874972160844353512419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343666592428918276033117 128874972160844353512419)
                  ·
                    rfl

theorem cell21_564712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_564712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564712 prefixEnd_564712 := by exact prefixLift 564712
  have htrace : WordTrace (prefixWord ++ tailWord_564712) baseStart_564712 baseEnd_564712 := by
    simpa [prefixWord, tailWord_564712, baseEnd_564712] using wordTrace_append hprefix tailTrace_564712
  have hstable : (prefixWord ++ tailWord_564712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564712).length < 2 ^ (prefixWord ++ tailWord_564712).sum := by decide
  have hdescent : baseEnd_564712 < baseStart_564712 := by decide
  rcases family_descends (prefixWord ++ tailWord_564712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564864 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_564864 : Nat := 118140960795 + 564864 * 2 ^ 59
def prefixEnd_564864 : Nat := 4983230072969 + 3 ^ 40 * 564864 * 2
def baseEnd_564864 : Nat := 128909660631725866978775

theorem tailTrace_564864 : CollatzResearch.WordTrace tailWord_564864 prefixEnd_564864 128909660631725866978775 := by
  unfold tailWord_564864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301141312800836967926823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13734855083734449290569097 10301141312800836967926823)
  ·
    refine ⟨15451711969201255451890235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10301141312800836967926823 15451711969201255451890235)
    ·
      refine ⟨23177567953801883177835353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451711969201255451890235 23177567953801883177835353)
      ·
        refine ⟨17383175965351412383376515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23177567953801883177835353 17383175965351412383376515)
        ·
          refine ⟨26074763948027118575064773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17383175965351412383376515 26074763948027118575064773)
          ·
            refine ⟨4889018240255084732824645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26074763948027118575064773 4889018240255084732824645)
            ·
              refine ⟨916690920047828387404621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4889018240255084732824645 916690920047828387404621)
              ·
                refine ⟨343759095017935645276733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916690920047828387404621 343759095017935645276733)
                ·
                  refine ⟨128909660631725866978775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343759095017935645276733 128909660631725866978775)
                  ·
                    rfl

theorem cell21_564864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_564864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564864 prefixEnd_564864 := by exact prefixLift 564864
  have htrace : WordTrace (prefixWord ++ tailWord_564864) baseStart_564864 baseEnd_564864 := by
    simpa [prefixWord, tailWord_564864, baseEnd_564864] using wordTrace_append hprefix tailTrace_564864
  have hstable : (prefixWord ++ tailWord_564864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564864).length < 2 ^ (prefixWord ++ tailWord_564864).sum := by decide
  have hdescent : baseEnd_564864 < baseStart_564864 := by decide
  rcases family_descends (prefixWord ++ tailWord_564864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564875 : List Nat := [1, 1, 1, 1, 4, 1, 12]
def baseStart_564875 : Nat := 118140960795 + 564875 * 2 ^ 59
def prefixEnd_564875 : Nat := 4983230072969 + 3 ^ 40 * 564875 * 2
def baseEnd_564875 : Nat := 14323574553510254699491

theorem tailTrace_564875 : CollatzResearch.WordTrace tailWord_564875 prefixEnd_564875 14323574553510254699491 := by
  unfold tailWord_564875
  simp only [CollatzResearch.WordTrace]
  refine ⟨20602683828561822814504079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13735122552374548543002719 20602683828561822814504079)
  ·
    refine ⟨30904025742842734221756119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20602683828561822814504079 30904025742842734221756119)
    ·
      refine ⟨46356038614264101332634179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30904025742842734221756119 46356038614264101332634179)
      ·
        refine ⟨69534057921396151998951269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46356038614264101332634179 69534057921396151998951269)
        ·
          refine ⟨13037635860261778499803363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69534057921396151998951269 13037635860261778499803363)
          ·
            refine ⟨19556453790392667749705045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037635860261778499803363 19556453790392667749705045)
            ·
              refine ⟨14323574553510254699491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19556453790392667749705045 14323574553510254699491)
              ·
                rfl

theorem cell21_564875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 12].length) (baseStart_564875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564875 prefixEnd_564875 := by exact prefixLift 564875
  have htrace : WordTrace (prefixWord ++ tailWord_564875) baseStart_564875 baseEnd_564875 := by
    simpa [prefixWord, tailWord_564875, baseEnd_564875] using wordTrace_append hprefix tailTrace_564875
  have hstable : (prefixWord ++ tailWord_564875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564875).length < 2 ^ (prefixWord ++ tailWord_564875).sum := by decide
  have hdescent : baseEnd_564875 < baseStart_564875 := by decide
  rcases family_descends (prefixWord ++ tailWord_564875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564878 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_564878 : Nat := 118140960795 + 564878 * 2 ^ 59
def prefixEnd_564878 : Nat := 4983230072969 + 3 ^ 40 * 564878 * 2
def baseEnd_564878 : Nat := 128912855622464953745413

theorem tailTrace_564878 : CollatzResearch.WordTrace tailWord_564878 prefixEnd_564878 128912855622464953745413 := by
  unfold tailWord_564878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575349155943869290857911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13735195498367302884575525 2575349155943869290857911)
  ·
    refine ⟨3863023733915803936286867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575349155943869290857911 3863023733915803936286867)
    ·
      refine ⟨5794535600873705904430301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863023733915803936286867 5794535600873705904430301)
      ·
        refine ⟨2172950850327639714161363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5794535600873705904430301 2172950850327639714161363)
        ·
          refine ⟨3259426275491459571242045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172950850327639714161363 3259426275491459571242045)
          ·
            refine ⟨1222284853309297339215767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3259426275491459571242045 1222284853309297339215767)
            ·
              refine ⟨1833427279963946008823651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222284853309297339215767 1833427279963946008823651)
              ·
                refine ⟨2750140919945919013235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833427279963946008823651 2750140919945919013235477)
                ·
                  refine ⟨128912855622464953745413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2750140919945919013235477 128912855622464953745413)
                  ·
                    rfl

theorem cell21_564878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_564878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564878 prefixEnd_564878 := by exact prefixLift 564878
  have htrace : WordTrace (prefixWord ++ tailWord_564878) baseStart_564878 baseEnd_564878 := by
    simpa [prefixWord, tailWord_564878, baseEnd_564878] using wordTrace_append hprefix tailTrace_564878
  have hstable : (prefixWord ++ tailWord_564878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564878).length < 2 ^ (prefixWord ++ tailWord_564878).sum := by decide
  have hdescent : baseEnd_564878 < baseStart_564878 := by decide
  rcases family_descends (prefixWord ++ tailWord_564878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564954 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_564954 : Nat := 118140960795 + 564954 * 2 ^ 59
def prefixEnd_564954 : Nat := 4983230072969 + 3 ^ 40 * 564954 * 2
def baseEnd_564954 : Nat := 128930199857905710478591

theorem tailTrace_564954 : CollatzResearch.WordTrace tailWord_564954 prefixEnd_564954 128930199857905710478591 := by
  unfold tailWord_564954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151391298818904826657479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13737043463517079537753277 5151391298818904826657479)
  ·
    refine ⟨7727086948228357239986219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5151391298818904826657479 7727086948228357239986219)
    ·
      refine ⟨11590630422342535859979329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727086948228357239986219 11590630422342535859979329)
      ·
        refine ⟨8692972816756901894984497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11590630422342535859979329 8692972816756901894984497)
        ·
          refine ⟨6519729612567676421238373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8692972816756901894984497 6519729612567676421238373)
          ·
            refine ⟨1222449302356439328982195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6519729612567676421238373 1222449302356439328982195)
            ·
              refine ⟨1833673953534658993473293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222449302356439328982195 1833673953534658993473293)
              ·
                refine ⟨687627732575497122552485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1833673953534658993473293 687627732575497122552485)
                ·
                  refine ⟨128930199857905710478591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687627732575497122552485 128930199857905710478591)
                  ·
                    rfl

theorem cell21_564954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_564954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564954 prefixEnd_564954 := by exact prefixLift 564954
  have htrace : WordTrace (prefixWord ++ tailWord_564954) baseStart_564954 baseEnd_564954 := by
    simpa [prefixWord, tailWord_564954, baseEnd_564954] using wordTrace_append hprefix tailTrace_564954
  have hstable : (prefixWord ++ tailWord_564954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564954).length < 2 ^ (prefixWord ++ tailWord_564954).sum := by decide
  have hdescent : baseEnd_564954 < baseStart_564954 := by decide
  rcases family_descends (prefixWord ++ tailWord_564954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564968 : List Nat := [2, 1, 4, 1, 3, 1, 2, 7]
def baseStart_564968 : Nat := 118140960795 + 564968 * 2 ^ 59
def prefixEnd_564968 : Nat := 4983230072969 + 3 ^ 40 * 564968 * 2
def baseEnd_564968 : Nat := 42977798282881599081743

theorem tailTrace_564968 : CollatzResearch.WordTrace tailWord_564968 prefixEnd_564968 42977798282881599081743 := by
  unfold tailWord_564968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303037908612449848819779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13737383878149933131759705 10303037908612449848819779)
  ·
    refine ⟨15454556862918674773229669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10303037908612449848819779 15454556862918674773229669)
    ·
      refine ⟨2897729411797251519980563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15454556862918674773229669 2897729411797251519980563)
      ·
        refine ⟨4346594117695877279970845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897729411797251519980563 4346594117695877279970845)
        ·
          refine ⟨1629972794135953979989067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4346594117695877279970845 1629972794135953979989067)
          ·
            refine ⟨2444959191203930969983601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629972794135953979989067 2444959191203930969983601)
            ·
              refine ⟨1833719393402948227487701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2444959191203930969983601 1833719393402948227487701)
              ·
                refine ⟨42977798282881599081743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1833719393402948227487701 42977798282881599081743)
                ·
                  rfl

theorem cell21_564968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_564968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_564968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_564968 prefixEnd_564968 := by exact prefixLift 564968
  have htrace : WordTrace (prefixWord ++ tailWord_564968) baseStart_564968 baseEnd_564968 := by
    simpa [prefixWord, tailWord_564968, baseEnd_564968] using wordTrace_append hprefix tailTrace_564968
  have hstable : (prefixWord ++ tailWord_564968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564968).length < 2 ^ (prefixWord ++ tailWord_564968).sum := by decide
  have hdescent : baseEnd_564968 < baseStart_564968 := by decide
  rcases family_descends (prefixWord ++ tailWord_564968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565027 : List Nat := [1, 1, 1, 4, 2, 1, 2, 9]
def baseStart_565027 : Nat := 118140960795 + 565027 * 2 ^ 59
def prefixEnd_565027 : Nat := 4983230072969 + 3 ^ 40 * 565027 * 2
def baseEnd_565027 : Nat := 42982286484157935253925

theorem tailTrace_565027 : CollatzResearch.WordTrace tailWord_565027 prefixEnd_565027 42982286484157935253925 := by
  unfold tailWord_565027
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608227724011152774037335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13738818482674101849358223 20608227724011152774037335)
  ·
    refine ⟨30912341586016729161056003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20608227724011152774037335 30912341586016729161056003)
    ·
      refine ⟨46368512379025093741584005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30912341586016729161056003 46368512379025093741584005)
      ·
        refine ⟨8694096071067205076547001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46368512379025093741584005 8694096071067205076547001)
        ·
          refine ⟨6520572053300403807410251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8694096071067205076547001 6520572053300403807410251)
          ·
            refine ⟨9780858079950605711115377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520572053300403807410251 9780858079950605711115377)
            ·
              refine ⟨7335643559962954283336533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9780858079950605711115377 7335643559962954283336533)
              ·
                refine ⟨42982286484157935253925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7335643559962954283336533 42982286484157935253925)
                ·
                  rfl

theorem cell21_565027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_565027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565027 prefixEnd_565027 := by exact prefixLift 565027
  have htrace : WordTrace (prefixWord ++ tailWord_565027) baseStart_565027 baseEnd_565027 := by
    simpa [prefixWord, tailWord_565027, baseEnd_565027] using wordTrace_append hprefix tailTrace_565027
  have hstable : (prefixWord ++ tailWord_565027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565027).length < 2 ^ (prefixWord ++ tailWord_565027).sum := by decide
  have hdescent : baseEnd_565027 < baseStart_565027 := by decide
  rcases family_descends (prefixWord ++ tailWord_565027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565109 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 3]
def baseStart_565109 : Nat := 118140960795 + 565109 * 2 ^ 59
def prefixEnd_565109 : Nat := 4983230072969 + 3 ^ 40 * 565109 * 2
def baseEnd_565109 : Nat := 128965572969659885394941

theorem tailTrace_565109 : CollatzResearch.WordTrace tailWord_565109 prefixEnd_565109 128965572969659885394941 := by
  unfold tailWord_565109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611218509714080778522381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13740812339809387185681587 20611218509714080778522381)
  ·
    refine ⟨7729206941142780291945893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20611218509714080778522381 7729206941142780291945893)
    ·
      refine ⟨1449226301464271304739855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7729206941142780291945893 1449226301464271304739855)
      ·
        refine ⟨2173839452196406957109783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449226301464271304739855 2173839452196406957109783)
        ·
          refine ⟨3260759178294610435664675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173839452196406957109783 3260759178294610435664675)
          ·
            refine ⟨4891138767441915653497013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260759178294610435664675 4891138767441915653497013)
            ·
              refine ⟨458544259447679592515345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4891138767441915653497013 458544259447679592515345)
              ·
                refine ⟨343908194585759694386509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458544259447679592515345 343908194585759694386509)
                ·
                  refine ⟨128965572969659885394941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343908194585759694386509 128965572969659885394941)
                  ·
                    rfl

theorem cell21_565109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_565109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565109 prefixEnd_565109 := by exact prefixLift 565109
  have htrace : WordTrace (prefixWord ++ tailWord_565109) baseStart_565109 baseEnd_565109 := by
    simpa [prefixWord, tailWord_565109, baseEnd_565109] using wordTrace_append hprefix tailTrace_565109
  have hstable : (prefixWord ++ tailWord_565109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565109).length < 2 ^ (prefixWord ++ tailWord_565109).sum := by decide
  have hdescent : baseEnd_565109 < baseStart_565109 := by decide
  rcases family_descends (prefixWord ++ tailWord_565109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565123 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 4]
def baseStart_565123 : Nat := 118140960795 + 565123 * 2 ^ 59
def prefixEnd_565123 : Nat := 4983230072969 + 3 ^ 40 * 565123 * 2
def baseEnd_565123 : Nat := 128968767960398972161579

theorem tailTrace_565123 : CollatzResearch.WordTrace tailWord_565123 prefixEnd_565123 128968767960398972161579 := by
  unfold tailWord_565123
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611729131663361169532023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13741152754442240779688015 20611729131663361169532023)
  ·
    refine ⟨30917593697495041754298035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20611729131663361169532023 30917593697495041754298035)
    ·
      refine ⟨46376390546242562631447053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30917593697495041754298035 46376390546242562631447053)
      ·
        refine ⟨17391146454840960986792645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46376390546242562631447053 17391146454840960986792645)
        ·
          refine ⟨3260839960282680185023621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17391146454840960986792645 3260839960282680185023621)
          ·
            refine ⟨611407492553002534691929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3260839960282680185023621 611407492553002534691929)
            ·
              refine ⟨458555619414751901018947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611407492553002534691929 458555619414751901018947)
              ·
                refine ⟨687833429122127851528421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458555619414751901018947 687833429122127851528421)
                ·
                  refine ⟨128968767960398972161579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687833429122127851528421 128968767960398972161579)
                  ·
                    rfl

theorem cell21_565123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_565123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565123 prefixEnd_565123 := by exact prefixLift 565123
  have htrace : WordTrace (prefixWord ++ tailWord_565123) baseStart_565123 baseEnd_565123 := by
    simpa [prefixWord, tailWord_565123, baseEnd_565123] using wordTrace_append hprefix tailTrace_565123
  have hstable : (prefixWord ++ tailWord_565123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565123).length < 2 ^ (prefixWord ++ tailWord_565123).sum := by decide
  have hdescent : baseEnd_565123 < baseStart_565123 := by decide
  rcases family_descends (prefixWord ++ tailWord_565123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565160 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_565160 : Nat := 118140960795 + 565160 * 2 ^ 59
def prefixEnd_565160 : Nat := 4983230072969 + 3 ^ 40 * 565160 * 2
def baseEnd_565160 : Nat := 128977211864495130044837

theorem tailTrace_565160 : CollatzResearch.WordTrace tailWord_565160 prefixEnd_565160 128977211864495130044837 := by
  unfold tailWord_565160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306539316264658244314467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13742052421686210992419289 10306539316264658244314467)
  ·
    refine ⟨15459808974396987366471701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10306539316264658244314467 15459808974396987366471701)
    ·
      refine ⟨724678545674858782803361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15459808974396987366471701 724678545674858782803361)
      ·
        refine ⟨543508909256144087102521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724678545674858782803361 543508909256144087102521)
        ·
          refine ⟨407631681942108065326891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543508909256144087102521 407631681942108065326891)
          ·
            refine ⟨611447522913162097990337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407631681942108065326891 611447522913162097990337)
            ·
              refine ⟨458585642184871573492753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611447522913162097990337 458585642184871573492753)
              ·
                refine ⟨343939231638653680119565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458585642184871573492753 343939231638653680119565)
                ·
                  refine ⟨128977211864495130044837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343939231638653680119565 128977211864495130044837)
                  ·
                    rfl

theorem cell21_565160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_565160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565160 prefixEnd_565160 := by exact prefixLift 565160
  have htrace : WordTrace (prefixWord ++ tailWord_565160) baseStart_565160 baseEnd_565160 := by
    simpa [prefixWord, tailWord_565160, baseEnd_565160] using wordTrace_append hprefix tailTrace_565160
  have hstable : (prefixWord ++ tailWord_565160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565160).length < 2 ^ (prefixWord ++ tailWord_565160).sum := by decide
  have hdescent : baseEnd_565160 < baseStart_565160 := by decide
  rcases family_descends (prefixWord ++ tailWord_565160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565182 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_565182 : Nat := 118140960795 + 565182 * 2 ^ 59
def prefixEnd_565182 : Nat := 4983230072969 + 3 ^ 40 * 565182 * 2
def baseEnd_565182 : Nat := 128982232564227980678125

theorem tailTrace_565182 : CollatzResearch.WordTrace tailWord_565182 prefixEnd_565182 128982232564227980678125 := by
  unfold tailWord_565182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576735129806201780741225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13742587358966409497286533 2576735129806201780741225)
  ·
    refine ⟨1932551347354651335555919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576735129806201780741225 1932551347354651335555919)
    ·
      refine ⟨2898827021031977003333879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932551347354651335555919 2898827021031977003333879)
      ·
        refine ⟨4348240531547965505000819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898827021031977003333879 4348240531547965505000819)
        ·
          refine ⟨6522360797321948257501229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348240531547965505000819 6522360797321948257501229)
          ·
            refine ⟨2445885298995730596562961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6522360797321948257501229 2445885298995730596562961)
            ·
              refine ⟨1834413974246797947422221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445885298995730596562961 1834413974246797947422221)
              ·
                refine ⟨687905240342549230283333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1834413974246797947422221 687905240342549230283333)
                ·
                  refine ⟨128982232564227980678125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687905240342549230283333 128982232564227980678125)
                  ·
                    rfl

theorem cell21_565182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_565182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565182 prefixEnd_565182 := by exact prefixLift 565182
  have htrace : WordTrace (prefixWord ++ tailWord_565182) baseStart_565182 baseEnd_565182 := by
    simpa [prefixWord, tailWord_565182, baseEnd_565182] using wordTrace_append hprefix tailTrace_565182
  have hstable : (prefixWord ++ tailWord_565182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565182).length < 2 ^ (prefixWord ++ tailWord_565182).sum := by decide
  have hdescent : baseEnd_565182 < baseStart_565182 := by decide
  rcases family_descends (prefixWord ++ tailWord_565182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565362 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_565362 : Nat := 118140960795 + 565362 * 2 ^ 59
def prefixEnd_565362 : Nat := 4983230072969 + 3 ^ 40 * 565362 * 2
def baseEnd_565362 : Nat := 129023311016587667677757

theorem tailTrace_565362 : CollatzResearch.WordTrace tailWord_565362 prefixEnd_565362 129023311016587667677757 := by
  unfold tailWord_565362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155111544449376246870585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13746964118531669991654893 5155111544449376246870585)
  ·
    refine ⟨3866333658337032185152939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5155111544449376246870585 3866333658337032185152939)
    ·
      refine ⟨5799500487505548277729409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866333658337032185152939 5799500487505548277729409)
      ·
        refine ⟨4349625365629161208297057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5799500487505548277729409 4349625365629161208297057)
        ·
          refine ⟨3262219024221870906222793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4349625365629161208297057 3262219024221870906222793)
          ·
            refine ⟨2446664268166403179667095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3262219024221870906222793 2446664268166403179667095)
            ·
              refine ⟨3669996402249604769500643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446664268166403179667095 3669996402249604769500643)
              ·
                refine ⟨5504994603374407154250965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669996402249604769500643 5504994603374407154250965)
                ·
                  refine ⟨129023311016587667677757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5504994603374407154250965 129023311016587667677757)
                  ·
                    rfl

theorem cell21_565362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_565362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565362 prefixEnd_565362 := by exact prefixLift 565362
  have htrace : WordTrace (prefixWord ++ tailWord_565362) baseStart_565362 baseEnd_565362 := by
    simpa [prefixWord, tailWord_565362, baseEnd_565362] using wordTrace_append hprefix tailTrace_565362
  have hstable : (prefixWord ++ tailWord_565362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565362).length < 2 ^ (prefixWord ++ tailWord_565362).sum := by decide
  have hdescent : baseEnd_565362 < baseStart_565362 := by decide
  rcases family_descends (prefixWord ++ tailWord_565362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565376 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_565376 : Nat := 118140960795 + 565376 * 2 ^ 59
def prefixEnd_565376 : Nat := 4983230072969 + 3 ^ 40 * 565376 * 2
def baseEnd_565376 : Nat := 129026506007326754444395

theorem tailTrace_565376 : CollatzResearch.WordTrace tailWord_565376 prefixEnd_565376 129026506007326754444395 := by
  unfold tailWord_565376
  simp only [CollatzResearch.WordTrace]
  refine ⟨10310478399873392689245991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13747304533164523585661321 10310478399873392689245991)
  ·
    refine ⟨15465717599810089033868987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10310478399873392689245991 15465717599810089033868987)
    ·
      refine ⟨23198576399715133550803481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15465717599810089033868987 23198576399715133550803481)
      ·
        refine ⟨17398932299786350163102611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23198576399715133550803481 17398932299786350163102611)
        ·
          refine ⟨26098398449679525244653917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17398932299786350163102611 26098398449679525244653917)
          ·
            refine ⟨9786899418629821966745219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26098398449679525244653917 9786899418629821966745219)
            ·
              refine ⟨14680349127944732950117829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9786899418629821966745219 14680349127944732950117829)
              ·
                refine ⟨2752565461489637428147093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14680349127944732950117829 2752565461489637428147093)
                ·
                  refine ⟨129026506007326754444395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2752565461489637428147093 129026506007326754444395)
                  ·
                    rfl

theorem cell21_565376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_565376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565376 prefixEnd_565376 := by exact prefixLift 565376
  have htrace : WordTrace (prefixWord ++ tailWord_565376) baseStart_565376 baseEnd_565376 := by
    simpa [prefixWord, tailWord_565376, baseEnd_565376] using wordTrace_append hprefix tailTrace_565376
  have hstable : (prefixWord ++ tailWord_565376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565376).length < 2 ^ (prefixWord ++ tailWord_565376).sum := by decide
  have hdescent : baseEnd_565376 < baseStart_565376 := by decide
  rcases family_descends (prefixWord ++ tailWord_565376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565379 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 3]
def baseStart_565379 : Nat := 118140960795 + 565379 * 2 ^ 59
def prefixEnd_565379 : Nat := 4983230072969 + 3 ^ 40 * 565379 * 2
def baseEnd_565379 : Nat := 129027190648199415894389

theorem tailTrace_565379 : CollatzResearch.WordTrace tailWord_565379 prefixEnd_565379 129027190648199415894389 := by
  unfold tailWord_565379
  simp only [CollatzResearch.WordTrace]
  refine ⟨20621066218735916890851191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13747377479157277927234127 20621066218735916890851191)
  ·
    refine ⟨30931599328103875336276787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20621066218735916890851191 30931599328103875336276787)
    ·
      refine ⟨46397398992155813004415181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30931599328103875336276787 46397398992155813004415181)
      ·
        refine ⟨17399024622058429876655693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46397398992155813004415181 17399024622058429876655693)
        ·
          refine ⟨6524634233271911203745885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17399024622058429876655693 6524634233271911203745885)
          ·
            refine ⟨2446737837476966701404707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6524634233271911203745885 2446737837476966701404707)
            ·
              refine ⟨3670106756215450052107061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446737837476966701404707 3670106756215450052107061)
              ·
                refine ⟨344072508395198442385037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3670106756215450052107061 344072508395198442385037)
                ·
                  refine ⟨129027190648199415894389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344072508395198442385037 129027190648199415894389)
                  ·
                    rfl

theorem cell21_565379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 3].length) (baseStart_565379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565379 prefixEnd_565379 := by exact prefixLift 565379
  have htrace : WordTrace (prefixWord ++ tailWord_565379) baseStart_565379 baseEnd_565379 := by
    simpa [prefixWord, tailWord_565379, baseEnd_565379] using wordTrace_append hprefix tailTrace_565379
  have hstable : (prefixWord ++ tailWord_565379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565379).length < 2 ^ (prefixWord ++ tailWord_565379).sum := by decide
  have hdescent : baseEnd_565379 < baseStart_565379 := by decide
  rcases family_descends (prefixWord ++ tailWord_565379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565441 : List Nat := [1, 2, 6, 1, 2, 2, 7]
def baseStart_565441 : Nat := 118140960795 + 565441 * 2 ^ 59
def prefixEnd_565441 : Nat := 4983230072969 + 3 ^ 40 * 565441 * 2
def baseEnd_565441 : Nat := 14337926654766787317881

theorem tailTrace_565441 : CollatzResearch.WordTrace tailWord_565441 prefixEnd_565441 14337926654766787317881 := by
  unfold tailWord_565441
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623327544511301479608177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13748885029674200986405451 20623327544511301479608177)
  ·
    refine ⟨15467495658383476109706133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623327544511301479608177 15467495658383476109706133)
    ·
      refine ⟨725038858986725442642475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15467495658383476109706133 725038858986725442642475)
      ·
        refine ⟨1087558288480088163963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725038858986725442642475 1087558288480088163963713)
        ·
          refine ⟨815668716360066122972785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087558288480088163963713 815668716360066122972785)
          ·
            refine ⟨611751537270049592229589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815668716360066122972785 611751537270049592229589)
            ·
              refine ⟨14337926654766787317881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 611751537270049592229589 14337926654766787317881)
              ·
                rfl

theorem cell21_565441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 7].length) (baseStart_565441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565441 prefixEnd_565441 := by exact prefixLift 565441
  have htrace : WordTrace (prefixWord ++ tailWord_565441) baseStart_565441 baseEnd_565441 := by
    simpa [prefixWord, tailWord_565441, baseEnd_565441] using wordTrace_append hprefix tailTrace_565441
  have hstable : (prefixWord ++ tailWord_565441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565441).length < 2 ^ (prefixWord ++ tailWord_565441).sum := by decide
  have hdescent : baseEnd_565441 < baseStart_565441 := by decide
  rcases family_descends (prefixWord ++ tailWord_565441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565497 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_565497 : Nat := 118140960795 + 565497 * 2 ^ 59
def prefixEnd_565497 : Nat := 4983230072969 + 3 ^ 40 * 565497 * 2
def baseEnd_565497 : Nat := 129054119855857432927481

theorem tailTrace_565497 : CollatzResearch.WordTrace tailWord_565497 prefixEnd_565497 129054119855857432927481 := by
  unfold tailWord_565497
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625370032308423043646745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13750246688205615362431163 20625370032308423043646745)
  ·
    refine ⟨15469027524231317282735059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20625370032308423043646745 15469027524231317282735059)
    ·
      refine ⟨23203541286346975924102589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15469027524231317282735059 23203541286346975924102589)
      ·
        refine ⟨8701327982380115971538471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23203541286346975924102589 8701327982380115971538471)
        ·
          refine ⟨13051991973570173957307707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8701327982380115971538471 13051991973570173957307707)
          ·
            refine ⟨19577987960355260935961561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051991973570173957307707 19577987960355260935961561)
            ·
              refine ⟨14683490970266445701971171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19577987960355260935961561 14683490970266445701971171)
              ·
                refine ⟨22025236455399668552956757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683490970266445701971171 22025236455399668552956757)
                ·
                  refine ⟨129054119855857432927481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22025236455399668552956757 129054119855857432927481)
                  ·
                    rfl

theorem cell21_565497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_565497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565497 prefixEnd_565497 := by exact prefixLift 565497
  have htrace : WordTrace (prefixWord ++ tailWord_565497) baseStart_565497 baseEnd_565497 := by
    simpa [prefixWord, tailWord_565497, baseEnd_565497] using wordTrace_append hprefix tailTrace_565497
  have hstable : (prefixWord ++ tailWord_565497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565497).length < 2 ^ (prefixWord ++ tailWord_565497).sum := by decide
  have hdescent : baseEnd_565497 < baseStart_565497 := by decide
  rcases family_descends (prefixWord ++ tailWord_565497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565506 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_565506 : Nat := 118140960795 + 565506 * 2 ^ 59
def prefixEnd_565506 : Nat := 4983230072969 + 3 ^ 40 * 565506 * 2
def baseEnd_565506 : Nat := 129056173778475417277463

theorem tailTrace_565506 : CollatzResearch.WordTrace tailWord_565506 prefixEnd_565506 129056173778475417277463 := by
  unfold tailWord_565506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156424572318954395181093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13750465526183878387149581 5156424572318954395181093)
  ·
    refine ⟨966829607309803949096455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5156424572318954395181093 966829607309803949096455)
    ·
      refine ⟨1450244410964705923644683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966829607309803949096455 1450244410964705923644683)
      ·
        refine ⟨2175366616447058885467025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450244410964705923644683 2175366616447058885467025)
        ·
          refine ⟨1631524962335294164100269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175366616447058885467025 1631524962335294164100269)
          ·
            refine ⟨611821860875735311537601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1631524962335294164100269 611821860875735311537601)
            ·
              refine ⟨458866395656801483653201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611821860875735311537601 458866395656801483653201)
              ·
                refine ⟨344149796742601112739901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458866395656801483653201 344149796742601112739901)
                ·
                  refine ⟨129056173778475417277463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344149796742601112739901 129056173778475417277463)
                  ·
                    rfl

theorem cell21_565506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_565506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565506 prefixEnd_565506 := by exact prefixLift 565506
  have htrace : WordTrace (prefixWord ++ tailWord_565506) baseStart_565506 baseEnd_565506 := by
    simpa [prefixWord, tailWord_565506, baseEnd_565506] using wordTrace_append hprefix tailTrace_565506
  have hstable : (prefixWord ++ tailWord_565506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565506).length < 2 ^ (prefixWord ++ tailWord_565506).sum := by decide
  have hdescent : baseEnd_565506 < baseStart_565506 := by decide
  rcases family_descends (prefixWord ++ tailWord_565506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565534 : List Nat := [4, 3, 2, 1, 1, 2, 3, 5]
def baseStart_565534 : Nat := 118140960795 + 565534 * 2 ^ 59
def prefixEnd_565534 : Nat := 4983230072969 + 3 ^ 40 * 565534 * 2
def baseEnd_565534 : Nat := 43020854586651196936913

theorem tailTrace_565534 : CollatzResearch.WordTrace tailWord_565534 prefixEnd_565534 43020854586651196936913 := by
  unfold tailWord_565534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578339941646797295342957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13751146355449585575162437 2578339941646797295342957)
  ·
    refine ⟨966877478117548985753609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2578339941646797295342957 966877478117548985753609)
    ·
      refine ⟨725158108588161739315207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 966877478117548985753609 725158108588161739315207)
      ·
        refine ⟨1087737162882242608972811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725158108588161739315207 1087737162882242608972811)
        ·
          refine ⟨1631605744323363913459217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087737162882242608972811 1631605744323363913459217)
          ·
            refine ⟨1223704308242522935094413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1631605744323363913459217 1223704308242522935094413)
            ·
              refine ⟨458889115590946100660405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223704308242522935094413 458889115590946100660405)
              ·
                refine ⟨43020854586651196936913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 458889115590946100660405 43020854586651196936913)
                ·
                  rfl

theorem cell21_565534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_565534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565534 prefixEnd_565534 := by exact prefixLift 565534
  have htrace : WordTrace (prefixWord ++ tailWord_565534) baseStart_565534 baseEnd_565534 := by
    simpa [prefixWord, tailWord_565534, baseEnd_565534] using wordTrace_append hprefix tailTrace_565534
  have hstable : (prefixWord ++ tailWord_565534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565534).length < 2 ^ (prefixWord ++ tailWord_565534).sum := by decide
  have hdescent : baseEnd_565534 < baseStart_565534 := by decide
  rcases family_descends (prefixWord ++ tailWord_565534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565562 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_565562 : Nat := 118140960795 + 565562 * 2 ^ 59
def prefixEnd_565562 : Nat := 4983230072969 + 3 ^ 40 * 565562 * 2
def baseEnd_565562 : Nat := 129068953741431764344015

theorem tailTrace_565562 : CollatzResearch.WordTrace tailWord_565562 prefixEnd_565562 129068953741431764344015 := by
  unfold tailWord_565562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156935194268234786190735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13751827184715292763175293 5156935194268234786190735)
  ·
    refine ⟨7735402791402352179286103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156935194268234786190735 7735402791402352179286103)
    ·
      refine ⟨11603104187103528268929155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735402791402352179286103 11603104187103528268929155)
      ·
        refine ⟨17404656280655292403393733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11603104187103528268929155 17404656280655292403393733)
        ·
          refine ⟨3263373052622867325636325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17404656280655292403393733 3263373052622867325636325)
          ·
            refine ⟨611882447366787623556811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3263373052622867325636325 611882447366787623556811)
            ·
              refine ⟨917823671050181435335217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611882447366787623556811 917823671050181435335217)
              ·
                refine ⟨688367753287636076501413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917823671050181435335217 688367753287636076501413)
                ·
                  refine ⟨129068953741431764344015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688367753287636076501413 129068953741431764344015)
                  ·
                    rfl

theorem cell21_565562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_565562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565562 prefixEnd_565562 := by exact prefixLift 565562
  have htrace : WordTrace (prefixWord ++ tailWord_565562) baseStart_565562 baseEnd_565562 := by
    simpa [prefixWord, tailWord_565562, baseEnd_565562] using wordTrace_append hprefix tailTrace_565562
  have hstable : (prefixWord ++ tailWord_565562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565562).length < 2 ^ (prefixWord ++ tailWord_565562).sum := by decide
  have hdescent : baseEnd_565562 < baseStart_565562 := by decide
  rcases family_descends (prefixWord ++ tailWord_565562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565604 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_565604 : Nat := 118140960795 + 565604 * 2 ^ 59
def prefixEnd_565604 : Nat := 4983230072969 + 3 ^ 40 * 565604 * 2
def baseEnd_565604 : Nat := 129078538713649024643929

theorem tailTrace_565604 : CollatzResearch.WordTrace tailWord_565604 prefixEnd_565604 129078538713649024643929 := by
  unfold tailWord_565604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314636321460390158895933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13752848428613853545194577 10314636321460390158895933)
  ·
    refine ⟨3867988620547646309585975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10314636321460390158895933 3867988620547646309585975)
    ·
      refine ⟨5801982930821469464378963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867988620547646309585975 5801982930821469464378963)
      ·
        refine ⟨8702974396232204196568445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801982930821469464378963 8702974396232204196568445)
        ·
          refine ⟨3263615398587076573713167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8702974396232204196568445 3263615398587076573713167)
          ·
            refine ⟨4895423097880614860569751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263615398587076573713167 4895423097880614860569751)
            ·
              refine ⟨7343134646820922290854627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895423097880614860569751 7343134646820922290854627)
              ·
                refine ⟨11014701970231383436281941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7343134646820922290854627 11014701970231383436281941)
                ·
                  refine ⟨129078538713649024643929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11014701970231383436281941 129078538713649024643929)
                  ·
                    rfl

theorem cell21_565604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_565604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565604 prefixEnd_565604 := by exact prefixLift 565604
  have htrace : WordTrace (prefixWord ++ tailWord_565604) baseStart_565604 baseEnd_565604 := by
    simpa [prefixWord, tailWord_565604, baseEnd_565604] using wordTrace_append hprefix tailTrace_565604
  have hstable : (prefixWord ++ tailWord_565604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565604).length < 2 ^ (prefixWord ++ tailWord_565604).sum := by decide
  have hdescent : baseEnd_565604 < baseStart_565604 := by decide
  rcases family_descends (prefixWord ++ tailWord_565604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565621 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_565621 : Nat := 118140960795 + 565621 * 2 ^ 59
def prefixEnd_565621 : Nat := 4983230072969 + 3 ^ 40 * 565621 * 2
def baseEnd_565621 : Nat := 129082418345260772860561

theorem tailTrace_565621 : CollatzResearch.WordTrace tailWord_565621 prefixEnd_565621 129082418345260772860561 := by
  unfold tailWord_565621
  simp only [CollatzResearch.WordTrace]
  refine ⟨20629892683859192221160717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13753261789239461480773811 20629892683859192221160717)
  ·
    refine ⟨7736209756447197082935269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20629892683859192221160717 7736209756447197082935269)
    ·
      refine ⟨1450539329333849453050363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7736209756447197082935269 1450539329333849453050363)
      ·
        refine ⟨2175808994000774179575545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450539329333849453050363 2175808994000774179575545)
        ·
          refine ⟨1631856745500580634681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175808994000774179575545 1631856745500580634681659)
          ·
            refine ⟨2447785118250870952022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631856745500580634681659 2447785118250870952022489)
            ·
              refine ⟨1835838838688153214016867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447785118250870952022489 1835838838688153214016867)
              ·
                refine ⟨2753758258032229821025301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835838838688153214016867 2753758258032229821025301)
                ·
                  refine ⟨129082418345260772860561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2753758258032229821025301 129082418345260772860561)
                  ·
                    rfl

theorem cell21_565621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_565621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565621 prefixEnd_565621 := by exact prefixLift 565621
  have htrace : WordTrace (prefixWord ++ tailWord_565621) baseStart_565621 baseEnd_565621 := by
    simpa [prefixWord, tailWord_565621, baseEnd_565621] using wordTrace_append hprefix tailTrace_565621
  have hstable : (prefixWord ++ tailWord_565621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565621).length < 2 ^ (prefixWord ++ tailWord_565621).sum := by decide
  have hdescent : baseEnd_565621 < baseStart_565621 := by decide
  rcases family_descends (prefixWord ++ tailWord_565621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565731 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 4]
def baseStart_565731 : Nat := 118140960795 + 565731 * 2 ^ 59
def prefixEnd_565731 : Nat := 4983230072969 + 3 ^ 40 * 565731 * 2
def baseEnd_565731 : Nat := 129107521843925026027003

theorem tailTrace_565731 : CollatzResearch.WordTrace tailWord_565731 prefixEnd_565731 129107521843925026027003 := by
  unfold tailWord_565731
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633904713460681007665047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13755936475640454005110031 20633904713460681007665047)
  ·
    refine ⟨30950857070191021511497571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20633904713460681007665047 30950857070191021511497571)
    ·
      refine ⟨46426285605286532267246357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30950857070191021511497571 46426285605286532267246357)
      ·
        refine ⟨2176232137747806200027173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46426285605286532267246357 2176232137747806200027173)
        ·
          refine ⟨408043525827713662505095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2176232137747806200027173 408043525827713662505095)
          ·
            refine ⟨612065288741570493757643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408043525827713662505095 612065288741570493757643)
            ·
              refine ⟨918097933112355740636465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612065288741570493757643 918097933112355740636465)
              ·
                refine ⟨688573449834266805477349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918097933112355740636465 688573449834266805477349)
                ·
                  refine ⟨129107521843925026027003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688573449834266805477349 129107521843925026027003)
                  ·
                    rfl

theorem cell21_565731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 4].length) (baseStart_565731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565731 prefixEnd_565731 := by exact prefixLift 565731
  have htrace : WordTrace (prefixWord ++ tailWord_565731) baseStart_565731 baseEnd_565731 := by
    simpa [prefixWord, tailWord_565731, baseEnd_565731] using wordTrace_append hprefix tailTrace_565731
  have hstable : (prefixWord ++ tailWord_565731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565731).length < 2 ^ (prefixWord ++ tailWord_565731).sum := by decide
  have hdescent : baseEnd_565731 < baseStart_565731 := by decide
  rcases family_descends (prefixWord ++ tailWord_565731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565742 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_565742 : Nat := 118140960795 + 565742 * 2 ^ 59
def prefixEnd_565742 : Nat := 4983230072969 + 3 ^ 40 * 565742 * 2
def baseEnd_565742 : Nat := 129110032193791451343647

theorem tailTrace_565742 : CollatzResearch.WordTrace tailWord_565742 prefixEnd_565742 129110032193791451343647 := by
  unfold tailWord_565742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579288239552603735789435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13756203944280553257543653 2579288239552603735789435)
  ·
    refine ⟨3868932359328905603684153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579288239552603735789435 3868932359328905603684153)
    ·
      refine ⟨2901699269496679202763115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3868932359328905603684153 2901699269496679202763115)
      ·
        refine ⟨4352548904245018804144673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901699269496679202763115 4352548904245018804144673)
        ·
          refine ⟨3264411678183764103108505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352548904245018804144673 3264411678183764103108505)
          ·
            refine ⟨2448308758637823077331379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3264411678183764103108505 2448308758637823077331379)
            ·
              refine ⟨3672463137956734615997069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448308758637823077331379 3672463137956734615997069)
              ·
                refine ⟨1377173676733775480998901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3672463137956734615997069 1377173676733775480998901)
                ·
                  refine ⟨129110032193791451343647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1377173676733775480998901 129110032193791451343647)
                  ·
                    rfl

theorem cell21_565742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_565742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565742 prefixEnd_565742 := by exact prefixLift 565742
  have htrace : WordTrace (prefixWord ++ tailWord_565742) baseStart_565742 baseEnd_565742 := by
    simpa [prefixWord, tailWord_565742, baseEnd_565742] using wordTrace_append hprefix tailTrace_565742
  have hstable : (prefixWord ++ tailWord_565742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565742).length < 2 ^ (prefixWord ++ tailWord_565742).sum := by decide
  have hdescent : baseEnd_565742 < baseStart_565742 := by decide
  rcases family_descends (prefixWord ++ tailWord_565742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565762 : List Nat := [3, 4, 1, 2, 2, 2, 2, 5]
def baseStart_565762 : Nat := 118140960795 + 565762 * 2 ^ 59
def prefixEnd_565762 : Nat := 4983230072969 + 3 ^ 40 * 565762 * 2
def baseEnd_565762 : Nat := 43038198822091953670091

theorem tailTrace_565762 : CollatzResearch.WordTrace tailWord_565762 prefixEnd_565762 43038198822091953670091 := by
  unfold tailWord_565762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158758844087093325510885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13756690250898915534695693 5158758844087093325510885)
  ·
    refine ⟨967267283266329998533291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5158758844087093325510885 967267283266329998533291)
    ·
      refine ⟨1450900924899494997799937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967267283266329998533291 1450900924899494997799937)
      ·
        refine ⟨1088175693674621248349953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450900924899494997799937 1088175693674621248349953)
        ·
          refine ⟨816131770255965936262465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088175693674621248349953 816131770255965936262465)
          ·
            refine ⟨612098827691974452196849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816131770255965936262465 612098827691974452196849)
            ·
              refine ⟨459074120768980839147637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612098827691974452196849 459074120768980839147637)
              ·
                refine ⟨43038198822091953670091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459074120768980839147637 43038198822091953670091)
                ·
                  rfl

theorem cell21_565762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_565762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565762 prefixEnd_565762 := by exact prefixLift 565762
  have htrace : WordTrace (prefixWord ++ tailWord_565762) baseStart_565762 baseEnd_565762 := by
    simpa [prefixWord, tailWord_565762, baseEnd_565762] using wordTrace_append hprefix tailTrace_565762
  have hstable : (prefixWord ++ tailWord_565762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565762).length < 2 ^ (prefixWord ++ tailWord_565762).sum := by decide
  have hdescent : baseEnd_565762 < baseStart_565762 := by decide
  rcases family_descends (prefixWord ++ tailWord_565762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565852 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_565852 : Nat := 118140960795 + 565852 * 2 ^ 59
def prefixEnd_565852 : Nat := 4983230072969 + 3 ^ 40 * 565852 * 2
def baseEnd_565852 : Nat := 129135135692455704510089

theorem tailTrace_565852 : CollatzResearch.WordTrace tailWord_565852 prefixEnd_565852 129135135692455704510089 := by
  unfold tailWord_565852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319158973011159336409905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13758878630681545781879873 10319158973011159336409905)
  ·
    refine ⟨7739369229758369502307429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10319158973011159336409905 7739369229758369502307429)
    ·
      refine ⟨1451131730579694281682643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7739369229758369502307429 1451131730579694281682643)
      ·
        refine ⟨2176697595869541422523965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451131730579694281682643 2176697595869541422523965)
        ·
          refine ⟨816261598451078033446487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2176697595869541422523965 816261598451078033446487)
          ·
            refine ⟨1224392397676617050169731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816261598451078033446487 1224392397676617050169731)
            ·
              refine ⟨1836588596514925575254597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224392397676617050169731 1836588596514925575254597)
              ·
                refine ⟨344360361846548545360237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1836588596514925575254597 344360361846548545360237)
                ·
                  refine ⟨129135135692455704510089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344360361846548545360237 129135135692455704510089)
                  ·
                    rfl

theorem cell21_565852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_565852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565852 prefixEnd_565852 := by exact prefixLift 565852
  have htrace : WordTrace (prefixWord ++ tailWord_565852) baseStart_565852 baseEnd_565852 := by
    simpa [prefixWord, tailWord_565852, baseEnd_565852] using wordTrace_append hprefix tailTrace_565852
  have hstable : (prefixWord ++ tailWord_565852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565852).length < 2 ^ (prefixWord ++ tailWord_565852).sum := by decide
  have hdescent : baseEnd_565852 < baseStart_565852 := by decide
  rcases family_descends (prefixWord ++ tailWord_565852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565939 : List Nat := [1, 1, 1, 2, 3, 4, 4, 5]
def baseStart_565939 : Nat := 118140960795 + 565939 * 2 ^ 59
def prefixEnd_565939 : Nat := 4983230072969 + 3 ^ 40 * 565939 * 2
def baseEnd_565939 : Nat := 43051663425920962186637

theorem tailTrace_565939 : CollatzResearch.WordTrace tailWord_565939 prefixEnd_565939 43051663425920962186637 := by
  unfold tailWord_565939
  simp only [CollatzResearch.WordTrace]
  refine ⟨20641491096707132531236871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13760994064471421687491247 20641491096707132531236871)
  ·
    refine ⟨30962236645060698796855307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20641491096707132531236871 30962236645060698796855307)
    ·
      refine ⟨46443354967591048195282961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30962236645060698796855307 46443354967591048195282961)
      ·
        refine ⟨34832516225693286146462221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46443354967591048195282961 34832516225693286146462221)
        ·
          refine ⟨13062193584634982304923333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34832516225693286146462221 13062193584634982304923333)
          ·
            refine ⟨2449161297119059182173125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13062193584634982304923333 2449161297119059182173125)
            ·
              refine ⟨459217743209823596657461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2449161297119059182173125 459217743209823596657461)
              ·
                refine ⟨43051663425920962186637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459217743209823596657461 43051663425920962186637)
                ·
                  rfl

theorem cell21_565939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].length) (baseStart_565939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_565939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_565939 prefixEnd_565939 := by exact prefixLift 565939
  have htrace : WordTrace (prefixWord ++ tailWord_565939) baseStart_565939 baseEnd_565939 := by
    simpa [prefixWord, tailWord_565939, baseEnd_565939] using wordTrace_append hprefix tailTrace_565939
  have hstable : (prefixWord ++ tailWord_565939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565939).length < 2 ^ (prefixWord ++ tailWord_565939).sum := by decide
  have hdescent : baseEnd_565939 < baseStart_565939 := by decide
  rcases family_descends (prefixWord ++ tailWord_565939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566018 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_566018 : Nat := 118140960795 + 566018 * 2 ^ 59
def prefixEnd_566018 : Nat := 4983230072969 + 3 ^ 40 * 566018 * 2
def baseEnd_566018 : Nat := 129173019154076304743083

theorem tailTrace_566018 : CollatzResearch.WordTrace tailWord_566018 prefixEnd_566018 129173019154076304743083 := by
  unfold tailWord_566018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161093115855232255840677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13762914975613952682241805 5161093115855232255840677)
  ·
    refine ⟨967704959222856047970127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5161093115855232255840677 967704959222856047970127)
    ·
      refine ⟨1451557438834284071955191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967704959222856047970127 1451557438834284071955191)
      ·
        refine ⟨2177336158251426107932787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451557438834284071955191 2177336158251426107932787)
        ·
          refine ⟨3266004237377139161899181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177336158251426107932787 3266004237377139161899181)
          ·
            refine ⟨1224751589016427185712193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3266004237377139161899181 1224751589016427185712193)
            ·
              refine ⟨918563691762320389284145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224751589016427185712193 918563691762320389284145)
              ·
                refine ⟨688922768821740291963109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918563691762320389284145 688922768821740291963109)
                ·
                  refine ⟨129173019154076304743083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 688922768821740291963109 129173019154076304743083)
                  ·
                    rfl

theorem cell21_566018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_566018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566018 prefixEnd_566018 := by exact prefixLift 566018
  have htrace : WordTrace (prefixWord ++ tailWord_566018) baseStart_566018 baseEnd_566018 := by
    simpa [prefixWord, tailWord_566018, baseEnd_566018] using wordTrace_append hprefix tailTrace_566018
  have hstable : (prefixWord ++ tailWord_566018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566018).length < 2 ^ (prefixWord ++ tailWord_566018).sum := by decide
  have hdescent : baseEnd_566018 < baseStart_566018 := by decide
  rcases family_descends (prefixWord ++ tailWord_566018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566077 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_566077 : Nat := 118140960795 + 566077 * 2 ^ 59
def prefixEnd_566077 : Nat := 4983230072969 + 3 ^ 40 * 566077 * 2
def baseEnd_566077 : Nat := 129186483757905313259629

theorem tailTrace_566077 : CollatzResearch.WordTrace tailWord_566077 prefixEnd_566077 129186483757905313259629 := by
  unfold tailWord_566077
  simp only [CollatzResearch.WordTrace]
  refine ⟨20646524370207182099760485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13764349580138121399840323 20646524370207182099760485)
  ·
    refine ⟨3871223319413846643705091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20646524370207182099760485 3871223319413846643705091)
    ·
      refine ⟨5806834979120769965557637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871223319413846643705091 5806834979120769965557637)
      ·
        refine ⟨1088781558585144368542057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5806834979120769965557637 1088781558585144368542057)
        ·
          refine ⟨816586168938858276406543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088781558585144368542057 816586168938858276406543)
          ·
            refine ⟨1224879253408287414609815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816586168938858276406543 1224879253408287414609815)
            ·
              refine ⟨1837318880112431121914723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224879253408287414609815 1837318880112431121914723)
              ·
                refine ⟨2755978320168646682872085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837318880112431121914723 2755978320168646682872085)
                ·
                  refine ⟨129186483757905313259629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2755978320168646682872085 129186483757905313259629)
                  ·
                    rfl

theorem cell21_566077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_566077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566077 prefixEnd_566077 := by exact prefixLift 566077
  have htrace : WordTrace (prefixWord ++ tailWord_566077) baseStart_566077 baseEnd_566077 := by
    simpa [prefixWord, tailWord_566077, baseEnd_566077] using wordTrace_append hprefix tailTrace_566077
  have hstable : (prefixWord ++ tailWord_566077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566077).length < 2 ^ (prefixWord ++ tailWord_566077).sum := by decide
  have hdescent : baseEnd_566077 < baseStart_566077 := by decide
  rcases family_descends (prefixWord ++ tailWord_566077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566105 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_566105 : Nat := 118140960795 + 566105 * 2 ^ 59
def prefixEnd_566105 : Nat := 4983230072969 + 3 ^ 40 * 566105 * 2
def baseEnd_566105 : Nat := 129192873739383486792905

theorem tailTrace_566105 : CollatzResearch.WordTrace tailWord_566105 prefixEnd_566105 129192873739383486792905 := by
  unfold tailWord_566105
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647545614105742881779769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13765030409403828587853179 20647545614105742881779769)
  ·
    refine ⟨15485659210579307161334827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20647545614105742881779769 15485659210579307161334827)
    ·
      refine ⟨23228488815868960742002241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15485659210579307161334827 23228488815868960742002241)
      ·
        refine ⟨17421366611901720556501681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23228488815868960742002241 17421366611901720556501681)
        ·
          refine ⟨13066024958926290417376261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17421366611901720556501681 13066024958926290417376261)
          ·
            refine ⟨2449879679798679453258049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13066024958926290417376261 2449879679798679453258049)
            ·
              refine ⟨1837409759849009589943537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449879679798679453258049 1837409759849009589943537)
              ·
                refine ⟨1378057319886757192457653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1837409759849009589943537 1378057319886757192457653)
                ·
                  refine ⟨129192873739383486792905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1378057319886757192457653 129192873739383486792905)
                  ·
                    rfl

theorem cell21_566105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_566105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566105 prefixEnd_566105 := by exact prefixLift 566105
  have htrace : WordTrace (prefixWord ++ tailWord_566105) baseStart_566105 baseEnd_566105 := by
    simpa [prefixWord, tailWord_566105, baseEnd_566105] using wordTrace_append hprefix tailTrace_566105
  have hstable : (prefixWord ++ tailWord_566105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566105).length < 2 ^ (prefixWord ++ tailWord_566105).sum := by decide
  have hdescent : baseEnd_566105 < baseStart_566105 := by decide
  rcases family_descends (prefixWord ++ tailWord_566105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566108 : List Nat := [2, 2, 4, 2, 1, 1, 4, 5]
def baseStart_566108 : Nat := 118140960795 + 566108 * 2 ^ 59
def prefixEnd_566108 : Nat := 4983230072969 + 3 ^ 40 * 566108 * 2
def baseEnd_566108 : Nat := 43064519460085382747633

theorem tailTrace_566108 : CollatzResearch.WordTrace tailWord_566108 prefixEnd_566108 43064519460085382747633 := by
  unfold tailWord_566108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323827516547437197069489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13765103355396582929425985 10323827516547437197069489)
  ·
    refine ⟨7742870637410577897802117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10323827516547437197069489 7742870637410577897802117)
    ·
      refine ⟨1451788244514483355837897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7742870637410577897802117 1451788244514483355837897)
      ·
        refine ⟨1088841183385862516878423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451788244514483355837897 1088841183385862516878423)
        ·
          refine ⟨1633261775078793775317635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088841183385862516878423 1633261775078793775317635)
          ·
            refine ⟨2449892662618190662976453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633261775078793775317635 2449892662618190662976453)
            ·
              refine ⟨459354874240910749308085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2449892662618190662976453 459354874240910749308085)
              ·
                refine ⟨43064519460085382747633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459354874240910749308085 43064519460085382747633)
                ·
                  rfl

theorem cell21_566108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_566108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566108 prefixEnd_566108 := by exact prefixLift 566108
  have htrace : WordTrace (prefixWord ++ tailWord_566108) baseStart_566108 baseEnd_566108 := by
    simpa [prefixWord, tailWord_566108, baseEnd_566108] using wordTrace_append hprefix tailTrace_566108
  have hstable : (prefixWord ++ tailWord_566108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566108).length < 2 ^ (prefixWord ++ tailWord_566108).sum := by decide
  have hdescent : baseEnd_566108 < baseStart_566108 := by decide
  rcases family_descends (prefixWord ++ tailWord_566108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566153 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 4]
def baseStart_566153 : Nat := 118140960795 + 566153 * 2 ^ 59
def prefixEnd_566153 : Nat := 4983230072969 + 3 ^ 40 * 566153 * 2
def baseEnd_566153 : Nat := 129203827993346069992807

theorem tailTrace_566153 : CollatzResearch.WordTrace tailWord_566153 prefixEnd_566153 129203827993346069992807 := by
  unfold tailWord_566153
  simp only [CollatzResearch.WordTrace]
  refine ⟨20649296317931847079527113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13766197545287898053018075 20649296317931847079527113)
  ·
    refine ⟨15486972238448885309645335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20649296317931847079527113 15486972238448885309645335)
    ·
      refine ⟨23230458357673327964468003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15486972238448885309645335 23230458357673327964468003)
      ·
        refine ⟨34845687536509991946702005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23230458357673327964468003 34845687536509991946702005)
        ·
          refine ⟨3266783206547811745003313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34845687536509991946702005 3266783206547811745003313)
          ·
            refine ⟨2450087404910858808752485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266783206547811745003313 2450087404910858808752485)
            ·
              refine ⟨459391388420786026641091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2450087404910858808752485 459391388420786026641091)
              ·
                refine ⟨689087082631179039961637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459391388420786026641091 689087082631179039961637)
                ·
                  refine ⟨129203827993346069992807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689087082631179039961637 129203827993346069992807)
                  ·
                    rfl

theorem cell21_566153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_566153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566153 prefixEnd_566153 := by exact prefixLift 566153
  have htrace : WordTrace (prefixWord ++ tailWord_566153) baseStart_566153 baseEnd_566153 := by
    simpa [prefixWord, tailWord_566153, baseEnd_566153] using wordTrace_append hprefix tailTrace_566153
  have hstable : (prefixWord ++ tailWord_566153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566153).length < 2 ^ (prefixWord ++ tailWord_566153).sum := by decide
  have hdescent : baseEnd_566153 < baseStart_566153 := by decide
  rcases family_descends (prefixWord ++ tailWord_566153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566257 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_566257 : Nat := 118140960795 + 566257 * 2 ^ 59
def prefixEnd_566257 : Nat := 4983230072969 + 3 ^ 40 * 566257 * 2
def baseEnd_566257 : Nat := 129227562210265000259261

theorem tailTrace_566257 : CollatzResearch.WordTrace tailWord_566257 prefixEnd_566257 129227562210265000259261 := by
  unfold tailWord_566257
  simp only [CollatzResearch.WordTrace]
  refine ⟨20653089509555072841313025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13768726339703381894208683 20653089509555072841313025)
  ·
    refine ⟨15489817132166304630984769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20653089509555072841313025 15489817132166304630984769)
    ·
      refine ⟨11617362849124728473238577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489817132166304630984769 11617362849124728473238577)
      ·
        refine ⟨8713022136843546354928933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11617362849124728473238577 8713022136843546354928933)
        ·
          refine ⟨1633691650658164941549175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8713022136843546354928933 1633691650658164941549175)
          ·
            refine ⟨2450537475987247412323763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633691650658164941549175 2450537475987247412323763)
            ·
              refine ⟨3675806213980871118485645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450537475987247412323763 3675806213980871118485645)
              ·
                refine ⟨1378427330242826669432117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3675806213980871118485645 1378427330242826669432117)
                ·
                  refine ⟨129227562210265000259261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1378427330242826669432117 129227562210265000259261)
                  ·
                    rfl

theorem cell21_566257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_566257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566257 prefixEnd_566257 := by exact prefixLift 566257
  have htrace : WordTrace (prefixWord ++ tailWord_566257) baseStart_566257 baseEnd_566257 := by
    simpa [prefixWord, tailWord_566257, baseEnd_566257] using wordTrace_append hprefix tailTrace_566257
  have hstable : (prefixWord ++ tailWord_566257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566257).length < 2 ^ (prefixWord ++ tailWord_566257).sum := by decide
  have hdescent : baseEnd_566257 < baseStart_566257 := by decide
  rcases family_descends (prefixWord ++ tailWord_566257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566308 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_566308 : Nat := 118140960795 + 566308 * 2 ^ 59
def prefixEnd_566308 : Nat := 4983230072969 + 3 ^ 40 * 566308 * 2
def baseEnd_566308 : Nat := 129239201105100244909157

theorem tailTrace_566308 : CollatzResearch.WordTrace tailWord_566308 prefixEnd_566308 129239201105100244909157 := by
  unfold tailWord_566308
  simp only [CollatzResearch.WordTrace]
  refine ⟨10327474816185154275709789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13769966421580205700946385 10327474816185154275709789)
  ·
    refine ⟨3872803056069432853391171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10327474816185154275709789 3872803056069432853391171)
    ·
      refine ⟨5809204584104149280086757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3872803056069432853391171 5809204584104149280086757)
      ·
        refine ⟨1089225859519527990016267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5809204584104149280086757 1089225859519527990016267)
        ·
          refine ⟨1633838789279291985024401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089225859519527990016267 1633838789279291985024401)
          ·
            refine ⟨1225379091959468988768301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633838789279291985024401 1225379091959468988768301)
            ·
              refine ⟨459517159484800870788113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1225379091959468988768301 459517159484800870788113)
              ·
                refine ⟨344637869613600653091085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459517159484800870788113 344637869613600653091085)
                ·
                  refine ⟨129239201105100244909157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344637869613600653091085 129239201105100244909157)
                  ·
                    rfl

theorem cell21_566308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_566308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566308 prefixEnd_566308 := by exact prefixLift 566308
  have htrace : WordTrace (prefixWord ++ tailWord_566308) baseStart_566308 baseEnd_566308 := by
    simpa [prefixWord, tailWord_566308, baseEnd_566308] using wordTrace_append hprefix tailTrace_566308
  have hstable : (prefixWord ++ tailWord_566308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566308).length < 2 ^ (prefixWord ++ tailWord_566308).sum := by decide
  have hdescent : baseEnd_566308 < baseStart_566308 := by decide
  rcases family_descends (prefixWord ++ tailWord_566308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566350 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_566350 : Nat := 118140960795 + 566350 * 2 ^ 59
def prefixEnd_566350 : Nat := 4983230072969 + 3 ^ 40 * 566350 * 2
def baseEnd_566350 : Nat := 129248786077317505209071

theorem tailTrace_566350 : CollatzResearch.WordTrace tailWord_566350 prefixEnd_566350 129248786077317505209071 := by
  unfold tailWord_566350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582060187277268715556063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13770987665478766482965669 2582060187277268715556063)
  ·
    refine ⟨3873090280915903073334095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582060187277268715556063 3873090280915903073334095)
    ·
      refine ⟨5809635421373854610001143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873090280915903073334095 5809635421373854610001143)
      ·
        refine ⟨8714453132060781915001715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809635421373854610001143 8714453132060781915001715)
        ·
          refine ⟨13071679698091172872502573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8714453132060781915001715 13071679698091172872502573)
          ·
            refine ⟨4901879886784189827188465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13071679698091172872502573 4901879886784189827188465)
            ·
              refine ⟨3676409915088142370391349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4901879886784189827188465 3676409915088142370391349)
              ·
                refine ⟨344663429539513347224189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3676409915088142370391349 344663429539513347224189)
                ·
                  refine ⟨129248786077317505209071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344663429539513347224189 129248786077317505209071)
                  ·
                    rfl

theorem cell21_566350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_566350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566350 prefixEnd_566350 := by exact prefixLift 566350
  have htrace : WordTrace (prefixWord ++ tailWord_566350) baseStart_566350 baseEnd_566350 := by
    simpa [prefixWord, tailWord_566350, baseEnd_566350] using wordTrace_append hprefix tailTrace_566350
  have hstable : (prefixWord ++ tailWord_566350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566350).length < 2 ^ (prefixWord ++ tailWord_566350).sum := by decide
  have hdescent : baseEnd_566350 < baseStart_566350 := by decide
  rcases family_descends (prefixWord ++ tailWord_566350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566392 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_566392 : Nat := 118140960795 + 566392 * 2 ^ 59
def prefixEnd_566392 : Nat := 4983230072969 + 3 ^ 40 * 566392 * 2
def baseEnd_566392 : Nat := 129258371049534765508985

theorem tailTrace_566392 : CollatzResearch.WordTrace tailWord_566392 prefixEnd_566392 129258371049534765508985 := by
  unfold tailWord_566392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329006682032995448738715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13772008909377327264984953 10329006682032995448738715)
  ·
    refine ⟨15493510023049493173108073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10329006682032995448738715 15493510023049493173108073)
    ·
      refine ⟨11620132517287119879831055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15493510023049493173108073 11620132517287119879831055)
      ·
        refine ⟨17430198775930679819746583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11620132517287119879831055 17430198775930679819746583)
        ·
          refine ⟨26145298163896019729619875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17430198775930679819746583 26145298163896019729619875)
          ·
            refine ⟨39217947245844029594429813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26145298163896019729619875 39217947245844029594429813)
            ·
              refine ⟨3676682554297877774477795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39217947245844029594429813 3676682554297877774477795)
              ·
                refine ⟨5515023831446816661716693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676682554297877774477795 5515023831446816661716693)
                ·
                  refine ⟨129258371049534765508985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5515023831446816661716693 129258371049534765508985)
                  ·
                    rfl

theorem cell21_566392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_566392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566392 prefixEnd_566392 := by exact prefixLift 566392
  have htrace : WordTrace (prefixWord ++ tailWord_566392) baseStart_566392 baseEnd_566392 := by
    simpa [prefixWord, tailWord_566392, baseEnd_566392] using wordTrace_append hprefix tailTrace_566392
  have hstable : (prefixWord ++ tailWord_566392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566392).length < 2 ^ (prefixWord ++ tailWord_566392).sum := by decide
  have hdescent : baseEnd_566392 < baseStart_566392 := by decide
  rcases family_descends (prefixWord ++ tailWord_566392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566426 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_566426 : Nat := 118140960795 + 566426 * 2 ^ 59
def prefixEnd_566426 : Nat := 4983230072969 + 3 ^ 40 * 566426 * 2
def baseEnd_566426 : Nat := 129266130312758261942249

theorem tailTrace_566426 : CollatzResearch.WordTrace tailWord_566426 prefixEnd_566426 129266130312758261942249 := by
  unfold tailWord_566426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164813361485703676053783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13772835630628543136143421 5164813361485703676053783)
  ·
    refine ⟨7747220042228555514080675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5164813361485703676053783 7747220042228555514080675)
    ·
      refine ⟨11620830063342833271121013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747220042228555514080675 11620830063342833271121013)
      ·
        refine ⟨1089452818438390619167595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11620830063342833271121013 1089452818438390619167595)
        ·
          refine ⟨1634179227657585928751393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089452818438390619167595 1634179227657585928751393)
          ·
            refine ⟨1225634420743189446563545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1634179227657585928751393 1225634420743189446563545)
            ·
              refine ⟨919225815557392084922659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225634420743189446563545 919225815557392084922659)
              ·
                refine ⟨1378838723336088127383989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919225815557392084922659 1378838723336088127383989)
                ·
                  refine ⟨129266130312758261942249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1378838723336088127383989 129266130312758261942249)
                  ·
                    rfl

theorem cell21_566426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_566426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566426 prefixEnd_566426 := by exact prefixLift 566426
  have htrace : WordTrace (prefixWord ++ tailWord_566426) baseStart_566426 baseEnd_566426 := by
    simpa [prefixWord, tailWord_566426, baseEnd_566426] using wordTrace_append hprefix tailTrace_566426
  have hstable : (prefixWord ++ tailWord_566426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566426).length < 2 ^ (prefixWord ++ tailWord_566426).sum := by decide
  have hdescent : baseEnd_566426 < baseStart_566426 := by decide
  rcases family_descends (prefixWord ++ tailWord_566426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566477 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 5]
def baseStart_566477 : Nat := 118140960795 + 566477 * 2 ^ 59
def prefixEnd_566477 : Nat := 4983230072969 + 3 ^ 40 * 566477 * 2
def baseEnd_566477 : Nat := 129277769207593506592145

theorem tailTrace_566477 : CollatzResearch.WordTrace tailWord_566477 prefixEnd_566477 129277769207593506592145 := by
  unfold tailWord_566477
  simp only [CollatzResearch.WordTrace]
  refine ⟨20661113568758050414321685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13774075712505366942881123 20661113568758050414321685)
  ·
    refine ⟨968489698535533613171329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20661113568758050414321685 968489698535533613171329)
    ·
      refine ⟨726367273901650209878497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 968489698535533613171329 726367273901650209878497)
      ·
        refine ⟨544775455426237657408873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 726367273901650209878497 544775455426237657408873)
        ·
          refine ⟨408581591569678243056655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544775455426237657408873 408581591569678243056655)
          ·
            refine ⟨612872387354517364584983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408581591569678243056655 612872387354517364584983)
            ·
              refine ⟨919308581031776046877475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612872387354517364584983 919308581031776046877475)
              ·
                refine ⟨1378962871547664070316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919308581031776046877475 1378962871547664070316213)
                ·
                  refine ⟨129277769207593506592145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1378962871547664070316213 129277769207593506592145)
                  ·
                    rfl

theorem cell21_566477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_566477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566477 prefixEnd_566477 := by exact prefixLift 566477
  have htrace : WordTrace (prefixWord ++ tailWord_566477) baseStart_566477 baseEnd_566477 := by
    simpa [prefixWord, tailWord_566477, baseEnd_566477] using wordTrace_append hprefix tailTrace_566477
  have hstable : (prefixWord ++ tailWord_566477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566477).length < 2 ^ (prefixWord ++ tailWord_566477).sum := by decide
  have hdescent : baseEnd_566477 < baseStart_566477 := by decide
  rcases family_descends (prefixWord ++ tailWord_566477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566530 : List Nat := [3, 4, 1, 1, 12]
def baseStart_566530 : Nat := 118140960795 + 566530 * 2 ^ 59
def prefixEnd_566530 : Nat := 4983230072969 + 3 ^ 40 * 566530 * 2
def baseEnd_566530 : Nat := 1596171167033051755663

theorem tailTrace_566530 : CollatzResearch.WordTrace tailWord_566530 prefixEnd_566530 1596171167033051755663 := by
  unfold tailWord_566530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165761659391510116500261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13775364425044026977334029 5165761659391510116500261)
  ·
    refine ⟨968580311135908146843799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5165761659391510116500261 968580311135908146843799)
    ·
      refine ⟨1452870466703862220265699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968580311135908146843799 1452870466703862220265699)
      ·
        refine ⟨2179305700055793330398549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452870466703862220265699 2179305700055793330398549)
        ·
          refine ⟨1596171167033051755663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2179305700055793330398549 1596171167033051755663)
          ·
            rfl

theorem cell21_566530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 12].length) (baseStart_566530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566530 prefixEnd_566530 := by exact prefixLift 566530
  have htrace : WordTrace (prefixWord ++ tailWord_566530) baseStart_566530 baseEnd_566530 := by
    simpa [prefixWord, tailWord_566530, baseEnd_566530] using wordTrace_append hprefix tailTrace_566530
  have hstable : (prefixWord ++ tailWord_566530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566530).length < 2 ^ (prefixWord ++ tailWord_566530).sum := by decide
  have hdescent : baseEnd_566530 < baseStart_566530 := by decide
  rcases family_descends (prefixWord ++ tailWord_566530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566536 : List Nat := [2, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_566536 : Nat := 118140960795 + 566536 * 2 ^ 59
def prefixEnd_566536 : Nat := 4983230072969 + 3 ^ 40 * 566536 * 2
def baseEnd_566536 : Nat := 129291233811422515108691

theorem tailTrace_566536 : CollatzResearch.WordTrace tailWord_566536 prefixEnd_566536 129291233811422515108691 := by
  unfold tailWord_566536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331632737772151745359731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13775510317029535660479641 10331632737772151745359731)
  ·
    refine ⟨15497449106658227618039597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10331632737772151745359731 15497449106658227618039597)
    ·
      refine ⟨5811543414996835356764849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15497449106658227618039597 5811543414996835356764849)
      ·
        refine ⟨4358657561247626517573637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5811543414996835356764849 4358657561247626517573637)
        ·
          refine ⟨817248292733929972045057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4358657561247626517573637 817248292733929972045057)
          ·
            refine ⟨612936219550447479033793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817248292733929972045057 612936219550447479033793)
            ·
              refine ⟨459702164662835609275345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612936219550447479033793 459702164662835609275345)
              ·
                refine ⟨344776623497126706956509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459702164662835609275345 344776623497126706956509)
                ·
                  refine ⟨129291233811422515108691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344776623497126706956509 129291233811422515108691)
                  ·
                    rfl

theorem cell21_566536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_566536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566536 prefixEnd_566536 := by exact prefixLift 566536
  have htrace : WordTrace (prefixWord ++ tailWord_566536) baseStart_566536 baseEnd_566536 := by
    simpa [prefixWord, tailWord_566536, baseEnd_566536] using wordTrace_append hprefix tailTrace_566536
  have hstable : (prefixWord ++ tailWord_566536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566536).length < 2 ^ (prefixWord ++ tailWord_566536).sum := by decide
  have hdescent : baseEnd_566536 < baseStart_566536 := by decide
  rcases family_descends (prefixWord ++ tailWord_566536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566578 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_566578 : Nat := 118140960795 + 566578 * 2 ^ 59
def prefixEnd_566578 : Nat := 4983230072969 + 3 ^ 40 * 566578 * 2
def baseEnd_566578 : Nat := 129300818783639775408605

theorem tailTrace_566578 : CollatzResearch.WordTrace tailWord_566578 prefixEnd_566578 129300818783639775408605 := by
  unfold tailWord_566578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5166199335348036165937097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13776531560928096442498925 5166199335348036165937097)
  ·
    refine ⟨3874649501511027124452823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5166199335348036165937097 3874649501511027124452823)
    ·
      refine ⟨5811974252266540686679235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3874649501511027124452823 5811974252266540686679235)
      ·
        refine ⟨8717961378399811030018853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811974252266540686679235 8717961378399811030018853)
        ·
          refine ⟨1634617758449964568128535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8717961378399811030018853 1634617758449964568128535)
          ·
            refine ⟨2451926637674946852192803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634617758449964568128535 2451926637674946852192803)
            ·
              refine ⟨3677889956512420278289205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451926637674946852192803 3677889956512420278289205)
              ·
                refine ⟨344802183423039401089613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3677889956512420278289205 344802183423039401089613)
                ·
                  refine ⟨129300818783639775408605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344802183423039401089613 129300818783639775408605)
                  ·
                    rfl

theorem cell21_566578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_566578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566578 prefixEnd_566578 := by exact prefixLift 566578
  have htrace : WordTrace (prefixWord ++ tailWord_566578) baseStart_566578 baseEnd_566578 := by
    simpa [prefixWord, tailWord_566578, baseEnd_566578] using wordTrace_append hprefix tailTrace_566578
  have hstable : (prefixWord ++ tailWord_566578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566578).length < 2 ^ (prefixWord ++ tailWord_566578).sum := by decide
  have hdescent : baseEnd_566578 < baseStart_566578 := by decide
  rcases family_descends (prefixWord ++ tailWord_566578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566651 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_566651 : Nat := 118140960795 + 566651 * 2 ^ 59
def prefixEnd_566651 : Nat := 4983230072969 + 3 ^ 40 * 566651 * 2
def baseEnd_566651 : Nat := 129317478378207870691789

theorem tailTrace_566651 : CollatzResearch.WordTrace tailWord_566651 prefixEnd_566651 129317478378207870691789 := by
  unfold tailWord_566651
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667459870127678131155807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13778306580085118754103871 20667459870127678131155807)
  ·
    refine ⟨31001189805191517196733711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20667459870127678131155807 31001189805191517196733711)
    ·
      refine ⟨46501784707787275795100567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31001189805191517196733711 46501784707787275795100567)
      ·
        refine ⟨69752677061680913692650851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46501784707787275795100567 69752677061680913692650851)
        ·
          refine ⟨104629015592521370538976277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69752677061680913692650851 104629015592521370538976277)
          ·
            refine ⟨4904485105899439244014513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104629015592521370538976277 4904485105899439244014513)
            ·
              refine ⟨3678363829424579433010885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904485105899439244014513 3678363829424579433010885)
              ·
                refine ⟨689693218017108643689541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3678363829424579433010885 689693218017108643689541)
                ·
                  refine ⟨129317478378207870691789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689693218017108643689541 129317478378207870691789)
                  ·
                    rfl

theorem cell21_566651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_566651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566651 prefixEnd_566651 := by exact prefixLift 566651
  have htrace : WordTrace (prefixWord ++ tailWord_566651) baseStart_566651 baseEnd_566651 := by
    simpa [prefixWord, tailWord_566651, baseEnd_566651] using wordTrace_append hprefix tailTrace_566651
  have hstable : (prefixWord ++ tailWord_566651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566651).length < 2 ^ (prefixWord ++ tailWord_566651).sum := by decide
  have hdescent : baseEnd_566651 < baseStart_566651 := by decide
  rcases family_descends (prefixWord ++ tailWord_566651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566716 : List Nat := [2, 2, 2, 4, 3, 1, 1, 6]
def baseStart_566716 : Nat := 118140960795 + 566716 * 2 ^ 59
def prefixEnd_566716 : Nat := 4983230072969 + 3 ^ 40 * 566716 * 2
def baseEnd_566716 : Nat := 43110770754594067369441

theorem tailTrace_566716 : CollatzResearch.WordTrace tailWord_566716 prefixEnd_566716 43110770754594067369441 := by
  unfold tailWord_566716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10334915307446097116136001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13779887076594796154848001 10334915307446097116136001)
  ·
    refine ⟨7751186480584572837102001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10334915307446097116136001 7751186480584572837102001)
    ·
      refine ⟨5813389860438429627826501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7751186480584572837102001 5813389860438429627826501)
      ·
        refine ⟨1090010598832205555217469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5813389860438429627826501 1090010598832205555217469)
        ·
          refine ⟨408753974562077083206551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090010598832205555217469 408753974562077083206551)
          ·
            refine ⟨613130961843115624809827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408753974562077083206551 613130961843115624809827)
            ·
              refine ⟨919696442764673437214741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613130961843115624809827 919696442764673437214741)
              ·
                refine ⟨43110770754594067369441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 919696442764673437214741 43110770754594067369441)
                ·
                  rfl

theorem cell21_566716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_566716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566716 prefixEnd_566716 := by exact prefixLift 566716
  have htrace : WordTrace (prefixWord ++ tailWord_566716) baseStart_566716 baseEnd_566716 := by
    simpa [prefixWord, tailWord_566716, baseEnd_566716] using wordTrace_append hprefix tailTrace_566716
  have hstable : (prefixWord ++ tailWord_566716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566716).length < 2 ^ (prefixWord ++ tailWord_566716).sum := by decide
  have hdescent : baseEnd_566716 < baseStart_566716 := by decide
  rcases family_descends (prefixWord ++ tailWord_566716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566727 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_566727 : Nat := 118140960795 + 566727 * 2 ^ 59
def prefixEnd_566727 : Nat := 4983230072969 + 3 ^ 40 * 566727 * 2
def baseEnd_566727 : Nat := 129334822613648627424967

theorem tailTrace_566727 : CollatzResearch.WordTrace tailWord_566727 prefixEnd_566727 129334822613648627424967 := by
  unfold tailWord_566727
  simp only [CollatzResearch.WordTrace]
  refine ⟨20670231817852343110922435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780154545234895407281623 20670231817852343110922435)
  ·
    refine ⟨31005347726778514666383653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20670231817852343110922435 31005347726778514666383653)
    ·
      refine ⟨5813502698770971499946935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31005347726778514666383653 5813502698770971499946935)
      ·
        refine ⟨8720254048156457249920403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813502698770971499946935 8720254048156457249920403)
        ·
          refine ⟨13080381072234685874880605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8720254048156457249920403 13080381072234685874880605)
          ·
            refine ⟨4905142902088007203080227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13080381072234685874880605 4905142902088007203080227)
            ·
              refine ⟨7357714353132010804620341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905142902088007203080227 7357714353132010804620341)
              ·
                refine ⟨689785720606126012933157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7357714353132010804620341 689785720606126012933157)
                ·
                  refine ⟨129334822613648627424967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689785720606126012933157 129334822613648627424967)
                  ·
                    rfl

theorem cell21_566727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_566727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566727 prefixEnd_566727 := by exact prefixLift 566727
  have htrace : WordTrace (prefixWord ++ tailWord_566727) baseStart_566727 baseEnd_566727 := by
    simpa [prefixWord, tailWord_566727, baseEnd_566727] using wordTrace_append hprefix tailTrace_566727
  have hstable : (prefixWord ++ tailWord_566727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566727).length < 2 ^ (prefixWord ++ tailWord_566727).sum := by decide
  have hdescent : baseEnd_566727 < baseStart_566727 := by decide
  rcases family_descends (prefixWord ++ tailWord_566727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566817 : List Nat := [1, 2, 3, 2, 2, 2, 9]
def baseStart_566817 : Nat := 118140960795 + 566817 * 2 ^ 59
def prefixEnd_566817 : Nat := 4983230072969 + 3 ^ 40 * 566817 * 2
def baseEnd_566817 : Nat := 14372817982203163436087

theorem tailTrace_566817 : CollatzResearch.WordTrace tailWord_566817 prefixEnd_566817 14372817982203163436087 := by
  unfold tailWord_566817
  simp only [CollatzResearch.WordTrace]
  refine ⟨20673514387526288481698705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13782342925017525654465803 20673514387526288481698705)
  ·
    refine ⟨15505135790644716361274029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20673514387526288481698705 15505135790644716361274029)
    ·
      refine ⟨5814425921491768635477761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15505135790644716361274029 5814425921491768635477761)
      ·
        refine ⟨4360819441118826476608321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5814425921491768635477761 4360819441118826476608321)
        ·
          refine ⟨3270614580839119857456241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360819441118826476608321 3270614580839119857456241)
          ·
            refine ⟨2452960935629339893092181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270614580839119857456241 2452960935629339893092181)
            ·
              refine ⟨14372817982203163436087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2452960935629339893092181 14372817982203163436087)
              ·
                rfl

theorem cell21_566817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 9].length) (baseStart_566817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566817 prefixEnd_566817 := by exact prefixLift 566817
  have htrace : WordTrace (prefixWord ++ tailWord_566817) baseStart_566817 baseEnd_566817 := by
    simpa [prefixWord, tailWord_566817, baseEnd_566817] using wordTrace_append hprefix tailTrace_566817
  have hstable : (prefixWord ++ tailWord_566817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566817).length < 2 ^ (prefixWord ++ tailWord_566817).sum := by decide
  have hdescent : baseEnd_566817 < baseStart_566817 := by decide
  rcases family_descends (prefixWord ++ tailWord_566817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566837 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 4]
def baseStart_566837 : Nat := 118140960795 + 566837 * 2 ^ 59
def prefixEnd_566837 : Nat := 4983230072969 + 3 ^ 40 * 566837 * 2
def baseEnd_566837 : Nat := 129359926112312880591409

theorem tailTrace_566837 : CollatzResearch.WordTrace tailWord_566837 prefixEnd_566837 129359926112312880591409 := by
  unfold tailWord_566837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674243847453831897426765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13782829231635887931617843 20674243847453831897426765)
  ·
    refine ⟨7752841442795186961535037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20674243847453831897426765 7752841442795186961535037)
    ·
      refine ⟨2907315541048195110575639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7752841442795186961535037 2907315541048195110575639)
      ·
        refine ⟨4360973311572292665863459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907315541048195110575639 4360973311572292665863459)
        ·
          refine ⟨6541459967358438998795189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360973311572292665863459 6541459967358438998795189)
          ·
            refine ⟨613261871939853656137049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6541459967358438998795189 613261871939853656137049)
            ·
              refine ⟨459946403954890242102787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613261871939853656137049 459946403954890242102787)
              ·
                refine ⟨689919605932335363154181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459946403954890242102787 689919605932335363154181)
                ·
                  refine ⟨129359926112312880591409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689919605932335363154181 129359926112312880591409)
                  ·
                    rfl

theorem cell21_566837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_566837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566837 prefixEnd_566837 := by exact prefixLift 566837
  have htrace : WordTrace (prefixWord ++ tailWord_566837) baseStart_566837 baseEnd_566837 := by
    simpa [prefixWord, tailWord_566837, baseEnd_566837] using wordTrace_append hprefix tailTrace_566837
  have hstable : (prefixWord ++ tailWord_566837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566837).length < 2 ^ (prefixWord ++ tailWord_566837).sum := by decide
  have hdescent : baseEnd_566837 < baseStart_566837 := by decide
  rcases family_descends (prefixWord ++ tailWord_566837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566865 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 3]
def baseStart_566865 : Nat := 118140960795 + 566865 * 2 ^ 59
def prefixEnd_566865 : Nat := 4983230072969 + 3 ^ 40 * 566865 * 2
def baseEnd_566865 : Nat := 129366316093791054124685

theorem tailTrace_566865 : CollatzResearch.WordTrace tailWord_566865 prefixEnd_566865 129366316093791054124685 := by
  unfold tailWord_566865
  simp only [CollatzResearch.WordTrace]
  refine ⟨20675265091352392679446049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13783510060901595119630699 20675265091352392679446049)
  ·
    refine ⟨15506448818514294509584537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20675265091352392679446049 15506448818514294509584537)
    ·
      refine ⟨11629836613885720882188403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15506448818514294509584537 11629836613885720882188403)
      ·
        refine ⟨17444754920828581323282605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629836613885720882188403 17444754920828581323282605)
        ·
          refine ⟨6541783095310717996230977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17444754920828581323282605 6541783095310717996230977)
          ·
            refine ⟨4906337321483038497173233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6541783095310717996230977 4906337321483038497173233)
            ·
              refine ⟨3679752991112278872879925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4906337321483038497173233 3679752991112278872879925)
              ·
                refine ⟨344976842916776144332493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3679752991112278872879925 344976842916776144332493)
                ·
                  refine ⟨129366316093791054124685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344976842916776144332493 129366316093791054124685)
                  ·
                    rfl

theorem cell21_566865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_566865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566865 prefixEnd_566865 := by exact prefixLift 566865
  have htrace : WordTrace (prefixWord ++ tailWord_566865) baseStart_566865 baseEnd_566865 := by
    simpa [prefixWord, tailWord_566865, baseEnd_566865] using wordTrace_append hprefix tailTrace_566865
  have hstable : (prefixWord ++ tailWord_566865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566865).length < 2 ^ (prefixWord ++ tailWord_566865).sum := by decide
  have hdescent : baseEnd_566865 < baseStart_566865 := by decide
  rcases family_descends (prefixWord ++ tailWord_566865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566930 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 4]
def baseStart_566930 : Nat := 118140960795 + 566930 * 2 ^ 59
def prefixEnd_566930 : Nat := 4983230072969 + 3 ^ 40 * 566930 * 2
def baseEnd_566930 : Nat := 129381149979365385541219

theorem tailTrace_566930 : CollatzResearch.WordTrace tailWord_566930 prefixEnd_566930 129381149979365385541219 := by
  unfold tailWord_566930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169408959029227195140561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13785090557411272520374829 5169408959029227195140561)
  ·
    refine ⟨3877056719271920396355421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5169408959029227195140561 3877056719271920396355421)
    ·
      refine ⟨1453896269726970148633283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3877056719271920396355421 1453896269726970148633283)
      ·
        refine ⟨2180844404590455222949925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453896269726970148633283 2180844404590455222949925)
        ·
          refine ⟨408908325860710354303111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2180844404590455222949925 408908325860710354303111)
          ·
            refine ⟨613362488791065531454667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408908325860710354303111 613362488791065531454667)
            ·
              refine ⟨920043733186598297182001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613362488791065531454667 920043733186598297182001)
              ·
                refine ⟨690032799889948722886501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920043733186598297182001 690032799889948722886501)
                ·
                  refine ⟨129381149979365385541219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690032799889948722886501 129381149979365385541219)
                  ·
                    rfl

theorem cell21_566930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_566930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566930 prefixEnd_566930 := by exact prefixLift 566930
  have htrace : WordTrace (prefixWord ++ tailWord_566930) baseStart_566930 baseEnd_566930 := by
    simpa [prefixWord, tailWord_566930, baseEnd_566930] using wordTrace_append hprefix tailTrace_566930
  have hstable : (prefixWord ++ tailWord_566930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566930).length < 2 ^ (prefixWord ++ tailWord_566930).sum := by decide
  have hdescent : baseEnd_566930 < baseStart_566930 := by decide
  rcases family_descends (prefixWord ++ tailWord_566930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566986 : List Nat := [3, 1, 2, 1, 5, 2, 7]
def baseStart_566986 : Nat := 118140960795 + 566986 * 2 ^ 59
def prefixEnd_566986 : Nat := 4983230072969 + 3 ^ 40 * 566986 * 2
def baseEnd_566986 : Nat := 14377103326924636956419

theorem tailTrace_566986 : CollatzResearch.WordTrace tailWord_566986 prefixEnd_566986 14377103326924636956419 := by
  unfold tailWord_566986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169919580978507586150203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13786452215942686896400541 5169919580978507586150203)
  ·
    refine ⟨7754879371467761379225305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169919580978507586150203 7754879371467761379225305)
    ·
      refine ⟨5816159528600821034418979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754879371467761379225305 5816159528600821034418979)
      ·
        refine ⟨8724239292901231551628469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816159528600821034418979 8724239292901231551628469)
        ·
          refine ⟨817897433709490457965169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8724239292901231551628469 817897433709490457965169)
          ·
            refine ⟨613423075282117843473877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817897433709490457965169 613423075282117843473877)
            ·
              refine ⟨14377103326924636956419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 613423075282117843473877 14377103326924636956419)
              ·
                rfl

theorem cell21_566986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 7].length) (baseStart_566986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_566986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_566986 prefixEnd_566986 := by exact prefixLift 566986
  have htrace : WordTrace (prefixWord ++ tailWord_566986) baseStart_566986 baseEnd_566986 := by
    simpa [prefixWord, tailWord_566986, baseEnd_566986] using wordTrace_append hprefix tailTrace_566986
  have hstable : (prefixWord ++ tailWord_566986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566986).length < 2 ^ (prefixWord ++ tailWord_566986).sum := by decide
  have hdescent : baseEnd_566986 < baseStart_566986 := by decide
  rcases family_descends (prefixWord ++ tailWord_566986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567076 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_567076 : Nat := 118140960795 + 567076 * 2 ^ 59
def prefixEnd_567076 : Nat := 4983230072969 + 3 ^ 40 * 567076 * 2
def baseEnd_567076 : Nat := 129414469168501576107587

theorem tailTrace_567076 : CollatzResearch.WordTrace tailWord_567076 prefixEnd_567076 129414469168501576107587 := by
  unfold tailWord_567076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341480446793987857688541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13788640595725317143584721 10341480446793987857688541)
  ·
    refine ⟨3878055167547745446633203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10341480446793987857688541 3878055167547745446633203)
    ·
      refine ⟨5817082751321618169949805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878055167547745446633203 5817082751321618169949805)
      ·
        refine ⟨2181406031745606813731177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5817082751321618169949805 2181406031745606813731177)
        ·
          refine ⟨1636054523809205110298383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181406031745606813731177 1636054523809205110298383)
          ·
            refine ⟨2454081785713807665447575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636054523809205110298383 2454081785713807665447575)
            ·
              refine ⟨3681122678570711498171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454081785713807665447575 3681122678570711498171363)
              ·
                refine ⟨5521684017856067247257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681122678570711498171363 5521684017856067247257045)
                ·
                  refine ⟨129414469168501576107587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5521684017856067247257045 129414469168501576107587)
                  ·
                    rfl

theorem cell21_567076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_567076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567076 prefixEnd_567076 := by exact prefixLift 567076
  have htrace : WordTrace (prefixWord ++ tailWord_567076) baseStart_567076 baseEnd_567076 := by
    simpa [prefixWord, tailWord_567076, baseEnd_567076] using wordTrace_append hprefix tailTrace_567076
  have hstable : (prefixWord ++ tailWord_567076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567076).length < 2 ^ (prefixWord ++ tailWord_567076).sum := by decide
  have hdescent : baseEnd_567076 < baseStart_567076 := by decide
  rcases family_descends (prefixWord ++ tailWord_567076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567107 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_567107 : Nat := 118140960795 + 567107 * 2 ^ 59
def prefixEnd_567107 : Nat := 4983230072969 + 3 ^ 40 * 567107 * 2
def baseEnd_567107 : Nat := 129421543790852411090857

theorem tailTrace_567107 : CollatzResearch.WordTrace tailWord_567107 prefixEnd_567107 129421543790852411090857 := by
  unfold tailWord_567107
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684091556475668009755575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13789394370983778673170383 20684091556475668009755575)
  ·
    refine ⟨31026137334713502014633363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20684091556475668009755575 31026137334713502014633363)
    ·
      refine ⟨46539206002070253021950045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31026137334713502014633363 46539206002070253021950045)
      ·
        refine ⟨17452202250776344883231267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46539206002070253021950045 17452202250776344883231267)
        ·
          refine ⟨26178303376164517324846901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17452202250776344883231267 26178303376164517324846901)
          ·
            refine ⟨2454215941515423499204397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26178303376164517324846901 2454215941515423499204397)
            ·
              refine ⟨920330978068283812201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454215941515423499204397 920330978068283812201649)
              ·
                refine ⟨690248233551212859151237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920330978068283812201649 690248233551212859151237)
                ·
                  refine ⟨129421543790852411090857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690248233551212859151237 129421543790852411090857)
                  ·
                    rfl

theorem cell21_567107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_567107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567107 prefixEnd_567107 := by exact prefixLift 567107
  have htrace : WordTrace (prefixWord ++ tailWord_567107) baseStart_567107 baseEnd_567107 := by
    simpa [prefixWord, tailWord_567107, baseEnd_567107] using wordTrace_append hprefix tailTrace_567107
  have hstable : (prefixWord ++ tailWord_567107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567107).length < 2 ^ (prefixWord ++ tailWord_567107).sum := by decide
  have hdescent : baseEnd_567107 < baseStart_567107 := by decide
  rcases family_descends (prefixWord ++ tailWord_567107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567110 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_567110 : Nat := 118140960795 + 567110 * 2 ^ 59
def prefixEnd_567110 : Nat := 4983230072969 + 3 ^ 40 * 567110 * 2
def baseEnd_567110 : Nat := 129422228431725072540851

theorem tailTrace_567110 : CollatzResearch.WordTrace tailWord_567110 prefixEnd_567110 129422228431725072540851 := by
  unfold tailWord_567110
  simp only [CollatzResearch.WordTrace]
  refine ⟨646381280483274985066087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13789467316976533014743189 646381280483274985066087)
  ·
    refine ⟨969571920724912477599131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646381280483274985066087 969571920724912477599131)
    ·
      refine ⟨1454357881087368716398697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969571920724912477599131 1454357881087368716398697)
      ·
        refine ⟨1090768410815526537299023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1454357881087368716398697 1090768410815526537299023)
        ·
          refine ⟨1636152616223289805948535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090768410815526537299023 1636152616223289805948535)
          ·
            refine ⟨2454228924334934708922803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636152616223289805948535 2454228924334934708922803)
            ·
              refine ⟨3681343386502402063384205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454228924334934708922803 3681343386502402063384205)
              ·
                refine ⟨1380503769938400773769077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3681343386502402063384205 1380503769938400773769077)
                ·
                  refine ⟨129422228431725072540851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1380503769938400773769077 129422228431725072540851)
                  ·
                    rfl

theorem cell21_567110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_567110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567110 prefixEnd_567110 := by exact prefixLift 567110
  have htrace : WordTrace (prefixWord ++ tailWord_567110) baseStart_567110 baseEnd_567110 := by
    simpa [prefixWord, tailWord_567110, baseEnd_567110] using wordTrace_append hprefix tailTrace_567110
  have hstable : (prefixWord ++ tailWord_567110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567110).length < 2 ^ (prefixWord ++ tailWord_567110).sum := by decide
  have hdescent : baseEnd_567110 < baseStart_567110 := by decide
  rcases family_descends (prefixWord ++ tailWord_567110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567138 : List Nat := [3, 3, 2, 1, 2, 2, 1, 7]
def baseStart_567138 : Nat := 118140960795 + 567138 * 2 ^ 59
def prefixEnd_567138 : Nat := 4983230072969 + 3 ^ 40 * 567138 * 2
def baseEnd_567138 : Nat := 43142872804401082024709

theorem tailTrace_567138 : CollatzResearch.WordTrace tailWord_567138 prefixEnd_567138 43142872804401082024709 := by
  unfold tailWord_567138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171305554840840076033517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13790148146242240202756045 5171305554840840076033517)
  ·
    refine ⟨1939239583065315028512569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5171305554840840076033517 1939239583065315028512569)
    ·
      refine ⟨1454429687298986271384427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1939239583065315028512569 1454429687298986271384427)
      ·
        refine ⟨2181644530948479407076641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454429687298986271384427 2181644530948479407076641)
        ·
          refine ⟨1636233398211359555307481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181644530948479407076641 1636233398211359555307481)
          ·
            refine ⟨1227175048658519666480611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636233398211359555307481 1227175048658519666480611)
            ·
              refine ⟨1840762572987779499720917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227175048658519666480611 1840762572987779499720917)
              ·
                refine ⟨43142872804401082024709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1840762572987779499720917 43142872804401082024709)
                ·
                  rfl

theorem cell21_567138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_567138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567138 prefixEnd_567138 := by exact prefixLift 567138
  have htrace : WordTrace (prefixWord ++ tailWord_567138) baseStart_567138 baseEnd_567138 := by
    simpa [prefixWord, tailWord_567138, baseEnd_567138] using wordTrace_append hprefix tailTrace_567138
  have hstable : (prefixWord ++ tailWord_567138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567138).length < 2 ^ (prefixWord ++ tailWord_567138).sum := by decide
  have hdescent : baseEnd_567138 < baseStart_567138 := by decide
  rcases family_descends (prefixWord ++ tailWord_567138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567197 : List Nat := [1, 4, 2, 1, 2, 2, 2, 7]
def baseStart_567197 : Nat := 118140960795 + 567197 * 2 ^ 59
def prefixEnd_567197 : Nat := 4983230072969 + 3 ^ 40 * 567197 * 2
def baseEnd_567197 : Nat := 43147361005677418196891

theorem tailTrace_567197 : CollatzResearch.WordTrace tailWord_567197 prefixEnd_567197 43147361005677418196891 := by
  unfold tailWord_567197
  simp only [CollatzResearch.WordTrace]
  refine ⟨20687374126149613380531845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13791582750766408920354563 20687374126149613380531845)
  ·
    refine ⟨3878882648653052508849721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20687374126149613380531845 3878882648653052508849721)
    ·
      refine ⟨2909161986489789381637291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3878882648653052508849721 2909161986489789381637291)
      ·
        refine ⟨4363742979734684072455937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909161986489789381637291 4363742979734684072455937)
        ·
          refine ⟨3272807234801013054341953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363742979734684072455937 3272807234801013054341953)
          ·
            refine ⟨2454605426100759790756465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272807234801013054341953 2454605426100759790756465)
            ·
              refine ⟨1840954069575569843067349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454605426100759790756465 1840954069575569843067349)
              ·
                refine ⟨43147361005677418196891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1840954069575569843067349 43147361005677418196891)
                ·
                  rfl

theorem cell21_567197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_567197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567197 prefixEnd_567197 := by exact prefixLift 567197
  have htrace : WordTrace (prefixWord ++ tailWord_567197) baseStart_567197 baseEnd_567197 := by
    simpa [prefixWord, tailWord_567197, baseEnd_567197] using wordTrace_append hprefix tailTrace_567197
  have hstable : (prefixWord ++ tailWord_567197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567197).length < 2 ^ (prefixWord ++ tailWord_567197).sum := by decide
  have hdescent : baseEnd_567197 < baseStart_567197 := by decide
  rcases family_descends (prefixWord ++ tailWord_567197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567366 : List Nat := [6, 1, 1, 1, 1, 1, 1, 9]
def baseStart_567366 : Nat := 118140960795 + 567366 * 2 ^ 59
def prefixEnd_567366 : Nat := 4983230072969 + 3 ^ 40 * 567366 * 2
def baseEnd_567366 : Nat := 43160217039841838757887

theorem tailTrace_567366 : CollatzResearch.WordTrace tailWord_567366 prefixEnd_567366 43160217039841838757887 := by
  unfold tailWord_567366
  simp only [CollatzResearch.WordTrace]
  refine ⟨646673064454292351357311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13795692041691570162289301 646673064454292351357311)
  ·
    refine ⟨970009596681438527035967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646673064454292351357311 970009596681438527035967)
    ·
      refine ⟨1455014395022157790553951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970009596681438527035967 1455014395022157790553951)
      ·
        refine ⟨2182521592533236685830927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455014395022157790553951 2182521592533236685830927)
        ·
          refine ⟨3273782388799855028746391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182521592533236685830927 3273782388799855028746391)
          ·
            refine ⟨4910673583199782543119587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273782388799855028746391 4910673583199782543119587)
            ·
              refine ⟨7366010374799673814679381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910673583199782543119587 7366010374799673814679381)
              ·
                refine ⟨43160217039841838757887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7366010374799673814679381 43160217039841838757887)
                ·
                  rfl

theorem cell21_567366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_567366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567366 prefixEnd_567366 := by exact prefixLift 567366
  have htrace : WordTrace (prefixWord ++ tailWord_567366) baseStart_567366 baseEnd_567366 := by
    simpa [prefixWord, tailWord_567366, baseEnd_567366] using wordTrace_append hprefix tailTrace_567366
  have hstable : (prefixWord ++ tailWord_567366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567366).length < 2 ^ (prefixWord ++ tailWord_567366).sum := by decide
  have hdescent : baseEnd_567366 < baseStart_567366 := by decide
  rcases family_descends (prefixWord ++ tailWord_567366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567397 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 3]
def baseStart_567397 : Nat := 118140960795 + 567397 * 2 ^ 59
def prefixEnd_567397 : Nat := 4983230072969 + 3 ^ 40 * 567397 * 2
def baseEnd_567397 : Nat := 129487725741876351256931

theorem tailTrace_567397 : CollatzResearch.WordTrace tailWord_567397 prefixEnd_567397 129487725741876351256931 := by
  unfold tailWord_567397
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694668725425047537812445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13796445816950031691874963 20694668725425047537812445)
  ·
    refine ⟨7760500772034392826679667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20694668725425047537812445 7760500772034392826679667)
    ·
      refine ⟨11640751158051589240019501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7760500772034392826679667 11640751158051589240019501)
      ·
        refine ⟨4365281684269345965007313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11640751158051589240019501 4365281684269345965007313)
        ·
          refine ⟨3273961263202009473755485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365281684269345965007313 3273961263202009473755485)
          ·
            refine ⟨1227735473700753552658307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3273961263202009473755485 1227735473700753552658307)
            ·
              refine ⟨1841603210551130328987461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227735473700753552658307 1841603210551130328987461)
              ·
                refine ⟨345300601978336936685149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1841603210551130328987461 345300601978336936685149)
                ·
                  refine ⟨129487725741876351256931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345300601978336936685149 129487725741876351256931)
                  ·
                    rfl

theorem cell21_567397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_567397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567397 prefixEnd_567397 := by exact prefixLift 567397
  have htrace : WordTrace (prefixWord ++ tailWord_567397) baseStart_567397 baseEnd_567397 := by
    simpa [prefixWord, tailWord_567397, baseEnd_567397] using wordTrace_append hprefix tailTrace_567397
  have hstable : (prefixWord ++ tailWord_567397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567397).length < 2 ^ (prefixWord ++ tailWord_567397).sum := by decide
  have hdescent : baseEnd_567397 < baseStart_567397 := by decide
  rcases family_descends (prefixWord ++ tailWord_567397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567456 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_567456 : Nat := 118140960795 + 567456 * 2 ^ 59
def prefixEnd_567456 : Nat := 4983230072969 + 3 ^ 40 * 567456 * 2
def baseEnd_567456 : Nat := 129501190345705359773477

theorem tailTrace_567456 : CollatzResearch.WordTrace tailWord_567456 prefixEnd_567456 129501190345705359773477 := by
  unfold tailWord_567456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348410316105650307105111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13797880421474200409473481 10348410316105650307105111)
  ·
    refine ⟨15522615474158475460657667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10348410316105650307105111 15522615474158475460657667)
    ·
      refine ⟨23283923211237713190986501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15522615474158475460657667 23283923211237713190986501)
      ·
        refine ⟨4365735602107071223309969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23283923211237713190986501 4365735602107071223309969)
        ·
          refine ⟨3274301701580303417482477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365735602107071223309969 3274301701580303417482477)
          ·
            refine ⟨1227863138092613781555929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3274301701580303417482477 1227863138092613781555929)
            ·
              refine ⟨920897353569460336166947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227863138092613781555929 920897353569460336166947)
              ·
                refine ⟨1381346030354190504250421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920897353569460336166947 1381346030354190504250421)
                ·
                  refine ⟨129501190345705359773477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381346030354190504250421 129501190345705359773477)
                  ·
                    rfl

theorem cell21_567456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_567456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567456 prefixEnd_567456 := by exact prefixLift 567456
  have htrace : WordTrace (prefixWord ++ tailWord_567456) baseStart_567456 baseEnd_567456 := by
    simpa [prefixWord, tailWord_567456, baseEnd_567456] using wordTrace_append hprefix tailTrace_567456
  have hstable : (prefixWord ++ tailWord_567456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567456).length < 2 ^ (prefixWord ++ tailWord_567456).sum := by decide
  have hdescent : baseEnd_567456 < baseStart_567456 := by decide
  rcases family_descends (prefixWord ++ tailWord_567456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567476 : List Nat := [2, 5, 3, 1, 1, 1, 1, 7]
def baseStart_567476 : Nat := 118140960795 + 567476 * 2 ^ 59
def prefixEnd_567476 : Nat := 4983230072969 + 3 ^ 40 * 567476 * 2
def baseEnd_567476 : Nat := 43168584872729923146701

theorem tailTrace_567476 : CollatzResearch.WordTrace tailWord_567476 prefixEnd_567476 43168584872729923146701 := by
  unfold tailWord_567476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348775046069422014969141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13798366728092562686625521 10348775046069422014969141)
  ·
    refine ⟨970197660569008313903357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10348775046069422014969141 970197660569008313903357)
    ·
      refine ⟨363824122713378117713759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 970197660569008313903357 363824122713378117713759)
      ·
        refine ⟨545736184070067176570639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363824122713378117713759 545736184070067176570639)
        ·
          refine ⟨818604276105100764855959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545736184070067176570639 818604276105100764855959)
          ·
            refine ⟨1227906414157651147283939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818604276105100764855959 1227906414157651147283939)
            ·
              refine ⟨1841859621236476720925909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227906414157651147283939 1841859621236476720925909)
              ·
                refine ⟨43168584872729923146701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1841859621236476720925909 43168584872729923146701)
                ·
                  rfl

theorem cell21_567476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_567476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567476 prefixEnd_567476 := by exact prefixLift 567476
  have htrace : WordTrace (prefixWord ++ tailWord_567476) baseStart_567476 baseEnd_567476 := by
    simpa [prefixWord, tailWord_567476, baseEnd_567476] using wordTrace_append hprefix tailTrace_567476
  have hstable : (prefixWord ++ tailWord_567476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567476).length < 2 ^ (prefixWord ++ tailWord_567476).sum := by decide
  have hdescent : baseEnd_567476 < baseStart_567476 := by decide
  rcases family_descends (prefixWord ++ tailWord_567476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567560 : List Nat := [2, 1, 3, 2, 3, 10]
def baseStart_567560 : Nat := 118140960795 + 567560 * 2 ^ 59
def prefixEnd_567560 : Nat := 4983230072969 + 3 ^ 40 * 567560 * 2
def baseEnd_567560 : Nat := 4797219428245344075553

theorem tailTrace_567560 : CollatzResearch.WordTrace tailWord_567560 prefixEnd_567560 4797219428245344075553 := by
  unfold tailWord_567560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350306911917263187998067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13800409215889684250664089 10350306911917263187998067)
  ·
    refine ⟨15525460367875894781997101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350306911917263187998067 15525460367875894781997101)
    ·
      refine ⟨5822047637953460543248913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15525460367875894781997101 5822047637953460543248913)
      ·
        refine ⟨4366535728465095407436685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5822047637953460543248913 4366535728465095407436685)
        ·
          refine ⟨1637450898174410777788757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4366535728465095407436685 1637450898174410777788757)
          ·
            refine ⟨4797219428245344075553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1637450898174410777788757 4797219428245344075553)
            ·
              rfl

theorem cell21_567560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 10].length) (baseStart_567560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567560 prefixEnd_567560 := by exact prefixLift 567560
  have htrace : WordTrace (prefixWord ++ tailWord_567560) baseStart_567560 baseEnd_567560 := by
    simpa [prefixWord, tailWord_567560, baseEnd_567560] using wordTrace_append hprefix tailTrace_567560
  have hstable : (prefixWord ++ tailWord_567560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567560).length < 2 ^ (prefixWord ++ tailWord_567560).sum := by decide
  have hdescent : baseEnd_567560 < baseStart_567560 := by decide
  rcases family_descends (prefixWord ++ tailWord_567560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567608 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_567608 : Nat := 118140960795 + 567608 * 2 ^ 59
def prefixEnd_567608 : Nat := 4983230072969 + 3 ^ 40 * 567608 * 2
def baseEnd_567608 : Nat := 129535878816586873239833

theorem tailTrace_567608 : CollatzResearch.WordTrace tailWord_567608 prefixEnd_567608 129535878816586873239833 := by
  unfold tailWord_567608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351182263830315286871739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13801576351773753715828985 10351182263830315286871739)
  ·
    refine ⟨15526773395745472930307609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10351182263830315286871739 15526773395745472930307609)
    ·
      refine ⟨11645080046809104697730707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15526773395745472930307609 11645080046809104697730707)
      ·
        refine ⟨17467620070213657046596061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11645080046809104697730707 17467620070213657046596061)
        ·
          refine ⟨6550357526330121392473523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17467620070213657046596061 6550357526330121392473523)
          ·
            refine ⟨9825536289495182088710285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550357526330121392473523 9825536289495182088710285)
            ·
              refine ⟨3684576108560693283266357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9825536289495182088710285 3684576108560693283266357)
              ·
                refine ⟨345429010177564995306221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3684576108560693283266357 345429010177564995306221)
                ·
                  refine ⟨129535878816586873239833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345429010177564995306221 129535878816586873239833)
                  ·
                    rfl

theorem cell21_567608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_567608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567608 prefixEnd_567608 := by exact prefixLift 567608
  have htrace : WordTrace (prefixWord ++ tailWord_567608) baseStart_567608 baseEnd_567608 := by
    simpa [prefixWord, tailWord_567608, baseEnd_567608] using wordTrace_append hprefix tailTrace_567608
  have hstable : (prefixWord ++ tailWord_567608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567608).length < 2 ^ (prefixWord ++ tailWord_567608).sum := by decide
  have hdescent : baseEnd_567608 < baseStart_567608 := by decide
  rcases family_descends (prefixWord ++ tailWord_567608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567639 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 4]
def baseStart_567639 : Nat := 118140960795 + 567639 * 2 ^ 59
def prefixEnd_567639 : Nat := 4983230072969 + 3 ^ 40 * 567639 * 2
def baseEnd_567639 : Nat := 129542953438937708223103

theorem tailTrace_567639 : CollatzResearch.WordTrace tailWord_567639 prefixEnd_567639 129542953438937708223103 := by
  unfold tailWord_567639
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703495190548322868121971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13802330127032215245414647 20703495190548322868121971)
  ·
    refine ⟨31055242785822484302182957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20703495190548322868121971 31055242785822484302182957)
    ·
      refine ⟨11645716044683431613318609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31055242785822484302182957 11645716044683431613318609)
      ·
        refine ⟨8734287033512573709988957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11645716044683431613318609 8734287033512573709988957)
        ·
          refine ⟨3275357637567215141245859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8734287033512573709988957 3275357637567215141245859)
          ·
            refine ⟨4913036456350822711868789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275357637567215141245859 4913036456350822711868789)
            ·
              refine ⟨460597167782889629237699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4913036456350822711868789 460597167782889629237699)
              ·
                refine ⟨690895751674334443856549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460597167782889629237699 690895751674334443856549)
                ·
                  refine ⟨129542953438937708223103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690895751674334443856549 129542953438937708223103)
                  ·
                    rfl

theorem cell21_567639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 4].length) (baseStart_567639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567639 prefixEnd_567639 := by exact prefixLift 567639
  have htrace : WordTrace (prefixWord ++ tailWord_567639) baseStart_567639 baseEnd_567639 := by
    simpa [prefixWord, tailWord_567639, baseEnd_567639] using wordTrace_append hprefix tailTrace_567639
  have hstable : (prefixWord ++ tailWord_567639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567639).length < 2 ^ (prefixWord ++ tailWord_567639).sum := by decide
  have hdescent : baseEnd_567639 < baseStart_567639 := by decide
  rcases family_descends (prefixWord ++ tailWord_567639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567653 : List Nat := [1, 3, 1, 3, 1, 3, 4, 5]
def baseStart_567653 : Nat := 118140960795 + 567653 * 2 ^ 59
def prefixEnd_567653 : Nat := 4983230072969 + 3 ^ 40 * 567653 * 2
def baseEnd_567653 : Nat := 43182049476558931663247

theorem tailTrace_567653 : CollatzResearch.WordTrace tailWord_567653 prefixEnd_567653 43182049476558931663247 := by
  unfold tailWord_567653
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704005812497603259131613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13802670541665068839421075 20704005812497603259131613)
  ·
    refine ⟨7764002179686601222174355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20704005812497603259131613 7764002179686601222174355)
    ·
      refine ⟨11646003269529901833261533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7764002179686601222174355 11646003269529901833261533)
      ·
        refine ⟨4367251226073713187473075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11646003269529901833261533 4367251226073713187473075)
        ·
          refine ⟨6550876839110569781209613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367251226073713187473075 6550876839110569781209613)
          ·
            refine ⟨2456578814666463667953605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6550876839110569781209613 2456578814666463667953605)
            ·
              refine ⟨460608527749961937741301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2456578814666463667953605 460608527749961937741301)
              ·
                refine ⟨43182049476558931663247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460608527749961937741301 43182049476558931663247)
                ·
                  rfl

theorem cell21_567653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].length) (baseStart_567653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567653 prefixEnd_567653 := by exact prefixLift 567653
  have htrace : WordTrace (prefixWord ++ tailWord_567653) baseStart_567653 baseEnd_567653 := by
    simpa [prefixWord, tailWord_567653, baseEnd_567653] using wordTrace_append hprefix tailTrace_567653
  have hstable : (prefixWord ++ tailWord_567653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567653).length < 2 ^ (prefixWord ++ tailWord_567653).sum := by decide
  have hdescent : baseEnd_567653 < baseStart_567653 := by decide
  rcases family_descends (prefixWord ++ tailWord_567653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567690 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_567690 : Nat := 118140960795 + 567690 * 2 ^ 59
def prefixEnd_567690 : Nat := 4983230072969 + 3 ^ 40 * 567690 * 2
def baseEnd_567690 : Nat := 129554592333772952872999

theorem tailTrace_567690 : CollatzResearch.WordTrace tailWord_567690 prefixEnd_567690 129554592333772952872999 := by
  unfold tailWord_567690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5176338828340889644557131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13803570208909039052152349 5176338828340889644557131)
  ·
    refine ⟨7764508242511334466835697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5176338828340889644557131 7764508242511334466835697)
    ·
      refine ⟨5823381181883500850126773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7764508242511334466835697 5823381181883500850126773)
      ·
        refine ⟨545941985801578204699385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5823381181883500850126773 545941985801578204699385)
        ·
          refine ⟨409456489351183653524539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545941985801578204699385 409456489351183653524539)
          ·
            refine ⟨614184734026775480286809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409456489351183653524539 614184734026775480286809)
            ·
              refine ⟨460638550520081610215107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614184734026775480286809 460638550520081610215107)
              ·
                refine ⟨690957825780122415322661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460638550520081610215107 690957825780122415322661)
                ·
                  refine ⟨129554592333772952872999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690957825780122415322661 129554592333772952872999)
                  ·
                    rfl

theorem cell21_567690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_567690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567690 prefixEnd_567690 := by exact prefixLift 567690
  have htrace : WordTrace (prefixWord ++ tailWord_567690) baseStart_567690 baseEnd_567690 := by
    simpa [prefixWord, tailWord_567690, baseEnd_567690] using wordTrace_append hprefix tailTrace_567690
  have hstable : (prefixWord ++ tailWord_567690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567690).length < 2 ^ (prefixWord ++ tailWord_567690).sum := by decide
  have hdescent : baseEnd_567690 < baseStart_567690 := by decide
  rcases family_descends (prefixWord ++ tailWord_567690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567712 : List Nat := [2, 1, 1, 4, 1, 3, 2, 7]
def baseStart_567712 : Nat := 118140960795 + 567712 * 2 ^ 59
def prefixEnd_567712 : Nat := 4983230072969 + 3 ^ 40 * 567712 * 2
def baseEnd_567712 : Nat := 43186537677835267835429

theorem tailTrace_567712 : CollatzResearch.WordTrace tailWord_567712 prefixEnd_567712 43186537677835267835429 := by
  unfold tailWord_567712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353078859641928167764695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13804105146189237557019593 10353078859641928167764695)
  ·
    refine ⟨15529618289462892251647043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10353078859641928167764695 15529618289462892251647043)
    ·
      refine ⟨23294427434194338377470565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15529618289462892251647043 23294427434194338377470565)
      ·
        refine ⟨4367705143911438445775731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23294427434194338377470565 4367705143911438445775731)
        ·
          refine ⟨6551557715867157668663597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4367705143911438445775731 6551557715867157668663597)
          ·
            refine ⟨2456834143450184125748849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6551557715867157668663597 2456834143450184125748849)
            ·
              refine ⟨1842625607587638094311637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2456834143450184125748849 1842625607587638094311637)
              ·
                refine ⟨43186537677835267835429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1842625607587638094311637 43186537677835267835429)
                ·
                  rfl

theorem cell21_567712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_567712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567712 prefixEnd_567712 := by exact prefixLift 567712
  have htrace : WordTrace (prefixWord ++ tailWord_567712) baseStart_567712 baseEnd_567712 := by
    simpa [prefixWord, tailWord_567712, baseEnd_567712] using wordTrace_append hprefix tailTrace_567712
  have hstable : (prefixWord ++ tailWord_567712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567712).length < 2 ^ (prefixWord ++ tailWord_567712).sum := by decide
  have hdescent : baseEnd_567712 < baseStart_567712 := by decide
  rcases family_descends (prefixWord ++ tailWord_567712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567819 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_567819 : Nat := 118140960795 + 567819 * 2 ^ 59
def prefixEnd_567819 : Nat := 4983230072969 + 3 ^ 40 * 567819 * 2
def baseEnd_567819 : Nat := 129584031891297395222735

theorem tailTrace_567819 : CollatzResearch.WordTrace tailWord_567819 prefixEnd_567819 129584031891297395222735 := by
  unfold tailWord_567819
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710060329896213609674511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13806706886597475739783007 20710060329896213609674511)
  ·
    refine ⟨31065090494844320414511767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20710060329896213609674511 31065090494844320414511767)
    ·
      refine ⟨46597635742266480621767651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31065090494844320414511767 46597635742266480621767651)
      ·
        refine ⟨69896453613399720932651477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46597635742266480621767651 69896453613399720932651477)
        ·
          refine ⟨1638198131564055959359019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 69896453613399720932651477 1638198131564055959359019)
          ·
            refine ⟨2457297197346083939038529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638198131564055959359019 2457297197346083939038529)
            ·
              refine ⟨1842972898009562954278897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457297197346083939038529 1842972898009562954278897)
              ·
                refine ⟨1382229673507172215709173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1842972898009562954278897 1382229673507172215709173)
                ·
                  refine ⟨129584031891297395222735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382229673507172215709173 129584031891297395222735)
                  ·
                    rfl

theorem cell21_567819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_567819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567819 prefixEnd_567819 := by exact prefixLift 567819
  have htrace : WordTrace (prefixWord ++ tailWord_567819) baseStart_567819 baseEnd_567819 := by
    simpa [prefixWord, tailWord_567819, baseEnd_567819] using wordTrace_append hprefix tailTrace_567819
  have hstable : (prefixWord ++ tailWord_567819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567819).length < 2 ^ (prefixWord ++ tailWord_567819).sum := by decide
  have hdescent : baseEnd_567819 < baseStart_567819 := by decide
  rcases family_descends (prefixWord ++ tailWord_567819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567822 : List Nat := [4, 1, 1, 2, 3, 3, 2, 5]
def baseStart_567822 : Nat := 118140960795 + 567822 * 2 ^ 59
def prefixEnd_567822 : Nat := 4983230072969 + 3 ^ 40 * 567822 * 2
def baseEnd_567822 : Nat := 43194905510723352224243

theorem tailTrace_567822 : CollatzResearch.WordTrace tailWord_567822 prefixEnd_567822 43194905510723352224243 := by
  unfold tailWord_567822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588771218610668140254215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13806779832590230081355813 2588771218610668140254215)
  ·
    refine ⟨3883156827916002210381323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588771218610668140254215 3883156827916002210381323)
    ·
      refine ⟨5824735241874003315571985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883156827916002210381323 5824735241874003315571985)
      ·
        refine ⟨4368551431405502486678989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824735241874003315571985 4368551431405502486678989)
        ·
          refine ⟨1638206786777063432504621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4368551431405502486678989 1638206786777063432504621)
          ·
            refine ⟨614327545041398787189233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1638206786777063432504621 614327545041398787189233)
            ·
              refine ⟨460745658781049090391925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614327545041398787189233 460745658781049090391925)
              ·
                refine ⟨43194905510723352224243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460745658781049090391925 43194905510723352224243)
                ·
                  rfl

theorem cell21_567822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_567822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567822 prefixEnd_567822 := by exact prefixLift 567822
  have htrace : WordTrace (prefixWord ++ tailWord_567822) baseStart_567822 baseEnd_567822 := by
    simpa [prefixWord, tailWord_567822, baseEnd_567822] using wordTrace_append hprefix tailTrace_567822
  have hstable : (prefixWord ++ tailWord_567822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567822).length < 2 ^ (prefixWord ++ tailWord_567822).sum := by decide
  have hdescent : baseEnd_567822 < baseStart_567822 := by decide
  rcases family_descends (prefixWord ++ tailWord_567822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567850 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_567850 : Nat := 118140960795 + 567850 * 2 ^ 59
def prefixEnd_567850 : Nat := 4983230072969 + 3 ^ 40 * 567850 * 2
def baseEnd_567850 : Nat := 129591106513648230206005

theorem tailTrace_567850 : CollatzResearch.WordTrace tailWord_567850 prefixEnd_567850 129591106513648230206005 := by
  unfold tailWord_567850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177797748195976476013251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13807460661855937269368669 5177797748195976476013251)
  ·
    refine ⟨7766696622293964714019877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5177797748195976476013251 7766696622293964714019877)
    ·
      refine ⟨1456255616680118383878727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7766696622293964714019877 1456255616680118383878727)
      ·
        refine ⟨2184383425020177575818091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456255616680118383878727 2184383425020177575818091)
        ·
          refine ⟨3276575137530266363727137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184383425020177575818091 3276575137530266363727137)
          ·
            refine ⟨2457431353147699772795353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276575137530266363727137 2457431353147699772795353)
            ·
              refine ⟨1843073514860774829596515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457431353147699772795353 1843073514860774829596515)
              ·
                refine ⟨2764610272291162244394773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843073514860774829596515 2764610272291162244394773)
                ·
                  refine ⟨129591106513648230206005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2764610272291162244394773 129591106513648230206005)
                  ·
                    rfl

theorem cell21_567850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_567850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567850 prefixEnd_567850 := by exact prefixLift 567850
  have htrace : WordTrace (prefixWord ++ tailWord_567850) baseStart_567850 baseEnd_567850 := by
    simpa [prefixWord, tailWord_567850, baseEnd_567850] using wordTrace_append hprefix tailTrace_567850
  have hstable : (prefixWord ++ tailWord_567850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567850).length < 2 ^ (prefixWord ++ tailWord_567850).sum := by decide
  have hdescent : baseEnd_567850 < baseStart_567850 := by decide
  rcases family_descends (prefixWord ++ tailWord_567850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567864 : List Nat := [2, 1, 2, 1, 4, 1, 4, 6]
def baseStart_567864 : Nat := 118140960795 + 567864 * 2 ^ 59
def prefixEnd_567864 : Nat := 4983230072969 + 3 ^ 40 * 567864 * 2
def baseEnd_567864 : Nat := 43198100501462438990881

theorem tailTrace_567864 : CollatzResearch.WordTrace tailWord_567864 prefixEnd_567864 43198100501462438990881 := by
  unfold tailWord_567864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355850807366593147531323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13807801076488790863375097 10355850807366593147531323)
  ·
    refine ⟨15533776211049889721296985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10355850807366593147531323 15533776211049889721296985)
    ·
      refine ⟨11650332158287417290972739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15533776211049889721296985 11650332158287417290972739)
      ·
        refine ⟨17475498237431125936459109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650332158287417290972739 17475498237431125936459109)
        ·
          refine ⟨3276655919518336113086083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17475498237431125936459109 3276655919518336113086083)
          ·
            refine ⟨4914983879277504169629125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276655919518336113086083 4914983879277504169629125)
            ·
              refine ⟨921559477364532031805461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4914983879277504169629125 921559477364532031805461)
              ·
                refine ⟨43198100501462438990881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 921559477364532031805461 43198100501462438990881)
                ·
                  rfl

theorem cell21_567864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_567864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567864 prefixEnd_567864 := by exact prefixLift 567864
  have htrace : WordTrace (prefixWord ++ tailWord_567864) baseStart_567864 baseEnd_567864 := by
    simpa [prefixWord, tailWord_567864, baseEnd_567864] using wordTrace_append hprefix tailTrace_567864
  have hstable : (prefixWord ++ tailWord_567864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567864).length < 2 ^ (prefixWord ++ tailWord_567864).sum := by decide
  have hdescent : baseEnd_567864 < baseStart_567864 := by decide
  rcases family_descends (prefixWord ++ tailWord_567864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567923 : List Nat := [1, 1, 1, 2, 2, 1, 1, 12]
def baseStart_567923 : Nat := 118140960795 + 567923 * 2 ^ 59
def prefixEnd_567923 : Nat := 4983230072969 + 3 ^ 40 * 567923 * 2
def baseEnd_567923 : Nat := 43202588702738775163063

theorem tailTrace_567923 : CollatzResearch.WordTrace tailWord_567923 prefixEnd_567923 43202588702738775163063 := by
  unfold tailWord_567923
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713853521519439371460423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13809235681012959580973615 20713853521519439371460423)
  ·
    refine ⟨31070780282279159057190635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20713853521519439371460423 31070780282279159057190635)
    ·
      refine ⟨46606170423418738585785953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31070780282279159057190635 46606170423418738585785953)
      ·
        refine ⟨34954627817564053939339465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46606170423418738585785953 34954627817564053939339465)
        ·
          refine ⟨26215970863173040454504599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34954627817564053939339465 26215970863173040454504599)
          ·
            refine ⟨39323956294759560681756899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26215970863173040454504599 39323956294759560681756899)
            ·
              refine ⟨58985934442139341022635349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39323956294759560681756899 58985934442139341022635349)
              ·
                refine ⟨43202588702738775163063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 58985934442139341022635349 43202588702738775163063)
                ·
                  rfl

theorem cell21_567923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_567923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_567923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_567923 prefixEnd_567923 := by exact prefixLift 567923
  have htrace : WordTrace (prefixWord ++ tailWord_567923) baseStart_567923 baseEnd_567923 := by
    simpa [prefixWord, tailWord_567923, baseEnd_567923] using wordTrace_append hprefix tailTrace_567923
  have hstable : (prefixWord ++ tailWord_567923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567923).length < 2 ^ (prefixWord ++ tailWord_567923).sum := by decide
  have hdescent : baseEnd_567923 < baseStart_567923 := by decide
  rcases family_descends (prefixWord ++ tailWord_567923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568092 : List Nat := [2, 2, 3, 1, 1, 3, 3, 6]
def baseStart_568092 : Nat := 118140960795 + 568092 * 2 ^ 59
def prefixEnd_568092 : Nat := 4983230072969 + 3 ^ 40 * 568092 * 2
def baseEnd_568092 : Nat := 43215444736903195724059

theorem tailTrace_568092 : CollatzResearch.WordTrace tailWord_568092 prefixEnd_568092 43215444736903195724059 := by
  unfold tailWord_568092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360008728953590617181265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13813344971938120822908353 10360008728953590617181265)
  ·
    refine ⟨7770006546715192962885949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10360008728953590617181265 7770006546715192962885949)
    ·
      refine ⟨2913752455018197361082231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7770006546715192962885949 2913752455018197361082231)
      ·
        refine ⟨4370628682527296041623347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913752455018197361082231 4370628682527296041623347)
        ·
          refine ⟨6555943023790944062435021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370628682527296041623347 6555943023790944062435021)
          ·
            refine ⟨2458478633921604023413133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555943023790944062435021 2458478633921604023413133)
            ·
              refine ⟨921929487720601508779925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458478633921604023413133 921929487720601508779925)
              ·
                refine ⟨43215444736903195724059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 921929487720601508779925 43215444736903195724059)
                ·
                  rfl

theorem cell21_568092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_568092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568092 prefixEnd_568092 := by exact prefixLift 568092
  have htrace : WordTrace (prefixWord ++ tailWord_568092) baseStart_568092 baseEnd_568092 := by
    simpa [prefixWord, tailWord_568092, baseEnd_568092] using wordTrace_append hprefix tailTrace_568092
  have hstable : (prefixWord ++ tailWord_568092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568092).length < 2 ^ (prefixWord ++ tailWord_568092).sum := by decide
  have hdescent : baseEnd_568092 < baseStart_568092 := by decide
  rcases family_descends (prefixWord ++ tailWord_568092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568129 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 4]
def baseStart_568129 : Nat := 118140960795 + 568129 * 2 ^ 59
def prefixEnd_568129 : Nat := 4983230072969 + 3 ^ 40 * 568129 * 2
def baseEnd_568129 : Nat := 129654778114805745055435

theorem tailTrace_568129 : CollatzResearch.WordTrace tailWord_568129 prefixEnd_568129 129654778114805745055435 := by
  unfold tailWord_568129
  simp only [CollatzResearch.WordTrace]
  refine ⟨20721366958773136553459441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13814244639182091035639627 20721366958773136553459441)
  ·
    refine ⟨15541025219079852415094581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20721366958773136553459441 15541025219079852415094581)
    ·
      refine ⟨1456971114288736163915117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15541025219079852415094581 1456971114288736163915117)
      ·
        refine ⟨546364167858276061468169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456971114288736163915117 546364167858276061468169)
        ·
          refine ⟨409773125893707046101127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546364167858276061468169 409773125893707046101127)
          ·
            refine ⟨614659688840560569151691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409773125893707046101127 614659688840560569151691)
            ·
              refine ⟨921989533260840853727537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614659688840560569151691 921989533260840853727537)
              ·
                refine ⟨691492149945630640295653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921989533260840853727537 691492149945630640295653)
                ·
                  refine ⟨129654778114805745055435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691492149945630640295653 129654778114805745055435)
                  ·
                    rfl

theorem cell21_568129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_568129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568129 prefixEnd_568129 := by exact prefixLift 568129
  have htrace : WordTrace (prefixWord ++ tailWord_568129) baseStart_568129 baseEnd_568129 := by
    simpa [prefixWord, tailWord_568129, baseEnd_568129] using wordTrace_append hprefix tailTrace_568129
  have hstable : (prefixWord ++ tailWord_568129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568129).length < 2 ^ (prefixWord ++ tailWord_568129).sum := by decide
  have hdescent : baseEnd_568129 < baseStart_568129 := by decide
  rcases family_descends (prefixWord ++ tailWord_568129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568137 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_568137 : Nat := 118140960795 + 568137 * 2 ^ 59
def prefixEnd_568137 : Nat := 4983230072969 + 3 ^ 40 * 568137 * 2
def baseEnd_568137 : Nat := 129656603823799508922085

theorem tailTrace_568137 : CollatzResearch.WordTrace tailWord_568137 prefixEnd_568137 129656603823799508922085 := by
  unfold tailWord_568137
  simp only [CollatzResearch.WordTrace]
  refine ⟨20721658742744153919750665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13814439161829435946500443 20721658742744153919750665)
  ·
    refine ⟨15541244057058115439812999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20721658742744153919750665 15541244057058115439812999)
    ·
      refine ⟨23311866085587173159719499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541244057058115439812999 23311866085587173159719499)
      ·
        refine ⟨34967799128380759739579249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23311866085587173159719499 34967799128380759739579249)
        ·
          refine ⟨26225849346285569804684437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34967799128380759739579249 26225849346285569804684437)
          ·
            refine ⟨1229336688107136084594583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26225849346285569804684437 1229336688107136084594583)
            ·
              refine ⟨1844005032160704126891875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229336688107136084594583 1844005032160704126891875)
              ·
                refine ⟨2766007548241056190337813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844005032160704126891875 2766007548241056190337813)
                ·
                  refine ⟨129656603823799508922085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2766007548241056190337813 129656603823799508922085)
                  ·
                    rfl

theorem cell21_568137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_568137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568137 prefixEnd_568137 := by exact prefixLift 568137
  have htrace : WordTrace (prefixWord ++ tailWord_568137) baseStart_568137 baseEnd_568137 := by
    simpa [prefixWord, tailWord_568137, baseEnd_568137] using wordTrace_append hprefix tailTrace_568137
  have hstable : (prefixWord ++ tailWord_568137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568137).length < 2 ^ (prefixWord ++ tailWord_568137).sum := by decide
  have hdescent : baseEnd_568137 < baseStart_568137 := by decide
  rcases family_descends (prefixWord ++ tailWord_568137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568140 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_568140 : Nat := 118140960795 + 568140 * 2 ^ 59
def prefixEnd_568140 : Nat := 4983230072969 + 3 ^ 40 * 568140 * 2
def baseEnd_568140 : Nat := 129657288464672170372079

theorem tailTrace_568140 : CollatzResearch.WordTrace tailWord_568140 prefixEnd_568140 129657288464672170372079 := by
  unfold tailWord_568140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360884080866642716054937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13814512107822190288073249 10360884080866642716054937)
  ·
    refine ⟨7770663060649982037041203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10360884080866642716054937 7770663060649982037041203)
    ·
      refine ⟨11655994590974973055561805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7770663060649982037041203 11655994590974973055561805)
      ·
        refine ⟨4370997971615614895835677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11655994590974973055561805 4370997971615614895835677)
        ·
          refine ⟨1639124239355855585938379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4370997971615614895835677 1639124239355855585938379)
          ·
            refine ⟨2458686359033783378907569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639124239355855585938379 2458686359033783378907569)
            ·
              refine ⟨1844014769275337534180677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458686359033783378907569 1844014769275337534180677)
              ·
                refine ⟨345752769239125787658877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1844014769275337534180677 345752769239125787658877)
                ·
                  refine ⟨129657288464672170372079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345752769239125787658877 129657288464672170372079)
                  ·
                    rfl

theorem cell21_568140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_568140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568140 prefixEnd_568140 := by exact prefixLift 568140
  have htrace : WordTrace (prefixWord ++ tailWord_568140) baseStart_568140 baseEnd_568140 := by
    simpa [prefixWord, tailWord_568140, baseEnd_568140] using wordTrace_append hprefix tailTrace_568140
  have hstable : (prefixWord ++ tailWord_568140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568140).length < 2 ^ (prefixWord ++ tailWord_568140).sum := by decide
  have hdescent : baseEnd_568140 < baseStart_568140 := by decide
  rcases family_descends (prefixWord ++ tailWord_568140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568168 : List Nat := [2, 1, 4, 2, 1, 3, 1, 7]
def baseStart_568168 : Nat := 118140960795 + 568168 * 2 ^ 59
def prefixEnd_568168 : Nat := 4983230072969 + 3 ^ 40 * 568168 * 2
def baseEnd_568168 : Nat := 43221226148716781301785

theorem tailTrace_568168 : CollatzResearch.WordTrace tailWord_568168 prefixEnd_568168 43221226148716781301785 := by
  unfold tailWord_568168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361394702815923107064579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13815192937087897476086105 10361394702815923107064579)
  ·
    refine ⟨15542092054223884660596869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361394702815923107064579 15542092054223884660596869)
    ·
      refine ⟨2914142260166978373861913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15542092054223884660596869 2914142260166978373861913)
      ·
        refine ⟨2185606695125233780396435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2914142260166978373861913 2185606695125233780396435)
        ·
          refine ⟨3278410042687850670594653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185606695125233780396435 3278410042687850670594653)
          ·
            refine ⟨1229403766007944001472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3278410042687850670594653 1229403766007944001472995)
            ·
              refine ⟨1844105649011916002209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229403766007944001472995 1844105649011916002209493)
              ·
                refine ⟨43221226148716781301785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1844105649011916002209493 43221226148716781301785)
                ·
                  rfl

theorem cell21_568168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_568168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568168 prefixEnd_568168 := by exact prefixLift 568168
  have htrace : WordTrace (prefixWord ++ tailWord_568168) baseStart_568168 baseEnd_568168 := by
    simpa [prefixWord, tailWord_568168, baseEnd_568168] using wordTrace_append hprefix tailTrace_568168
  have hstable : (prefixWord ++ tailWord_568168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568168).length < 2 ^ (prefixWord ++ tailWord_568168).sum := by decide
  have hdescent : baseEnd_568168 < baseStart_568168 := by decide
  rcases family_descends (prefixWord ++ tailWord_568168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568174 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_568174 : Nat := 118140960795 + 568174 * 2 ^ 59
def prefixEnd_568174 : Nat := 4983230072969 + 3 ^ 40 * 568174 * 2
def baseEnd_568174 : Nat := 129665047727895666805343

theorem tailTrace_568174 : CollatzResearch.WordTrace tailWord_568174 prefixEnd_568174 129665047727895666805343 := by
  unfold tailWord_568174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590376030451263654855947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13815338829073406159231717 2590376030451263654855947)
  ·
    refine ⟨3885564045676895482283921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590376030451263654855947 3885564045676895482283921)
    ·
      refine ⟨2914173034257671611712941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3885564045676895482283921 2914173034257671611712941)
      ·
        refine ⟨1092814887846626854392353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2914173034257671611712941 1092814887846626854392353)
        ·
          refine ⟨819611165884970140794265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092814887846626854392353 819611165884970140794265)
          ·
            refine ⟨614708374413727605595699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819611165884970140794265 614708374413727605595699)
            ·
              refine ⟨922062561620591408393549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614708374413727605595699 922062561620591408393549)
              ·
                refine ⟨345773460607721778147581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922062561620591408393549 345773460607721778147581)
                ·
                  refine ⟨129665047727895666805343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345773460607721778147581 129665047727895666805343)
                  ·
                    rfl

theorem cell21_568174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_568174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568174 prefixEnd_568174 := by exact prefixLift 568174
  have htrace : WordTrace (prefixWord ++ tailWord_568174) baseStart_568174 baseEnd_568174 := by
    simpa [prefixWord, tailWord_568174, baseEnd_568174] using wordTrace_append hprefix tailTrace_568174
  have hstable : (prefixWord ++ tailWord_568174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568174).length < 2 ^ (prefixWord ++ tailWord_568174).sum := by decide
  have hdescent : baseEnd_568174 < baseStart_568174 := by decide
  rcases family_descends (prefixWord ++ tailWord_568174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568199 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_568199 : Nat := 118140960795 + 568199 * 2 ^ 59
def prefixEnd_568199 : Nat := 4983230072969 + 3 ^ 40 * 568199 * 2
def baseEnd_568199 : Nat := 129670753068501178888625

theorem tailTrace_568199 : CollatzResearch.WordTrace tailWord_568199 prefixEnd_568199 129670753068501178888625 := by
  unfold tailWord_568199
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723920068519538508507651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13815946712346359005671767 20723920068519538508507651)
  ·
    refine ⟨31085880102779307762761477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20723920068519538508507651 31085880102779307762761477)
    ·
      refine ⟨5828602519271120205517777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31085880102779307762761477 5828602519271120205517777)
      ·
        refine ⟨4371451889453340154138333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5828602519271120205517777 4371451889453340154138333)
        ·
          refine ⟨1639294458545002557801875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371451889453340154138333 1639294458545002557801875)
          ·
            refine ⟨2458941687817503836702813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639294458545002557801875 2458941687817503836702813)
            ·
              refine ⟨922103132931563938763555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458941687817503836702813 922103132931563938763555)
              ·
                refine ⟨1383154699397345908145333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922103132931563938763555 1383154699397345908145333)
                ·
                  refine ⟨129670753068501178888625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1383154699397345908145333 129670753068501178888625)
                  ·
                    rfl

theorem cell21_568199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_568199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568199 prefixEnd_568199 := by exact prefixLift 568199
  have htrace : WordTrace (prefixWord ++ tailWord_568199) baseStart_568199 baseEnd_568199 := by
    simpa [prefixWord, tailWord_568199, baseEnd_568199] using wordTrace_append hprefix tailTrace_568199
  have hstable : (prefixWord ++ tailWord_568199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568199).length < 2 ^ (prefixWord ++ tailWord_568199).sum := by decide
  have hdescent : baseEnd_568199 < baseStart_568199 := by decide
  rcases family_descends (prefixWord ++ tailWord_568199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568227 : List Nat := [1, 1, 1, 4, 1, 2, 4, 7]
def baseStart_568227 : Nat := 118140960795 + 568227 * 2 ^ 59
def prefixEnd_568227 : Nat := 4983230072969 + 3 ^ 40 * 568227 * 2
def baseEnd_568227 : Nat := 43225714349993117473967

theorem tailTrace_568227 : CollatzResearch.WordTrace tailWord_568227 prefixEnd_568227 43225714349993117473967 := by
  unfold tailWord_568227
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724941312418099290526935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13816627541612066193684623 20724941312418099290526935)
  ·
    refine ⟨31087411968627148935790403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20724941312418099290526935 31087411968627148935790403)
    ·
      refine ⟨46631117952940723403685605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31087411968627148935790403 46631117952940723403685605)
      ·
        refine ⟨8743334616176385638191051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46631117952940723403685605 8743334616176385638191051)
        ·
          refine ⟨13115001924264578457286577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743334616176385638191051 13115001924264578457286577)
          ·
            refine ⟨9836251443198433842964933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13115001924264578457286577 9836251443198433842964933)
            ·
              refine ⟨1844297145599706345555925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9836251443198433842964933 1844297145599706345555925)
              ·
                refine ⟨43225714349993117473967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1844297145599706345555925 43225714349993117473967)
                ·
                  rfl

theorem cell21_568227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_568227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568227 prefixEnd_568227 := by exact prefixLift 568227
  have htrace : WordTrace (prefixWord ++ tailWord_568227) baseStart_568227 baseEnd_568227 := by
    simpa [prefixWord, tailWord_568227, baseEnd_568227] using wordTrace_append hprefix tailTrace_568227
  have hstable : (prefixWord ++ tailWord_568227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568227).length < 2 ^ (prefixWord ++ tailWord_568227).sum := by decide
  have hdescent : baseEnd_568227 < baseStart_568227 := by decide
  rcases family_descends (prefixWord ++ tailWord_568227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568272 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_568272 : Nat := 118140960795 + 568272 * 2 ^ 59
def prefixEnd_568272 : Nat := 4983230072969 + 3 ^ 40 * 568272 * 2
def baseEnd_568272 : Nat := 129687412663069274171809

theorem tailTrace_568272 : CollatzResearch.WordTrace tailWord_568272 prefixEnd_568272 129687412663069274171809 := by
  unfold tailWord_568272
  simp only [CollatzResearch.WordTrace]
  refine ⟨10363291298627535987957535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13817721731503381317276713 10363291298627535987957535)
  ·
    refine ⟨15544936947941303981936303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10363291298627535987957535 15544936947941303981936303)
    ·
      refine ⟨23317405421911955972904455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15544936947941303981936303 23317405421911955972904455)
      ·
        refine ⟨34976108132867933959356683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23317405421911955972904455 34976108132867933959356683)
        ·
          refine ⟨52464162199301900939035025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34976108132867933959356683 52464162199301900939035025)
          ·
            refine ⟨39348121649476425704276269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52464162199301900939035025 39348121649476425704276269)
            ·
              refine ⟨14755545618553659639103601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39348121649476425704276269 14755545618553659639103601)
              ·
                refine ⟨11066659213915244729327701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14755545618553659639103601 11066659213915244729327701)
                ·
                  refine ⟨129687412663069274171809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11066659213915244729327701 129687412663069274171809)
                  ·
                    rfl

theorem cell21_568272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_568272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568272 prefixEnd_568272 := by exact prefixLift 568272
  have htrace : WordTrace (prefixWord ++ tailWord_568272) baseStart_568272 baseEnd_568272 := by
    simpa [prefixWord, tailWord_568272, baseEnd_568272] using wordTrace_append hprefix tailTrace_568272
  have hstable : (prefixWord ++ tailWord_568272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568272).length < 2 ^ (prefixWord ++ tailWord_568272).sum := by decide
  have hdescent : baseEnd_568272 < baseStart_568272 := by decide
  rcases family_descends (prefixWord ++ tailWord_568272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568278 : List Nat := [5, 2, 1, 1, 2, 2, 3, 5]
def baseStart_568278 : Nat := 118140960795 + 568278 * 2 ^ 59
def prefixEnd_568278 : Nat := 4983230072969 + 3 ^ 40 * 568278 * 2
def baseEnd_568278 : Nat := 43229593981604865690599

theorem tailTrace_568278 : CollatzResearch.WordTrace tailWord_568278 prefixEnd_568278 43229593981604865690599 := by
  unfold tailWord_568278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295425089702083437539593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13817867623488890000422325 1295425089702083437539593)
  ·
    refine ⟨971568817276562578154695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1295425089702083437539593 971568817276562578154695)
    ·
      refine ⟨1457353225914843867232043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971568817276562578154695 1457353225914843867232043)
      ·
        refine ⟨2186029838872265800848065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457353225914843867232043 2186029838872265800848065)
        ·
          refine ⟨1639522379154199350636049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2186029838872265800848065 1639522379154199350636049)
          ·
            refine ⟨1229641784365649512977037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639522379154199350636049 1229641784365649512977037)
            ·
              refine ⟨461115669137118567366389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1229641784365649512977037 461115669137118567366389)
              ·
                refine ⟨43229593981604865690599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461115669137118567366389 43229593981604865690599)
                ·
                  rfl

theorem cell21_568278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_568278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568278 prefixEnd_568278 := by exact prefixLift 568278
  have htrace : WordTrace (prefixWord ++ tailWord_568278) baseStart_568278 baseEnd_568278 := by
    simpa [prefixWord, tailWord_568278, baseEnd_568278] using wordTrace_append hprefix tailTrace_568278
  have hstable : (prefixWord ++ tailWord_568278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568278).length < 2 ^ (prefixWord ++ tailWord_568278).sum := by decide
  have hdescent : baseEnd_568278 < baseStart_568278 := by decide
  rcases family_descends (prefixWord ++ tailWord_568278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568303 : List Nat := [1, 1, 2, 1, 4, 4, 8]
def baseStart_568303 : Nat := 118140960795 + 568303 * 2 ^ 59
def prefixEnd_568303 : Nat := 4983230072969 + 3 ^ 40 * 568303 * 2
def baseEnd_568303 : Nat := 14410498587268901017231

theorem tailTrace_568303 : CollatzResearch.WordTrace tailWord_568303 prefixEnd_568303 14410498587268901017231 := by
  unfold tailWord_568303
  simp only [CollatzResearch.WordTrace]
  refine ⟨20727713260142764270293563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13818475506761842846862375 20727713260142764270293563)
  ·
    refine ⟨31091569890214146405440345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20727713260142764270293563 31091569890214146405440345)
    ·
      refine ⟨23318677417660609804080259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31091569890214146405440345 23318677417660609804080259)
      ·
        refine ⟨34978016126490914706120389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23318677417660609804080259 34978016126490914706120389)
        ·
          refine ⟨6558378023717046507397573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34978016126490914706120389 6558378023717046507397573)
          ·
            refine ⟨1229695879446946220137045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6558378023717046507397573 1229695879446946220137045)
            ·
              refine ⟨14410498587268901017231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1229695879446946220137045 14410498587268901017231)
              ·
                rfl

theorem cell21_568303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_568303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568303 prefixEnd_568303 := by exact prefixLift 568303
  have htrace : WordTrace (prefixWord ++ tailWord_568303) baseStart_568303 baseEnd_568303 := by
    simpa [prefixWord, tailWord_568303, baseEnd_568303] using wordTrace_append hprefix tailTrace_568303
  have hstable : (prefixWord ++ tailWord_568303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568303).length < 2 ^ (prefixWord ++ tailWord_568303).sum := by decide
  have hdescent : baseEnd_568303 < baseStart_568303 := by decide
  rcases family_descends (prefixWord ++ tailWord_568303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568309 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_568309 : Nat := 118140960795 + 568309 * 2 ^ 59
def prefixEnd_568309 : Nat := 4983230072969 + 3 ^ 40 * 568309 * 2
def baseEnd_568309 : Nat := 129695856567165432055067

theorem tailTrace_568309 : CollatzResearch.WordTrace tailWord_568309 prefixEnd_568309 129695856567165432055067 := by
  unfold tailWord_568309
  simp only [CollatzResearch.WordTrace]
  refine ⟨20727932098121027295011981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13818621398747351530007987 20727932098121027295011981)
  ·
    refine ⟨7772974536795385235629493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20727932098121027295011981 7772974536795385235629493)
    ·
      refine ⟨728716362824567365840265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7772974536795385235629493 728716362824567365840265)
      ·
        refine ⟨546537272118425524380199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728716362824567365840265 546537272118425524380199)
        ·
          refine ⟨819805908177638286570299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546537272118425524380199 819805908177638286570299)
          ·
            refine ⟨1229708862266457429855449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819805908177638286570299 1229708862266457429855449)
            ·
              refine ⟨922281646699843072391587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229708862266457429855449 922281646699843072391587)
              ·
                refine ⟨1383422470049764608587381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922281646699843072391587 1383422470049764608587381)
                ·
                  refine ⟨129695856567165432055067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1383422470049764608587381 129695856567165432055067)
                  ·
                    rfl

theorem cell21_568309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_568309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568309 prefixEnd_568309 := by exact prefixLift 568309
  have htrace : WordTrace (prefixWord ++ tailWord_568309) baseStart_568309 baseEnd_568309 := by
    simpa [prefixWord, tailWord_568309, baseEnd_568309] using wordTrace_append hprefix tailTrace_568309
  have hstable : (prefixWord ++ tailWord_568309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568309).length < 2 ^ (prefixWord ++ tailWord_568309).sum := by decide
  have hdescent : baseEnd_568309 < baseStart_568309 := by decide
  rcases family_descends (prefixWord ++ tailWord_568309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568368 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 3]
def baseStart_568368 : Nat := 118140960795 + 568368 * 2 ^ 59
def prefixEnd_568368 : Nat := 4983230072969 + 3 ^ 40 * 568368 * 2
def baseEnd_568368 : Nat := 129709321170994440571613

theorem tailTrace_568368 : CollatzResearch.WordTrace tailWord_568368 prefixEnd_568368 129709321170994440571613 := by
  unfold tailWord_568368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10365042002453640185704879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13820056003271520247606505 10365042002453640185704879)
  ·
    refine ⟨15547563003680460278557319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10365042002453640185704879 15547563003680460278557319)
    ·
      refine ⟨23321344505520690417835979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15547563003680460278557319 23321344505520690417835979)
      ·
        refine ⟨34982016758281035626753969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23321344505520690417835979 34982016758281035626753969)
        ·
          refine ⟨26236512568710776720065477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34982016758281035626753969 26236512568710776720065477)
          ·
            refine ⟨4919346106633270635012277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26236512568710776720065477 4919346106633270635012277)
            ·
              refine ⟨461188697496869122032401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4919346106633270635012277 461188697496869122032401)
              ·
                refine ⟨345891523122651841524301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461188697496869122032401 345891523122651841524301)
                ·
                  refine ⟨129709321170994440571613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345891523122651841524301 129709321170994440571613)
                  ·
                    rfl

theorem cell21_568368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_568368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568368 prefixEnd_568368 := by exact prefixLift 568368
  have htrace : WordTrace (prefixWord ++ tailWord_568368) baseStart_568368 baseEnd_568368 := by
    simpa [prefixWord, tailWord_568368, baseEnd_568368] using wordTrace_append hprefix tailTrace_568368
  have hstable : (prefixWord ++ tailWord_568368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568368).length < 2 ^ (prefixWord ++ tailWord_568368).sum := by decide
  have hdescent : baseEnd_568368 < baseStart_568368 := by decide
  rcases family_descends (prefixWord ++ tailWord_568368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568413 : List Nat := [1, 4, 4, 1, 3, 8]
def baseStart_568413 : Nat := 118140960795 + 568413 * 2 ^ 59
def prefixEnd_568413 : Nat := 4983230072969 + 3 ^ 40 * 568413 * 2
def baseEnd_568413 : Nat := 4804429288299420826723

theorem tailTrace_568413 : CollatzResearch.WordTrace tailWord_568413 prefixEnd_568413 4804429288299420826723 := by
  unfold tailWord_568413
  simp only [CollatzResearch.WordTrace]
  refine ⟨20731725289744253056797893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13821150193162835371198595 20731725289744253056797893)
  ·
    refine ⟨3887198491827047448149605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20731725289744253056797893 3887198491827047448149605)
    ·
      refine ⟨728849717217571396528051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3887198491827047448149605 728849717217571396528051)
      ·
        refine ⟨1093274575826357094792077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728849717217571396528051 1093274575826357094792077)
        ·
          refine ⟨409977965934883910547029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1093274575826357094792077 409977965934883910547029)
          ·
            refine ⟨4804429288299420826723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 409977965934883910547029 4804429288299420826723)
            ·
              rfl

theorem cell21_568413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 8].length) (baseStart_568413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568413 prefixEnd_568413 := by exact prefixLift 568413
  have htrace : WordTrace (prefixWord ++ tailWord_568413) baseStart_568413 baseEnd_568413 := by
    simpa [prefixWord, tailWord_568413, baseEnd_568413] using wordTrace_append hprefix tailTrace_568413
  have hstable : (prefixWord ++ tailWord_568413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568413).length < 2 ^ (prefixWord ++ tailWord_568413).sum := by decide
  have hdescent : baseEnd_568413 < baseStart_568413 := by decide
  rcases family_descends (prefixWord ++ tailWord_568413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568593 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_568593 : Nat := 118140960795 + 568593 * 2 ^ 59
def prefixEnd_568593 : Nat := 4983230072969 + 3 ^ 40 * 568593 * 2
def baseEnd_568593 : Nat := 129760669236444049321153

theorem tailTrace_568593 : CollatzResearch.WordTrace tailWord_568593 prefixEnd_568593 129760669236444049321153 := by
  unfold tailWord_568593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20738290429092143798350433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13825526952728095865566955 20738290429092143798350433)
  ·
    refine ⟨15553717821819107848762825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20738290429092143798350433 15553717821819107848762825)
    ·
      refine ⟨11665288366364330886572119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15553717821819107848762825 11665288366364330886572119)
      ·
        refine ⟨17497932549546496329858179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11665288366364330886572119 17497932549546496329858179)
        ·
          refine ⟨26246898824319744494787269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17497932549546496329858179 26246898824319744494787269)
          ·
            refine ⟨4921293529559952092772613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26246898824319744494787269 4921293529559952092772613)
            ·
              refine ⟨922742536792491017394865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4921293529559952092772613 922742536792491017394865)
              ·
                refine ⟨692056902594368263046149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922742536792491017394865 692056902594368263046149)
                ·
                  refine ⟨129760669236444049321153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692056902594368263046149 129760669236444049321153)
                  ·
                    rfl

theorem cell21_568593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_568593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568593 prefixEnd_568593 := by exact prefixLift 568593
  have htrace : WordTrace (prefixWord ++ tailWord_568593) baseStart_568593 baseEnd_568593 := by
    simpa [prefixWord, tailWord_568593, baseEnd_568593] using wordTrace_append hprefix tailTrace_568593
  have hstable : (prefixWord ++ tailWord_568593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568593).length < 2 ^ (prefixWord ++ tailWord_568593).sum := by decide
  have hdescent : baseEnd_568593 < baseStart_568593 := by decide
  rcases family_descends (prefixWord ++ tailWord_568593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568630 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_568630 : Nat := 118140960795 + 568630 * 2 ^ 59
def prefixEnd_568630 : Nat := 4983230072969 + 3 ^ 40 * 568630 * 2
def baseEnd_568630 : Nat := 129769113140540207204411

theorem tailTrace_568630 : CollatzResearch.WordTrace tailWord_568630 prefixEnd_568630 129769113140540207204411 := by
  unfold tailWord_568630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296227495622381194840459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13826426619972066078298229 1296227495622381194840459)
  ·
    refine ⟨1944341243433571792260689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296227495622381194840459 1944341243433571792260689)
    ·
      refine ⟨1458255932575178844195517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1944341243433571792260689 1458255932575178844195517)
      ·
        refine ⟨546845974715692066573319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1458255932575178844195517 546845974715692066573319)
        ·
          refine ⟨820268962073538099859979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546845974715692066573319 820268962073538099859979)
          ·
            refine ⟨1230403443110307149789969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820268962073538099859979 1230403443110307149789969)
            ·
              refine ⟨922802582332730362342477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230403443110307149789969 922802582332730362342477)
              ·
                refine ⟨346050968374773885878429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922802582332730362342477 346050968374773885878429)
                ·
                  refine ⟨129769113140540207204411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346050968374773885878429 129769113140540207204411)
                  ·
                    rfl

theorem cell21_568630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_568630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568630 prefixEnd_568630 := by exact prefixLift 568630
  have htrace : WordTrace (prefixWord ++ tailWord_568630) baseStart_568630 baseEnd_568630 := by
    simpa [prefixWord, tailWord_568630, baseEnd_568630] using wordTrace_append hprefix tailTrace_568630
  have hstable : (prefixWord ++ tailWord_568630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568630).length < 2 ^ (prefixWord ++ tailWord_568630).sum := by decide
  have hdescent : baseEnd_568630 < baseStart_568630 := by decide
  rcases family_descends (prefixWord ++ tailWord_568630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568638 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_568638 : Nat := 118140960795 + 568638 * 2 ^ 59
def prefixEnd_568638 : Nat := 4983230072969 + 3 ^ 40 * 568638 * 2
def baseEnd_568638 : Nat := 129770938849533971071061

theorem tailTrace_568638 : CollatzResearch.WordTrace tailWord_568638 prefixEnd_568638 129770938849533971071061 := by
  unfold tailWord_568638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592491464241139560467321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13826621142619410989159045 2592491464241139560467321)
  ·
    refine ⟨1944368598180854670350491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2592491464241139560467321 1944368598180854670350491)
    ·
      refine ⟨2916552897271282005525737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944368598180854670350491 2916552897271282005525737)
      ·
        refine ⟨2187414672953461504144303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2916552897271282005525737 2187414672953461504144303)
        ·
          refine ⟨3281122009430192256216455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187414672953461504144303 3281122009430192256216455)
          ·
            refine ⟨4921683014145288384324683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281122009430192256216455 4921683014145288384324683)
            ·
              refine ⟨7382524521217932576487025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921683014145288384324683 7382524521217932576487025)
              ·
                refine ⟨5536893390913449432365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7382524521217932576487025 5536893390913449432365269)
                ·
                  refine ⟨129770938849533971071061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5536893390913449432365269 129770938849533971071061)
                  ·
                    rfl

theorem cell21_568638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_568638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568638 prefixEnd_568638 := by exact prefixLift 568638
  have htrace : WordTrace (prefixWord ++ tailWord_568638) baseStart_568638 baseEnd_568638 := by
    simpa [prefixWord, tailWord_568638, baseEnd_568638] using wordTrace_append hprefix tailTrace_568638
  have hstable : (prefixWord ++ tailWord_568638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568638).length < 2 ^ (prefixWord ++ tailWord_568638).sum := by decide
  have hdescent : baseEnd_568638 < baseStart_568638 := by decide
  rcases family_descends (prefixWord ++ tailWord_568638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568697 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_568697 : Nat := 118140960795 + 568697 * 2 ^ 59
def prefixEnd_568697 : Nat := 4983230072969 + 3 ^ 40 * 568697 * 2
def baseEnd_568697 : Nat := 129784403453362979587607

theorem tailTrace_568697 : CollatzResearch.WordTrace tailWord_568697 prefixEnd_568697 129784403453362979587607 := by
  unfold tailWord_568697
  simp only [CollatzResearch.WordTrace]
  refine ⟨20742083620715369560136345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828055747143579706757563 20742083620715369560136345)
  ·
    refine ⟨15556562715536527170102259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20742083620715369560136345 15556562715536527170102259)
    ·
      refine ⟨23334844073304790755153389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15556562715536527170102259 23334844073304790755153389)
      ·
        refine ⟨8750566527489296533182521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23334844073304790755153389 8750566527489296533182521)
        ·
          refine ⟨6562924895616972399886891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8750566527489296533182521 6562924895616972399886891)
          ·
            refine ⟨9844387343425458599830337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6562924895616972399886891 9844387343425458599830337)
            ·
              refine ⟨7383290507569093949872753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9844387343425458599830337 7383290507569093949872753)
              ·
                refine ⟨5537467880676820462404565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7383290507569093949872753 5537467880676820462404565)
                ·
                  refine ⟨129784403453362979587607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5537467880676820462404565 129784403453362979587607)
                  ·
                    rfl

theorem cell21_568697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_568697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568697 prefixEnd_568697 := by exact prefixLift 568697
  have htrace : WordTrace (prefixWord ++ tailWord_568697) baseStart_568697 baseEnd_568697 := by
    simpa [prefixWord, tailWord_568697, baseEnd_568697] using wordTrace_append hprefix tailTrace_568697
  have hstable : (prefixWord ++ tailWord_568697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568697).length < 2 ^ (prefixWord ++ tailWord_568697).sum := by decide
  have hdescent : baseEnd_568697 < baseStart_568697 := by decide
  rcases family_descends (prefixWord ++ tailWord_568697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568706 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_568706 : Nat := 118140960795 + 568706 * 2 ^ 59
def prefixEnd_568706 : Nat := 4983230072969 + 3 ^ 40 * 568706 * 2
def baseEnd_568706 : Nat := 129786457375980963937589

theorem tailTrace_568706 : CollatzResearch.WordTrace tailWord_568706 prefixEnd_568706 129786457375980963937589 := by
  unfold tailWord_568706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185602969420691024303493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13828274585121842731475981 5185602969420691024303493)
  ·
    refine ⟨972300556766379567056905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5185602969420691024303493 972300556766379567056905)
    ·
      refine ⟨729225417574784675292679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 972300556766379567056905 729225417574784675292679)
      ·
        refine ⟨1093838126362177012939019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729225417574784675292679 1093838126362177012939019)
        ·
          refine ⟨1640757189543265519408529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093838126362177012939019 1640757189543265519408529)
          ·
            refine ⟨1230567892157449139556397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640757189543265519408529 1230567892157449139556397)
            ·
              refine ⟨461462959559043427333649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230567892157449139556397 461462959559043427333649)
              ·
                refine ⟨346097219669282570500237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461462959559043427333649 346097219669282570500237)
                ·
                  refine ⟨129786457375980963937589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346097219669282570500237 129786457375980963937589)
                  ·
                    rfl

theorem cell21_568706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_568706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568706 prefixEnd_568706 := by exact prefixLift 568706
  have htrace : WordTrace (prefixWord ++ tailWord_568706) baseStart_568706 baseEnd_568706 := by
    simpa [prefixWord, tailWord_568706, baseEnd_568706] using wordTrace_append hprefix tailTrace_568706
  have hstable : (prefixWord ++ tailWord_568706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568706).length < 2 ^ (prefixWord ++ tailWord_568706).sum := by decide
  have hdescent : baseEnd_568706 < baseStart_568706 := by decide
  rcases family_descends (prefixWord ++ tailWord_568706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568807 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 3]
def baseStart_568807 : Nat := 118140960795 + 568807 * 2 ^ 59
def prefixEnd_568807 : Nat := 4983230072969 + 3 ^ 40 * 568807 * 2
def baseEnd_568807 : Nat := 129809506952027232754049

theorem tailTrace_568807 : CollatzResearch.WordTrace tailWord_568807 prefixEnd_568807 129809506952027232754049 := by
  unfold tailWord_568807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746095650316858346640675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13830730433544572231093783 20746095650316858346640675)
  ·
    refine ⟨31119143475475287519961013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20746095650316858346640675 31119143475475287519961013)
    ·
      refine ⟨2917419700825808204996345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31119143475475287519961013 2917419700825808204996345)
      ·
        refine ⟨2188064775619356153747259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2917419700825808204996345 2188064775619356153747259)
        ·
          refine ⟨3282097163429034230620889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188064775619356153747259 3282097163429034230620889)
          ·
            refine ⟨2461572872571775672965667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3282097163429034230620889 2461572872571775672965667)
            ·
              refine ⟨3692359308857663509448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461572872571775672965667 3692359308857663509448501)
              ·
                refine ⟨346158685205405954010797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3692359308857663509448501 346158685205405954010797)
                ·
                  refine ⟨129809506952027232754049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346158685205405954010797 129809506952027232754049)
                  ·
                    rfl

theorem cell21_568807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].length) (baseStart_568807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568807 prefixEnd_568807 := by exact prefixLift 568807
  have htrace : WordTrace (prefixWord ++ tailWord_568807) baseStart_568807 baseEnd_568807 := by
    simpa [prefixWord, tailWord_568807, baseEnd_568807] using wordTrace_append hprefix tailTrace_568807
  have hstable : (prefixWord ++ tailWord_568807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568807).length < 2 ^ (prefixWord ++ tailWord_568807).sum := by decide
  have hdescent : baseEnd_568807 < baseStart_568807 := by decide
  rcases family_descends (prefixWord ++ tailWord_568807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568849 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_568849 : Nat := 118140960795 + 568849 * 2 ^ 59
def prefixEnd_568849 : Nat := 4983230072969 + 3 ^ 40 * 568849 * 2
def baseEnd_568849 : Nat := 129819091924244493053963

theorem tailTrace_568849 : CollatzResearch.WordTrace tailWord_568849 prefixEnd_568849 129819091924244493053963 := by
  unfold tailWord_568849
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747627516164699519669601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831751677443133013113067 20747627516164699519669601)
  ·
    refine ⟨15560720637123524639752201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20747627516164699519669601 15560720637123524639752201)
    ·
      refine ⟨11670540477842643479814151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15560720637123524639752201 11670540477842643479814151)
      ·
        refine ⟨17505810716763965219721227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11670540477842643479814151 17505810716763965219721227)
        ·
          refine ⟨26258716075145947829581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17505810716763965219721227 26258716075145947829581841)
          ·
            refine ⟨19694037056359460872186381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26258716075145947829581841 19694037056359460872186381)
            ·
              refine ⟨7385263896134797827069893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19694037056359460872186381 7385263896134797827069893)
              ·
                refine ⟨1384736980525274592575605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7385263896134797827069893 1384736980525274592575605)
                ·
                  refine ⟨129819091924244493053963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1384736980525274592575605 129819091924244493053963)
                  ·
                    rfl

theorem cell21_568849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_568849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568849 prefixEnd_568849 := by exact prefixLift 568849
  have htrace : WordTrace (prefixWord ++ tailWord_568849) baseStart_568849 baseEnd_568849 := by
    simpa [prefixWord, tailWord_568849, baseEnd_568849] using wordTrace_append hprefix tailTrace_568849
  have hstable : (prefixWord ++ tailWord_568849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568849).length < 2 ^ (prefixWord ++ tailWord_568849).sum := by decide
  have hdescent : baseEnd_568849 < baseStart_568849 := by decide
  rcases family_descends (prefixWord ++ tailWord_568849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568880 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_568880 : Nat := 118140960795 + 568880 * 2 ^ 59
def prefixEnd_568880 : Nat := 4983230072969 + 3 ^ 40 * 568880 * 2
def baseEnd_568880 : Nat := 129826166546595328037233

theorem tailTrace_568880 : CollatzResearch.WordTrace tailWord_568880 prefixEnd_568880 129826166546595328037233 := by
  unfold tailWord_568880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374379089526195907024047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13832505452701594542698729 10374379089526195907024047)
  ·
    refine ⟨15561568634289293860536071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10374379089526195907024047 15561568634289293860536071)
    ·
      refine ⟨23342352951433940790804107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15561568634289293860536071 23342352951433940790804107)
      ·
        refine ⟨35013529427150911186206161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23342352951433940790804107 35013529427150911186206161)
        ·
          refine ⟨26260147070363183389654621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35013529427150911186206161 26260147070363183389654621)
          ·
            refine ⟨9847555151386193771120483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26260147070363183389654621 9847555151386193771120483)
            ·
              refine ⟨14771332727079290656680725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847555151386193771120483 14771332727079290656680725)
              ·
                refine ⟨692406221581841749531909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14771332727079290656680725 692406221581841749531909)
                ·
                  refine ⟨129826166546595328037233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692406221581841749531909 129826166546595328037233)
                  ·
                    rfl

theorem cell21_568880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_568880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568880 prefixEnd_568880 := by exact prefixLift 568880
  have htrace : WordTrace (prefixWord ++ tailWord_568880) baseStart_568880 baseEnd_568880 := by
    simpa [prefixWord, tailWord_568880, baseEnd_568880] using wordTrace_append hprefix tailTrace_568880
  have hstable : (prefixWord ++ tailWord_568880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568880).length < 2 ^ (prefixWord ++ tailWord_568880).sum := by decide
  have hdescent : baseEnd_568880 < baseStart_568880 := by decide
  rcases family_descends (prefixWord ++ tailWord_568880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568897 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_568897 : Nat := 118140960795 + 568897 * 2 ^ 59
def prefixEnd_568897 : Nat := 4983230072969 + 3 ^ 40 * 568897 * 2
def baseEnd_568897 : Nat := 129830046178207076253865

theorem tailTrace_568897 : CollatzResearch.WordTrace tailWord_568897 prefixEnd_568897 129830046178207076253865 := by
  unfold tailWord_568897
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749378219990803717416945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13832918813327202478277963 20749378219990803717416945)
  ·
    refine ⟨15562033664993102788062709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20749378219990803717416945 15562033664993102788062709)
    ·
      refine ⟨1458940656093103386380879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15562033664993102788062709 1458940656093103386380879)
      ·
        refine ⟨2188410984139655079571319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458940656093103386380879 2188410984139655079571319)
        ·
          refine ⟨3282616476209482619356979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188410984139655079571319 3282616476209482619356979)
          ·
            refine ⟨4923924714314223929035469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282616476209482619356979 4923924714314223929035469)
            ·
              refine ⟨1846471767867833973388301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4923924714314223929035469 1846471767867833973388301)
              ·
                refine ⟨692426912950437740020613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846471767867833973388301 692426912950437740020613)
                ·
                  refine ⟨129830046178207076253865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692426912950437740020613 129830046178207076253865)
                  ·
                    rfl

theorem cell21_568897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_568897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568897 prefixEnd_568897 := by exact prefixLift 568897
  have htrace : WordTrace (prefixWord ++ tailWord_568897) baseStart_568897 baseEnd_568897 := by
    simpa [prefixWord, tailWord_568897, baseEnd_568897] using wordTrace_append hprefix tailTrace_568897
  have hstable : (prefixWord ++ tailWord_568897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568897).length < 2 ^ (prefixWord ++ tailWord_568897).sum := by decide
  have hdescent : baseEnd_568897 < baseStart_568897 := by decide
  rcases family_descends (prefixWord ++ tailWord_568897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568939 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_568939 : Nat := 118140960795 + 568939 * 2 ^ 59
def prefixEnd_568939 : Nat := 4983230072969 + 3 ^ 40 * 568939 * 2
def baseEnd_568939 : Nat := 129839631150424336553779

theorem tailTrace_568939 : CollatzResearch.WordTrace tailWord_568939 prefixEnd_568939 129839631150424336553779 := by
  unfold tailWord_568939
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750910085838644890445871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13833940057225763260297247 20750910085838644890445871)
  ·
    refine ⟨31126365128757967335668807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20750910085838644890445871 31126365128757967335668807)
    ·
      refine ⟨46689547693136951003503211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31126365128757967335668807 46689547693136951003503211)
      ·
        refine ⟨70034321539705426505254817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46689547693136951003503211 70034321539705426505254817)
        ·
          refine ⟨52525741154779069878941113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70034321539705426505254817 52525741154779069878941113)
          ·
            refine ⟨39394305866084302409205835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52525741154779069878941113 39394305866084302409205835)
            ·
              refine ⟨59091458799126453613808753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39394305866084302409205835 59091458799126453613808753)
              ·
                refine ⟨44318594099344840210356565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59091458799126453613808753 44318594099344840210356565)
                ·
                  refine ⟨129839631150424336553779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 44318594099344840210356565 129839631150424336553779)
                  ·
                    rfl

theorem cell21_568939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_568939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568939 prefixEnd_568939 := by exact prefixLift 568939
  have htrace : WordTrace (prefixWord ++ tailWord_568939) baseStart_568939 baseEnd_568939 := by
    simpa [prefixWord, tailWord_568939, baseEnd_568939] using wordTrace_append hprefix tailTrace_568939
  have hstable : (prefixWord ++ tailWord_568939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568939).length < 2 ^ (prefixWord ++ tailWord_568939).sum := by decide
  have hdescent : baseEnd_568939 < baseStart_568939 := by decide
  rcases family_descends (prefixWord ++ tailWord_568939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568990 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_568990 : Nat := 118140960795 + 568990 * 2 ^ 59
def prefixEnd_568990 : Nat := 4983230072969 + 3 ^ 40 * 568990 * 2
def baseEnd_568990 : Nat := 129851270045259581203675

theorem tailTrace_568990 : CollatzResearch.WordTrace tailWord_568990 prefixEnd_568990 129851270045259581203675 := by
  unfold tailWord_568990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594096276081735075069053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13835180139102587067034949 2594096276081735075069053)
  ·
    refine ⟨972786103530650653150895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2594096276081735075069053 972786103530650653150895)
    ·
      refine ⟨1459179155295975979726343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972786103530650653150895 1459179155295975979726343)
      ·
        refine ⟨2188768732943963969589515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459179155295975979726343 2188768732943963969589515)
        ·
          refine ⟨3283153099415945954384273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188768732943963969589515 3283153099415945954384273)
          ·
            refine ⟨2462364824561959465788205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283153099415945954384273 2462364824561959465788205)
            ·
              refine ⟨923386809210734799670577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2462364824561959465788205 923386809210734799670577)
              ·
                refine ⟨692540106908051099752933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923386809210734799670577 692540106908051099752933)
                ·
                  refine ⟨129851270045259581203675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692540106908051099752933 129851270045259581203675)
                  ·
                    rfl

theorem cell21_568990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_568990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_568990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_568990 prefixEnd_568990 := by exact prefixLift 568990
  have htrace : WordTrace (prefixWord ++ tailWord_568990) baseStart_568990 baseEnd_568990 := by
    simpa [prefixWord, tailWord_568990, baseEnd_568990] using wordTrace_append hprefix tailTrace_568990
  have hstable : (prefixWord ++ tailWord_568990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568990).length < 2 ^ (prefixWord ++ tailWord_568990).sum := by decide
  have hdescent : baseEnd_568990 < baseStart_568990 := by decide
  rcases family_descends (prefixWord ++ tailWord_568990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569052 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 5]
def baseStart_569052 : Nat := 118140960795 + 569052 * 2 ^ 59
def prefixEnd_569052 : Nat := 4983230072969 + 3 ^ 40 * 569052 * 2
def baseEnd_569052 : Nat := 129865419289961251170215

theorem tailTrace_569052 : CollatzResearch.WordTrace tailWord_569052 prefixEnd_569052 129865419289961251170215 := by
  unfold tailWord_569052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377515767214632594654705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13836687689619510126206273 10377515767214632594654705)
  ·
    refine ⟨7783136825410974445991029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10377515767214632594654705 7783136825410974445991029)
    ·
      refine ⟨729669077382278854311659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7783136825410974445991029 729669077382278854311659)
      ·
        refine ⟨1094503616073418281467489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729669077382278854311659 1094503616073418281467489)
        ·
          refine ⟨820877712055063711100617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094503616073418281467489 820877712055063711100617)
          ·
            refine ⟨615658284041297783325463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820877712055063711100617 615658284041297783325463)
            ·
              refine ⟨923487426061946674988195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615658284041297783325463 923487426061946674988195)
              ·
                refine ⟨1385231139092920012482293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923487426061946674988195 1385231139092920012482293)
                ·
                  refine ⟨129865419289961251170215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385231139092920012482293 129865419289961251170215)
                  ·
                    rfl

theorem cell21_569052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_569052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569052 prefixEnd_569052 := by exact prefixLift 569052
  have htrace : WordTrace (prefixWord ++ tailWord_569052) baseStart_569052 baseEnd_569052 := by
    simpa [prefixWord, tailWord_569052, baseEnd_569052] using wordTrace_append hprefix tailTrace_569052
  have hstable : (prefixWord ++ tailWord_569052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569052).length < 2 ^ (prefixWord ++ tailWord_569052).sum := by decide
  have hdescent : baseEnd_569052 < baseStart_569052 := by decide
  rcases family_descends (prefixWord ++ tailWord_569052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569091 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_569091 : Nat := 118140960795 + 569091 * 2 ^ 59
def prefixEnd_569091 : Nat := 4983230072969 + 3 ^ 40 * 569091 * 2
def baseEnd_569091 : Nat := 129874319621305850020135

theorem tailTrace_569091 : CollatzResearch.WordTrace tailWord_569091 prefixEnd_569091 129874319621305850020135 := by
  unfold tailWord_569091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20756453981287974849979127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13837635987525316566652751 20756453981287974849979127)
  ·
    refine ⟨31134680971931962274968691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20756453981287974849979127 31134680971931962274968691)
    ·
      refine ⟨46702021457897943412453037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31134680971931962274968691 46702021457897943412453037)
      ·
        refine ⟨17513258046711728779669889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46702021457897943412453037 17513258046711728779669889)
        ·
          refine ⟨13134943535033796584752417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17513258046711728779669889 13134943535033796584752417)
          ·
            refine ⟨9851207651275347438564313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13134943535033796584752417 9851207651275347438564313)
            ·
              refine ⟨7388405738456510578923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9851207651275347438564313 7388405738456510578923235)
              ·
                refine ⟨11082608607684765868384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7388405738456510578923235 11082608607684765868384853)
                ·
                  refine ⟨129874319621305850020135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11082608607684765868384853 129874319621305850020135)
                  ·
                    rfl

theorem cell21_569091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_569091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569091 prefixEnd_569091 := by exact prefixLift 569091
  have htrace : WordTrace (prefixWord ++ tailWord_569091) baseStart_569091 baseEnd_569091 := by
    simpa [prefixWord, tailWord_569091, baseEnd_569091] using wordTrace_append hprefix tailTrace_569091
  have hstable : (prefixWord ++ tailWord_569091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569091).length < 2 ^ (prefixWord ++ tailWord_569091).sum := by decide
  have hdescent : baseEnd_569091 < baseStart_569091 := by decide
  rcases family_descends (prefixWord ++ tailWord_569091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569111 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 3]
def baseStart_569111 : Nat := 118140960795 + 569111 * 2 ^ 59
def prefixEnd_569111 : Nat := 4983230072969 + 3 ^ 40 * 569111 * 2
def baseEnd_569111 : Nat := 129878883893790259686761

theorem tailTrace_569111 : CollatzResearch.WordTrace tailWord_569111 prefixEnd_569111 129878883893790259686761 := by
  unfold tailWord_569111
  simp only [CollatzResearch.WordTrace]
  refine ⟨20757183441215518265707187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13838122294143678843804791 20757183441215518265707187)
  ·
    refine ⟨31135775161823277398560781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20757183441215518265707187 31135775161823277398560781)
    ·
      refine ⟨11675915685683729024460293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31135775161823277398560781 11675915685683729024460293)
      ·
        refine ⟨2189234191065699192086305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11675915685683729024460293 2189234191065699192086305)
        ·
          refine ⟨1641925643299274394064729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2189234191065699192086305 1641925643299274394064729)
          ·
            refine ⟨1231444232474455795548547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641925643299274394064729 1231444232474455795548547)
            ·
              refine ⟨1847166348711683693322821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231444232474455795548547 1847166348711683693322821)
              ·
                refine ⟨346343690383440692498029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1847166348711683693322821 346343690383440692498029)
                ·
                  refine ⟨129878883893790259686761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346343690383440692498029 129878883893790259686761)
                  ·
                    rfl

theorem cell21_569111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].length) (baseStart_569111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569111 prefixEnd_569111 := by exact prefixLift 569111
  have htrace : WordTrace (prefixWord ++ tailWord_569111) baseStart_569111 baseEnd_569111 := by
    simpa [prefixWord, tailWord_569111, baseEnd_569111] using wordTrace_append hprefix tailTrace_569111
  have hstable : (prefixWord ++ tailWord_569111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569111).length < 2 ^ (prefixWord ++ tailWord_569111).sum := by decide
  have hdescent : baseEnd_569111 < baseStart_569111 := by decide
  rcases family_descends (prefixWord ++ tailWord_569111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569170 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_569170 : Nat := 118140960795 + 569170 * 2 ^ 59
def prefixEnd_569170 : Nat := 4983230072969 + 3 ^ 40 * 569170 * 2
def baseEnd_569170 : Nat := 129892348497619268203307

theorem tailTrace_569170 : CollatzResearch.WordTrace tailWord_569170 prefixEnd_569170 129892348497619268203307 := by
  unfold tailWord_569170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189833837000442835526241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13839556898667847561403309 5189833837000442835526241)
  ·
    refine ⟨3892375377750332126644681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5189833837000442835526241 3892375377750332126644681)
    ·
      refine ⟨2919281533312749094983511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3892375377750332126644681 2919281533312749094983511)
      ·
        refine ⟨4378922299969123642475267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919281533312749094983511 4378922299969123642475267)
        ·
          refine ⟨6568383449953685463712901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378922299969123642475267 6568383449953685463712901)
          ·
            refine ⟨1231571896866316024446169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6568383449953685463712901 1231571896866316024446169)
            ·
              refine ⟨923678922649737018334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231571896866316024446169 923678922649737018334627)
              ·
                refine ⟨1385518383974605527501941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923678922649737018334627 1385518383974605527501941)
                ·
                  refine ⟨129892348497619268203307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385518383974605527501941 129892348497619268203307)
                  ·
                    rfl

theorem cell21_569170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_569170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569170 prefixEnd_569170 := by exact prefixLift 569170
  have htrace : WordTrace (prefixWord ++ tailWord_569170) baseStart_569170 baseEnd_569170 := by
    simpa [prefixWord, tailWord_569170, baseEnd_569170] using wordTrace_append hprefix tailTrace_569170
  have hstable : (prefixWord ++ tailWord_569170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569170).length < 2 ^ (prefixWord ++ tailWord_569170).sum := by decide
  have hdescent : baseEnd_569170 < baseStart_569170 := by decide
  rcases family_descends (prefixWord ++ tailWord_569170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569277 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_569277 : Nat := 118140960795 + 569277 * 2 ^ 59
def prefixEnd_569277 : Nat := 4983230072969 + 3 ^ 40 * 569277 * 2
def baseEnd_569277 : Nat := 129916767355410859919755

theorem tailTrace_569277 : CollatzResearch.WordTrace tailWord_569277 prefixEnd_569277 129916767355410859919755 := by
  unfold tailWord_569277
  simp only [CollatzResearch.WordTrace]
  refine ⟨20763237958614128616250085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13842158639076085744166723 20763237958614128616250085)
  ·
    refine ⟨3893107117240149115546891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20763237958614128616250085 3893107117240149115546891)
    ·
      refine ⟨5839660675860223673320337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893107117240149115546891 5839660675860223673320337)
      ·
        refine ⟨4379745506895167754990253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5839660675860223673320337 4379745506895167754990253)
        ·
          refine ⟨1642404565085687908121345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4379745506895167754990253 1642404565085687908121345)
          ·
            refine ⟨1231803423814265931091009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1642404565085687908121345 1231803423814265931091009)
            ·
              refine ⟨923852567860699448318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231803423814265931091009 923852567860699448318257)
              ·
                refine ⟨692889425895524586238693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923852567860699448318257 692889425895524586238693)
                ·
                  refine ⟨129916767355410859919755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692889425895524586238693 129916767355410859919755)
                  ·
                    rfl

theorem cell21_569277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_569277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_569277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_569277 prefixEnd_569277 := by exact prefixLift 569277
  have htrace : WordTrace (prefixWord ++ tailWord_569277) baseStart_569277 baseEnd_569277 := by
    simpa [prefixWord, tailWord_569277, baseEnd_569277] using wordTrace_append hprefix tailTrace_569277
  have hstable : (prefixWord ++ tailWord_569277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569277).length < 2 ^ (prefixWord ++ tailWord_569277).sum := by decide
  have hdescent : baseEnd_569277 < baseStart_569277 := by decide
  rcases family_descends (prefixWord ++ tailWord_569277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
