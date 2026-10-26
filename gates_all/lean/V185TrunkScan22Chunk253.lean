import V185TrunkScan22Chunk252

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2255772 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_2255772 : Nat := 118140960795 + 2255772 * 2 ^ 59
def prefixEnd_2255772 : Nat := 4983230072969 + 3 ^ 40 * 2255772 * 2
def baseEnd_2255772 : Nat := 257398951767567447861311

theorem tailTrace_2255772 : CollatzResearch.WordTrace tailWord_2255772 prefixEnd_2255772 257398951767567447861311 := by
  unfold tailWord_2255772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41137381991865387015488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54849842655820516020651713 41137381991865387015488785)
  ·
    refine ⟨30853036493899040261616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41137381991865387015488785 30853036493899040261616589)
    ·
      refine ⟨11569888685212140098106221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30853036493899040261616589 11569888685212140098106221)
      ·
        refine ⟨4338708256954552536789833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11569888685212140098106221 4338708256954552536789833)
        ·
          refine ⟨3254031192715914402592375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4338708256954552536789833 3254031192715914402592375)
          ·
            refine ⟨4881046789073871603888563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254031192715914402592375 4881046789073871603888563)
            ·
              refine ⟨7321570183610807405832845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881046789073871603888563 7321570183610807405832845)
              ·
                refine ⟨2745588818854052777187317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7321570183610807405832845 2745588818854052777187317)
                ·
                  refine ⟨257398951767567447861311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2745588818854052777187317 257398951767567447861311)
                  ·
                    rfl

theorem cell22_2255772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_2255772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255772 prefixEnd_2255772 := by exact prefixLift 2255772
  have htrace : WordTrace (prefixWord ++ tailWord_2255772) baseStart_2255772 baseEnd_2255772 := by
    simpa [prefixWord, tailWord_2255772, baseEnd_2255772] using wordTrace_append hprefix tailTrace_2255772
  have hstable : (prefixWord ++ tailWord_2255772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255772).length < 2 ^ (prefixWord ++ tailWord_2255772).sum := by decide
  have hdescent : baseEnd_2255772 < baseStart_2255772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255802 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_2255802 : Nat := 118140960795 + 2255802 * 2 ^ 59
def prefixEnd_2255802 : Nat := 4983230072969 + 3 ^ 40 * 2255802 * 2
def baseEnd_2255802 : Nat := 772207124915792265333841

theorem tailTrace_2255802 : CollatzResearch.WordTrace tailWord_2255802 prefixEnd_2255802 772207124915792265333841 := by
  unfold tailWord_2255802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20568964543405522288642415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54850572115748059436379773 20568964543405522288642415)
  ·
    refine ⟨30853446815108283432963623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20568964543405522288642415 30853446815108283432963623)
    ·
      refine ⟨46280170222662425149445435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30853446815108283432963623 46280170222662425149445435)
      ·
        refine ⟨69420255333993637724168153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46280170222662425149445435 69420255333993637724168153)
        ·
          refine ⟨52065191500495228293126115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69420255333993637724168153 52065191500495228293126115)
          ·
            refine ⟨78097787250742842439689173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52065191500495228293126115 78097787250742842439689173)
            ·
              refine ⟨1830416888689285369680215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78097787250742842439689173 1830416888689285369680215)
              ·
                refine ⟨2745625333033928054520323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830416888689285369680215 2745625333033928054520323)
                ·
                  refine ⟨4118437999550892081780485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745625333033928054520323 4118437999550892081780485)
                  ·
                    refine ⟨772207124915792265333841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118437999550892081780485 772207124915792265333841)
                    ·
                      rfl

theorem cell22_2255802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_2255802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255802 prefixEnd_2255802 := by exact prefixLift 2255802
  have htrace : WordTrace (prefixWord ++ tailWord_2255802) baseStart_2255802 baseEnd_2255802 := by
    simpa [prefixWord, tailWord_2255802, baseEnd_2255802] using wordTrace_append hprefix tailTrace_2255802
  have hstable : (prefixWord ++ tailWord_2255802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255802).length < 2 ^ (prefixWord ++ tailWord_2255802).sum := by decide
  have hdescent : baseEnd_2255802 < baseStart_2255802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255815 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2255815 : Nat := 118140960795 + 2255815 * 2 ^ 59
def prefixEnd_2255815 : Nat := 4983230072969 + 3 ^ 40 * 2255815 * 2
def baseEnd_2255815 : Nat := 772211575081464564758801

theorem tailTrace_2255815 : CollatzResearch.WordTrace tailWord_2255815 prefixEnd_2255815 772211575081464564758801 := by
  unfold tailWord_2255815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82276332322574992374792899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54850888215049994916528599 82276332322574992374792899)
  ·
    refine ⟨123414498483862488562189349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82276332322574992374792899 123414498483862488562189349)
    ·
      refine ⟨23140218465724216605410503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123414498483862488562189349 23140218465724216605410503)
      ·
        refine ⟨34710327698586324908115755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23140218465724216605410503 34710327698586324908115755)
        ·
          refine ⟨52065491547879487362173633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34710327698586324908115755 52065491547879487362173633)
          ·
            refine ⟨39049118660909615521630225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52065491547879487362173633 39049118660909615521630225)
            ·
              refine ⟨29286838995682211641222669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39049118660909615521630225 29286838995682211641222669)
              ·
                refine ⟨10982564623380829365458501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29286838995682211641222669 10982564623380829365458501)
                ·
                  refine ⟨2059230866883905506023469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10982564623380829365458501 2059230866883905506023469)
                  ·
                    refine ⟨772211575081464564758801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059230866883905506023469 772211575081464564758801)
                    ·
                      rfl

theorem cell22_2255815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2255815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255815 prefixEnd_2255815 := by exact prefixLift 2255815
  have htrace : WordTrace (prefixWord ++ tailWord_2255815) baseStart_2255815 baseEnd_2255815 := by
    simpa [prefixWord, tailWord_2255815, baseEnd_2255815] using wordTrace_append hprefix tailTrace_2255815
  have hstable : (prefixWord ++ tailWord_2255815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255815).length < 2 ^ (prefixWord ++ tailWord_2255815).sum := by decide
  have hdescent : baseEnd_2255815 < baseStart_2255815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255821 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2255821 : Nat := 118140960795 + 2255821 * 2 ^ 59
def prefixEnd_2255821 : Nat := 4983230072969 + 3 ^ 40 * 2255821 * 2
def baseEnd_2255821 : Nat := 772213629004082549108783

theorem tailTrace_2255821 : CollatzResearch.WordTrace tailWord_2255821 prefixEnd_2255821 772213629004082549108783 := by
  unfold tailWord_2255821
  simp only [CollatzResearch.WordTrace]
  refine ⟨82276551160553255399511317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54851034107035503599674211 82276551160553255399511317)
  ·
    refine ⟨3856713335650933846852093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82276551160553255399511317 3856713335650933846852093)
    ·
      refine ⟨1446267500869100192569535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3856713335650933846852093 1446267500869100192569535)
      ·
        refine ⟨2169401251303650288854303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446267500869100192569535 2169401251303650288854303)
        ·
          refine ⟨3254101876955475433281455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169401251303650288854303 3254101876955475433281455)
          ·
            refine ⟨4881152815433213149922183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3254101876955475433281455 4881152815433213149922183)
            ·
              refine ⟨7321729223149819724883275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881152815433213149922183 7321729223149819724883275)
              ·
                refine ⟨10982593834724729587324913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7321729223149819724883275 10982593834724729587324913)
                ·
                  refine ⟨8236945376043547190493685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10982593834724729587324913 8236945376043547190493685)
                  ·
                    refine ⟨772213629004082549108783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8236945376043547190493685 772213629004082549108783)
                    ·
                      rfl

theorem cell22_2255821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2255821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255821 prefixEnd_2255821 := by exact prefixLift 2255821
  have htrace : WordTrace (prefixWord ++ tailWord_2255821) baseStart_2255821 baseEnd_2255821 := by
    simpa [prefixWord, tailWord_2255821, baseEnd_2255821] using wordTrace_append hprefix tailTrace_2255821
  have hstable : (prefixWord ++ tailWord_2255821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255821).length < 2 ^ (prefixWord ++ tailWord_2255821).sum := by decide
  have hdescent : baseEnd_2255821 < baseStart_2255821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255832 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_2255832 : Nat := 118140960795 + 2255832 * 2 ^ 59
def prefixEnd_2255832 : Nat := 4983230072969 + 3 ^ 40 * 2255832 * 2
def baseEnd_2255832 : Nat := 772217394528882187083749

theorem tailTrace_2255832 : CollatzResearch.WordTrace tailWord_2255832 prefixEnd_2255832 772217394528882187083749 := by
  unfold tailWord_2255832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41138476181756702139080875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54851301575675602852107833 41138476181756702139080875)
  ·
    refine ⟨61707714272635053208621313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41138476181756702139080875 61707714272635053208621313)
    ·
      refine ⟨46280785704476289906465985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61707714272635053208621313 46280785704476289906465985)
      ·
        refine ⟨34710589278357217429849489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46280785704476289906465985 34710589278357217429849489)
        ·
          refine ⟨26032941958767913072387117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34710589278357217429849489 26032941958767913072387117)
          ·
            refine ⟨9762353234537967402145169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26032941958767913072387117 9762353234537967402145169)
            ·
              refine ⟨7321764925903475551608877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9762353234537967402145169 7321764925903475551608877)
              ·
                refine ⟨2745661847213803331853329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7321764925903475551608877 2745661847213803331853329)
                ·
                  refine ⟨2059246385410352498889997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2745661847213803331853329 2059246385410352498889997)
                  ·
                    refine ⟨772217394528882187083749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059246385410352498889997 772217394528882187083749)
                    ·
                      rfl

theorem cell22_2255832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_2255832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255832 prefixEnd_2255832 := by exact prefixLift 2255832
  have htrace : WordTrace (prefixWord ++ tailWord_2255832) baseStart_2255832 baseEnd_2255832 := by
    simpa [prefixWord, tailWord_2255832, baseEnd_2255832] using wordTrace_append hprefix tailTrace_2255832
  have hstable : (prefixWord ++ tailWord_2255832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255832).length < 2 ^ (prefixWord ++ tailWord_2255832).sum := by decide
  have hdescent : baseEnd_2255832 < baseStart_2255832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255847 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2255847 : Nat := 118140960795 + 2255847 * 2 ^ 59
def prefixEnd_2255847 : Nat := 4983230072969 + 3 ^ 40 * 2255847 * 2
def baseEnd_2255847 : Nat := 772222529335427147958703

theorem tailTrace_2255847 : CollatzResearch.WordTrace tailWord_2255847 prefixEnd_2255847 772222529335427147958703 := by
  unfold tailWord_2255847
  simp only [CollatzResearch.WordTrace]
  refine ⟨82277499458459061839957795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54851666305639374559971863 82277499458459061839957795)
  ·
    refine ⟨123416249187688592759936693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82277499458459061839957795 123416249187688592759936693)
    ·
      refine ⟨11570273361345805571244065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123416249187688592759936693 11570273361345805571244065)
      ·
        refine ⟨8677705021009354178433049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11570273361345805571244065 8677705021009354178433049)
        ·
          refine ⟨6508278765757015633824787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8677705021009354178433049 6508278765757015633824787)
          ·
            refine ⟨9762418148635523450737181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508278765757015633824787 9762418148635523450737181)
            ·
              refine ⟨3660906805738321294026443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9762418148635523450737181 3660906805738321294026443)
              ·
                refine ⟨5491360208607481941039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660906805738321294026443 5491360208607481941039665)
                ·
                  refine ⟨4118520156455611455779749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5491360208607481941039665 4118520156455611455779749)
                  ·
                    refine ⟨772222529335427147958703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118520156455611455779749 772222529335427147958703)
                    ·
                      rfl

theorem cell22_2255847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2255847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255847 prefixEnd_2255847 := by exact prefixLift 2255847
  have htrace : WordTrace (prefixWord ++ tailWord_2255847) baseStart_2255847 baseEnd_2255847 := by
    simpa [prefixWord, tailWord_2255847, baseEnd_2255847] using wordTrace_append hprefix tailTrace_2255847
  have hstable : (prefixWord ++ tailWord_2255847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255847).length < 2 ^ (prefixWord ++ tailWord_2255847).sum := by decide
  have hdescent : baseEnd_2255847 < baseStart_2255847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255877 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_2255877 : Nat := 118140960795 + 2255877 * 2 ^ 59
def prefixEnd_2255877 : Nat := 4983230072969 + 3 ^ 40 * 2255877 * 2
def baseEnd_2255877 : Nat := 772232798948517069708611

theorem tailTrace_2255877 : CollatzResearch.WordTrace tailWord_2255877 prefixEnd_2255877 772232798948517069708611 := by
  unfold tailWord_2255877
  simp only [CollatzResearch.WordTrace]
  refine ⟨82278593648350376963549885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54852395765566917975699923 82278593648350376963549885)
  ·
    refine ⟨30854472618131391361331207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82278593648350376963549885 30854472618131391361331207)
    ·
      refine ⟨46281708927197087041996811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30854472618131391361331207 46281708927197087041996811)
      ·
        refine ⟨69422563390795630562995217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46281708927197087041996811 69422563390795630562995217)
        ·
          refine ⟨52066922543096722922246413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69422563390795630562995217 52066922543096722922246413)
          ·
            refine ⟨19525095953661271095842405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52066922543096722922246413 19525095953661271095842405)
            ·
              refine ⟨3660955491311488330470451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19525095953661271095842405 3660955491311488330470451)
              ·
                refine ⟨5491433236967232495705677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660955491311488330470451 5491433236967232495705677)
                ·
                  refine ⟨2059287463862712185889629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5491433236967232495705677 2059287463862712185889629)
                  ·
                    refine ⟨772232798948517069708611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059287463862712185889629 772232798948517069708611)
                    ·
                      rfl

theorem cell22_2255877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_2255877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255877 prefixEnd_2255877 := by exact prefixLift 2255877
  have htrace : WordTrace (prefixWord ++ tailWord_2255877) baseStart_2255877 baseEnd_2255877 := by
    simpa [prefixWord, tailWord_2255877, baseEnd_2255877] using wordTrace_append hprefix tailTrace_2255877
  have hstable : (prefixWord ++ tailWord_2255877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255877).length < 2 ^ (prefixWord ++ tailWord_2255877).sum := by decide
  have hdescent : baseEnd_2255877 < baseStart_2255877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255954 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_2255954 : Nat := 118140960795 + 2255954 * 2 ^ 59
def prefixEnd_2255954 : Nat := 4983230072969 + 3 ^ 40 * 2255954 * 2
def baseEnd_2255954 : Nat := 772259157622114535533375

theorem tailTrace_2255954 : CollatzResearch.WordTrace tailWord_2255954 prefixEnd_2255954 772259157622114535533375 := by
  unfold tailWord_2255954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20570350517267854778525729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54854268046047612742735277 20570350517267854778525729)
  ·
    refine ⟨15427762887950891083894297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20570350517267854778525729 15427762887950891083894297)
    ·
      refine ⟨11570822165963168312920723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15427762887950891083894297 11570822165963168312920723)
      ·
        refine ⟨17356233248944752469381085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11570822165963168312920723 17356233248944752469381085)
        ·
          refine ⟨6508587468354282176017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17356233248944752469381085 6508587468354282176017907)
          ·
            refine ⟨9762881202531423264026861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6508587468354282176017907 9762881202531423264026861)
            ·
              refine ⟨3661080450949283724010073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9762881202531423264026861 3661080450949283724010073)
              ·
                refine ⟨2745810338211962793007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661080450949283724010073 2745810338211962793007555)
                ·
                  refine ⟨4118715507317944189511333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745810338211962793007555 4118715507317944189511333)
                  ·
                    refine ⟨772259157622114535533375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118715507317944189511333 772259157622114535533375)
                    ·
                      rfl

theorem cell22_2255954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_2255954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255954 prefixEnd_2255954 := by exact prefixLift 2255954
  have htrace : WordTrace (prefixWord ++ tailWord_2255954) baseStart_2255954 baseEnd_2255954 := by
    simpa [prefixWord, tailWord_2255954, baseEnd_2255954] using wordTrace_append hprefix tailTrace_2255954
  have hstable : (prefixWord ++ tailWord_2255954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255954).length < 2 ^ (prefixWord ++ tailWord_2255954).sum := by decide
  have hdescent : baseEnd_2255954 < baseStart_2255954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2255984 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_2255984 : Nat := 118140960795 + 2255984 * 2 ^ 59
def prefixEnd_2255984 : Nat := 4983230072969 + 3 ^ 40 * 2255984 * 2
def baseEnd_2255984 : Nat := 772269427235204457283283

theorem tailTrace_2255984 : CollatzResearch.WordTrace tailWord_2255984 prefixEnd_2255984 772269427235204457283283 := by
  unfold tailWord_2255984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41141248129481367118847503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54854997505975156158463337 41141248129481367118847503)
  ·
    refine ⟨61711872194222050678271255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41141248129481367118847503 61711872194222050678271255)
    ·
      refine ⟨92567808291333076017406883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61711872194222050678271255 92567808291333076017406883)
      ·
        refine ⟨138851712436999614026110325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92567808291333076017406883 138851712436999614026110325)
        ·
          refine ⟨13017348040968713814947843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138851712436999614026110325 13017348040968713814947843)
          ·
            refine ⟨19526022061453070722421765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017348040968713814947843 19526022061453070722421765)
            ·
              refine ⟨3661129136522450760454081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19526022061453070722421765 3661129136522450760454081)
              ·
                refine ⟨2745846852391838070340561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3661129136522450760454081 2745846852391838070340561)
                ·
                  refine ⟨2059385139293878552755421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2745846852391838070340561 2059385139293878552755421)
                  ·
                    refine ⟨772269427235204457283283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059385139293878552755421 772269427235204457283283)
                    ·
                      rfl

theorem cell22_2255984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_2255984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2255984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2255984 prefixEnd_2255984 := by exact prefixLift 2255984
  have htrace : WordTrace (prefixWord ++ tailWord_2255984) baseStart_2255984 baseEnd_2255984 := by
    simpa [prefixWord, tailWord_2255984, baseEnd_2255984] using wordTrace_append hprefix tailTrace_2255984
  have hstable : (prefixWord ++ tailWord_2255984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2255984).length < 2 ^ (prefixWord ++ tailWord_2255984).sum := by decide
  have hdescent : baseEnd_2255984 < baseStart_2255984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2255984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256014 : List Nat := [4, 1, 1, 3, 2, 2, 3, 6]
def baseStart_2256014 : Nat := 118140960795 + 2256014 * 2 ^ 59
def prefixEnd_2256014 : Nat := 4983230072969 + 3 ^ 40 * 2256014 * 2
def baseEnd_2256014 : Nat := 85808855205366042114799

theorem tailTrace_2256014 : CollatzResearch.WordTrace tailWord_2256014 prefixEnd_2256014 85808855205366042114799 := by
  unfold tailWord_2256014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10285448806106756170160887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54855726965902699574191397 10285448806106756170160887)
  ·
    refine ⟨15428173209160134255241331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10285448806106756170160887 15428173209160134255241331)
    ·
      refine ⟨23142259813740201382861997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15428173209160134255241331 23142259813740201382861997)
      ·
        refine ⟨8678347430152575518573249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23142259813740201382861997 8678347430152575518573249)
        ·
          refine ⟨6508760572614431638929937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8678347430152575518573249 6508760572614431638929937)
          ·
            refine ⟨4881570429460823729197453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6508760572614431638929937 4881570429460823729197453)
            ·
              refine ⟨1830588911047808898449045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4881570429460823729197453 1830588911047808898449045)
              ·
                refine ⟨85808855205366042114799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1830588911047808898449045 85808855205366042114799)
                ·
                  rfl

theorem cell22_2256014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_2256014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256014 prefixEnd_2256014 := by exact prefixLift 2256014
  have htrace : WordTrace (prefixWord ++ tailWord_2256014) baseStart_2256014 baseEnd_2256014 := by
    simpa [prefixWord, tailWord_2256014, baseEnd_2256014] using wordTrace_append hprefix tailTrace_2256014
  have hstable : (prefixWord ++ tailWord_2256014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256014).length < 2 ^ (prefixWord ++ tailWord_2256014).sum := by decide
  have hdescent : baseEnd_2256014 < baseStart_2256014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256057 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_2256057 : Nat := 118140960795 + 2256057 * 2 ^ 59
def prefixEnd_2256057 : Nat := 4983230072969 + 3 ^ 40 * 2256057 * 2
def baseEnd_2256057 : Nat := 772294416627056600208059

theorem tailTrace_2256057 : CollatzResearch.WordTrace tailWord_2256057 prefixEnd_2256057 772294416627056600208059 := by
  unfold tailWord_2256057
  simp only [CollatzResearch.WordTrace]
  refine ⟨82285158787698267705102425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54856772525132178470068283 82285158787698267705102425)
  ·
    refine ⟨61713869090773700778826819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82285158787698267705102425 61713869090773700778826819)
    ·
      refine ⟨92570803636160551168240229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61713869090773700778826819 92570803636160551168240229)
      ·
        refine ⟨17357025681780103344045043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92570803636160551168240229 17357025681780103344045043)
        ·
          refine ⟨26035538522670155016067565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17357025681780103344045043 26035538522670155016067565)
          ·
            refine ⟨9763326946001308131025337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26035538522670155016067565 9763326946001308131025337)
            ·
              refine ⟨7322495209500981098269003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9763326946001308131025337 7322495209500981098269003)
              ·
                refine ⟨10983742814251471647403505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322495209500981098269003 10983742814251471647403505)
                ·
                  refine ⟨8237807110688603735552629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10983742814251471647403505 8237807110688603735552629)
                  ·
                    refine ⟨772294416627056600208059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8237807110688603735552629 772294416627056600208059)
                    ·
                      rfl

theorem cell22_2256057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_2256057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256057 prefixEnd_2256057 := by exact prefixLift 2256057
  have htrace : WordTrace (prefixWord ++ tailWord_2256057) baseStart_2256057 baseEnd_2256057 := by
    simpa [prefixWord, tailWord_2256057, baseEnd_2256057] using wordTrace_append hprefix tailTrace_2256057
  have hstable : (prefixWord ++ tailWord_2256057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256057).length < 2 ^ (prefixWord ++ tailWord_2256057).sum := by decide
  have hdescent : baseEnd_2256057 < baseStart_2256057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256072 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2256072 : Nat := 118140960795 + 2256072 * 2 ^ 59
def prefixEnd_2256072 : Nat := 4983230072969 + 3 ^ 40 * 2256072 * 2
def baseEnd_2256072 : Nat := 772299551433601561083013

theorem tailTrace_2256072 : CollatzResearch.WordTrace tailWord_2256072 prefixEnd_2256072 772299551433601561083013 := by
  unfold tailWord_2256072
  simp only [CollatzResearch.WordTrace]
  refine ⟨41142852941321962633449235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54857137255095950177932313 41142852941321962633449235)
  ·
    refine ⟨61714279411982943950173853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41142852941321962633449235 61714279411982943950173853)
    ·
      refine ⟨23142854779493603981315195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61714279411982943950173853 23142854779493603981315195)
      ·
        refine ⟨34714282169240405971972793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23142854779493603981315195 34714282169240405971972793)
        ·
          refine ⟨26035711626930304478979595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34714282169240405971972793 26035711626930304478979595)
          ·
            refine ⟨39053567440395456718469393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26035711626930304478979595 39053567440395456718469393)
            ·
              refine ⟨29290175580296592538852045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39053567440395456718469393 29290175580296592538852045)
              ·
                refine ⟨10983815842611222202069517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29290175580296592538852045 10983815842611222202069517)
                ·
                  refine ⟨4118930940979208325776069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10983815842611222202069517 4118930940979208325776069)
                  ·
                    refine ⟨772299551433601561083013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4118930940979208325776069 772299551433601561083013)
                    ·
                      rfl

theorem cell22_2256072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2256072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256072 prefixEnd_2256072 := by exact prefixLift 2256072
  have htrace : WordTrace (prefixWord ++ tailWord_2256072) baseStart_2256072 baseEnd_2256072 := by
    simpa [prefixWord, tailWord_2256072, baseEnd_2256072] using wordTrace_append hprefix tailTrace_2256072
  have hstable : (prefixWord ++ tailWord_2256072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256072).length < 2 ^ (prefixWord ++ tailWord_2256072).sum := by decide
  have hdescent : baseEnd_2256072 < baseStart_2256072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256119 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 2, 3]
def baseStart_2256119 : Nat := 118140960795 + 2256119 * 2 ^ 59
def prefixEnd_2256119 : Nat := 4983230072969 + 3 ^ 40 * 2256119 * 2
def baseEnd_2256119 : Nat := 772315640494109105157869

theorem tailTrace_2256119 : CollatzResearch.WordTrace tailWord_2256119 prefixEnd_2256119 772315640494109105157869 := by
  unfold tailWord_2256119
  simp only [CollatzResearch.WordTrace]
  refine ⟨82287420113473652293859411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54858280075649101529239607 82287420113473652293859411)
  ·
    refine ⟨123431130170210478440789117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82287420113473652293859411 123431130170210478440789117)
    ·
      refine ⟨46286673813828929415295919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123431130170210478440789117 46286673813828929415295919)
      ·
        refine ⟨69430010720743394122943879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46286673813828929415295919 69430010720743394122943879)
        ·
          refine ⟨104145016081115091184415819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69430010720743394122943879 104145016081115091184415819)
          ·
            refine ⟨156217524121672636776623729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104145016081115091184415819 156217524121672636776623729)
            ·
              refine ⟨117163143091254477582467797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156217524121672636776623729 117163143091254477582467797)
              ·
                refine ⟨2746011166201276818339089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117163143091254477582467797 2746011166201276818339089)
                ·
                  refine ⟨2059508374650957613754317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746011166201276818339089 2059508374650957613754317)
                  ·
                    refine ⟨772315640494109105157869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059508374650957613754317 772315640494109105157869)
                    ·
                      rfl

theorem cell22_2256119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_2256119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256119 prefixEnd_2256119 := by exact prefixLift 2256119
  have htrace : WordTrace (prefixWord ++ tailWord_2256119) baseStart_2256119 baseEnd_2256119 := by
    simpa [prefixWord, tailWord_2256119, baseEnd_2256119] using wordTrace_append hprefix tailTrace_2256119
  have hstable : (prefixWord ++ tailWord_2256119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256119).length < 2 ^ (prefixWord ++ tailWord_2256119).sum := by decide
  have hdescent : baseEnd_2256119 < baseStart_2256119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256181 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2256181 : Nat := 118140960795 + 2256181 * 2 ^ 59
def prefixEnd_2256181 : Nat := 4983230072969 + 3 ^ 40 * 2256181 * 2
def baseEnd_2256181 : Nat := 772336864361161610107679

theorem tailTrace_2256181 : CollatzResearch.WordTrace tailWord_2256181 prefixEnd_2256181 772336864361161610107679 := by
  unfold tailWord_2256181
  simp only [CollatzResearch.WordTrace]
  refine ⟨82289681439249036882616397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54859787626166024588410931 82289681439249036882616397)
  ·
    refine ⟨30858630539718388830981149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82289681439249036882616397 30858630539718388830981149)
    ·
      refine ⟨11571986452394395811617931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30858630539718388830981149 11571986452394395811617931)
      ·
        refine ⟨17357979678591593717426897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11571986452394395811617931 17357979678591593717426897)
        ·
          refine ⟨13018484758943695288070173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17357979678591593717426897 13018484758943695288070173)
          ·
            refine ⟨4881931784603885733026315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13018484758943695288070173 4881931784603885733026315)
            ·
              refine ⟨7322897676905828599539473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881931784603885733026315 7322897676905828599539473)
              ·
                refine ⟨5492173257679371449654605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7322897676905828599539473 5492173257679371449654605)
                ·
                  refine ⟨2059564971629764293620477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5492173257679371449654605 2059564971629764293620477)
                  ·
                    refine ⟨772336864361161610107679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059564971629764293620477 772336864361161610107679)
                    ·
                      rfl

theorem cell22_2256181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2256181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256181 prefixEnd_2256181 := by exact prefixLift 2256181
  have htrace : WordTrace (prefixWord ++ tailWord_2256181) baseStart_2256181 baseEnd_2256181 := by
    simpa [prefixWord, tailWord_2256181, baseEnd_2256181] using wordTrace_append hprefix tailTrace_2256181
  have hstable : (prefixWord ++ tailWord_2256181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256181).length < 2 ^ (prefixWord ++ tailWord_2256181).sum := by decide
  have hdescent : baseEnd_2256181 < baseStart_2256181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256192 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_2256192 : Nat := 118140960795 + 2256192 * 2 ^ 59
def prefixEnd_2256192 : Nat := 4983230072969 + 3 ^ 40 * 2256192 * 2
def baseEnd_2256192 : Nat := 772340629885961248082645

theorem tailTrace_2256192 : CollatzResearch.WordTrace tailWord_2256192 prefixEnd_2256192 772340629885961248082645 := by
  unfold tailWord_2256192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41145041321104592880633415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54860055094806123840844553 41145041321104592880633415)
  ·
    refine ⟨61717561981656889320950123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41145041321104592880633415 61717561981656889320950123)
    ·
      refine ⟨92576342972485333981425185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61717561981656889320950123 92576342972485333981425185)
      ·
        refine ⟨69432257229364000486068889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92576342972485333981425185 69432257229364000486068889)
        ·
          refine ⟨52074192922023000364551667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69432257229364000486068889 52074192922023000364551667)
          ·
            refine ⟨78111289383034500546827501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52074192922023000364551667 78111289383034500546827501)
            ·
              refine ⟨29291733518637937705060313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78111289383034500546827501 29291733518637937705060313)
              ·
                refine ⟨21968800138978453278795235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29291733518637937705060313 21968800138978453278795235)
                ·
                  refine ⟨32953200208467679918192853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21968800138978453278795235 32953200208467679918192853)
                  ·
                    refine ⟨772340629885961248082645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32953200208467679918192853 772340629885961248082645)
                    ·
                      rfl

theorem cell22_2256192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_2256192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256192 prefixEnd_2256192 := by exact prefixLift 2256192
  have htrace : WordTrace (prefixWord ++ tailWord_2256192) baseStart_2256192 baseEnd_2256192 := by
    simpa [prefixWord, tailWord_2256192, baseEnd_2256192] using wordTrace_append hprefix tailTrace_2256192
  have hstable : (prefixWord ++ tailWord_2256192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256192).length < 2 ^ (prefixWord ++ tailWord_2256192).sum := by decide
  have hdescent : baseEnd_2256192 < baseStart_2256192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256301 : List Nat := [1, 5, 2, 2, 1, 1, 2, 8]
def baseStart_2256301 : Nat := 118140960795 + 2256301 * 2 ^ 59
def prefixEnd_2256301 : Nat := 4983230072969 + 3 ^ 40 * 2256301 * 2
def baseEnd_2256301 : Nat := 85819771423724588567479

theorem tailTrace_2256301 : CollatzResearch.WordTrace tailWord_2256301 prefixEnd_2256301 85819771423724588567479 := by
  unfold tailWord_2256301
  simp only [CollatzResearch.WordTrace]
  refine ⟨82294058198814297376984757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54862705465876198251323171 82294058198814297376984757)
  ·
    refine ⟨7715067956138840379092321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82294058198814297376984757 7715067956138840379092321)
    ·
      refine ⟨5786300967104130284319241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7715067956138840379092321 5786300967104130284319241)
      ·
        refine ⟨4339725725328097713239431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5786300967104130284319241 4339725725328097713239431)
        ·
          refine ⟨6509588587992146569859147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339725725328097713239431 6509588587992146569859147)
          ·
            refine ⟨9764382881988219854788721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509588587992146569859147 9764382881988219854788721)
            ·
              refine ⟨7323287161491164891091541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764382881988219854788721 7323287161491164891091541)
              ·
                refine ⟨85819771423724588567479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7323287161491164891091541 85819771423724588567479)
                ·
                  rfl

theorem cell22_2256301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 8].length) (baseStart_2256301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256301 prefixEnd_2256301 := by exact prefixLift 2256301
  have htrace : WordTrace (prefixWord ++ tailWord_2256301) baseStart_2256301 baseEnd_2256301 := by
    simpa [prefixWord, tailWord_2256301, baseEnd_2256301] using wordTrace_append hprefix tailTrace_2256301
  have hstable : (prefixWord ++ tailWord_2256301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256301).length < 2 ^ (prefixWord ++ tailWord_2256301).sum := by decide
  have hdescent : baseEnd_2256301 < baseStart_2256301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256344 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2256344 : Nat := 118140960795 + 2256344 * 2 ^ 59
def prefixEnd_2256344 : Nat := 4983230072969 + 3 ^ 40 * 2256344 * 2
def baseEnd_2256344 : Nat := 772392662592283518282179

theorem tailTrace_2256344 : CollatzResearch.WordTrace tailWord_2256344 prefixEnd_2256344 772392662592283518282179 := by
  unfold tailWord_2256344
  simp only [CollatzResearch.WordTrace]
  refine ⟨41147813268829257860400043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54863751025105677147200057 41147813268829257860400043)
  ·
    refine ⟨61721719903243886790600065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41147813268829257860400043 61721719903243886790600065)
    ·
      refine ⟨46291289927432915092950049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61721719903243886790600065 46291289927432915092950049)
      ·
        refine ⟨34718467445574686319712537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46291289927432915092950049 34718467445574686319712537)
        ·
          refine ⟨26038850584181014739784403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34718467445574686319712537 26038850584181014739784403)
          ·
            refine ⟨39058275876271522109676605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26038850584181014739784403 39058275876271522109676605)
            ·
              refine ⟨14646853453601820791128727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39058275876271522109676605 14646853453601820791128727)
              ·
                refine ⟨21970280180402731186693091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14646853453601820791128727 21970280180402731186693091)
                ·
                  refine ⟨32955420270604096780039637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21970280180402731186693091 32955420270604096780039637)
                  ·
                    refine ⟨772392662592283518282179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32955420270604096780039637 772392662592283518282179)
                    ·
                      rfl

theorem cell22_2256344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2256344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256344 prefixEnd_2256344 := by exact prefixLift 2256344
  have htrace : WordTrace (prefixWord ++ tailWord_2256344) baseStart_2256344 baseEnd_2256344 := by
    simpa [prefixWord, tailWord_2256344, baseEnd_2256344] using wordTrace_append hprefix tailTrace_2256344
  have hstable : (prefixWord ++ tailWord_2256344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256344).length < 2 ^ (prefixWord ++ tailWord_2256344).sum := by decide
  have hdescent : baseEnd_2256344 < baseStart_2256344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256346 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_2256346 : Nat := 118140960795 + 2256346 * 2 ^ 59
def prefixEnd_2256346 : Nat := 4983230072969 + 3 ^ 40 * 2256346 * 2
def baseEnd_2256346 : Nat := 257464449077718726577391

theorem tailTrace_2256346 : CollatzResearch.WordTrace tailWord_2256346 prefixEnd_2256346 257464449077718726577391 := by
  unfold tailWord_2256346
  simp only [CollatzResearch.WordTrace]
  refine ⟨20573924870912817515593223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54863799655767513374915261 20573924870912817515593223)
  ·
    refine ⟨30860887306369226273389835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20573924870912817515593223 30860887306369226273389835)
    ·
      refine ⟨46291330959553839410084753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30860887306369226273389835 46291330959553839410084753)
      ·
        refine ⟨34718498219665379557563565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46291330959553839410084753 34718498219665379557563565)
        ·
          refine ⟨13019436832374517334086337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34718498219665379557563565 13019436832374517334086337)
          ·
            refine ⟨9764577624280888000564753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13019436832374517334086337 9764577624280888000564753)
            ·
              refine ⟨7323433218210666000423565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764577624280888000564753 7323433218210666000423565)
              ·
                refine ⟨2746287456828999750158837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7323433218210666000423565 2746287456828999750158837)
                ·
                  refine ⟨257464449077718726577391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2746287456828999750158837 257464449077718726577391)
                  ·
                    rfl

theorem cell22_2256346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_2256346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256346 prefixEnd_2256346 := by exact prefixLift 2256346
  have htrace : WordTrace (prefixWord ++ tailWord_2256346) baseStart_2256346 baseEnd_2256346 := by
    simpa [prefixWord, tailWord_2256346, baseEnd_2256346] using wordTrace_append hprefix tailTrace_2256346
  have hstable : (prefixWord ++ tailWord_2256346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256346).length < 2 ^ (prefixWord ++ tailWord_2256346).sum := by decide
  have hdescent : baseEnd_2256346 < baseStart_2256346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256391 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 6]
def baseStart_2256391 : Nat := 118140960795 + 2256391 * 2 ^ 59
def prefixEnd_2256391 : Nat := 4983230072969 + 3 ^ 40 * 2256391 * 2
def baseEnd_2256391 : Nat := 257469583884263687452345

theorem tailTrace_2256391 : CollatzResearch.WordTrace tailWord_2256391 prefixEnd_2256391 257469583884263687452345 := by
  unfold tailWord_2256391
  simp only [CollatzResearch.WordTrace]
  refine ⟨82297340768488242747761027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54864893845658828498507351 82297340768488242747761027)
  ·
    refine ⟨123446011152732364121641541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82297340768488242747761027 123446011152732364121641541)
    ·
      refine ⟨23146127091137318272807789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123446011152732364121641541 23146127091137318272807789)
      ·
        refine ⟨8679797659176494352302921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23146127091137318272807789 8679797659176494352302921)
        ·
          refine ⟨6509848244382370764227191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8679797659176494352302921 6509848244382370764227191)
          ·
            refine ⟨9764772366573556146340787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509848244382370764227191 9764772366573556146340787)
            ·
              refine ⟨14647158549860334219511181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764772366573556146340787 14647158549860334219511181)
              ·
                refine ⟨5492684456197625332316693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14647158549860334219511181 5492684456197625332316693)
                ·
                  refine ⟨257469583884263687452345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5492684456197625332316693 257469583884263687452345)
                  ·
                    rfl

theorem cell22_2256391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_2256391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256391 prefixEnd_2256391 := by exact prefixLift 2256391
  have htrace : WordTrace (prefixWord ++ tailWord_2256391) baseStart_2256391 baseEnd_2256391 := by
    simpa [prefixWord, tailWord_2256391, baseEnd_2256391] using wordTrace_append hprefix tailTrace_2256391
  have hstable : (prefixWord ++ tailWord_2256391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256391).length < 2 ^ (prefixWord ++ tailWord_2256391).sum := by decide
  have hdescent : baseEnd_2256391 < baseStart_2256391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256421 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2256421 : Nat := 118140960795 + 2256421 * 2 ^ 59
def prefixEnd_2256421 : Nat := 4983230072969 + 3 ^ 40 * 2256421 * 2
def baseEnd_2256421 : Nat := 772419021265880984106943

theorem tailTrace_2256421 : CollatzResearch.WordTrace tailWord_2256421 prefixEnd_2256421 772419021265880984106943 := by
  unfold tailWord_2256421
  simp only [CollatzResearch.WordTrace]
  refine ⟨82298434958379557871353117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54865623305586371914235411 82298434958379557871353117)
  ·
    refine ⟨30861913109392334201757419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82298434958379557871353117 30861913109392334201757419)
    ·
      refine ⟨46292869664088501302636129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30861913109392334201757419 46292869664088501302636129)
      ·
        refine ⟨34719652248066375976977097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46292869664088501302636129 34719652248066375976977097)
        ·
          refine ⟨26039739186049781982732823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34719652248066375976977097 26039739186049781982732823)
          ·
            refine ⟨39059608779074672974099235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26039739186049781982732823 39059608779074672974099235)
            ·
              refine ⟨58589413168612009461148853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39059608779074672974099235 58589413168612009461148853)
              ·
                refine ⟨5492757484557375886982705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58589413168612009461148853 5492757484557375886982705)
                ·
                  refine ⟨4119568113418031915237029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5492757484557375886982705 4119568113418031915237029)
                  ·
                    refine ⟨772419021265880984106943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4119568113418031915237029 772419021265880984106943)
                    ·
                      rfl

theorem cell22_2256421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2256421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256421 prefixEnd_2256421 := by exact prefixLift 2256421
  have htrace : WordTrace (prefixWord ++ tailWord_2256421) baseStart_2256421 baseEnd_2256421 := by
    simpa [prefixWord, tailWord_2256421, baseEnd_2256421] using wordTrace_append hprefix tailTrace_2256421
  have hstable : (prefixWord ++ tailWord_2256421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256421).length < 2 ^ (prefixWord ++ tailWord_2256421).sum := by decide
  have hdescent : baseEnd_2256421 < baseStart_2256421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256468 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2256468 : Nat := 118140960795 + 2256468 * 2 ^ 59
def prefixEnd_2256468 : Nat := 4983230072969 + 3 ^ 40 * 2256468 * 2
def baseEnd_2256468 : Nat := 772435110326388528181799

theorem tailTrace_2256468 : CollatzResearch.WordTrace tailWord_2256468 prefixEnd_2256468 772435110326388528181799 := by
  unfold tailWord_2256468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41150074594604642449157029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54866766126139523265542705 41150074594604642449157029)
  ·
    refine ⟨7715638986488370459216943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41150074594604642449157029 7715638986488370459216943)
    ·
      refine ⟨11573458479732555688825415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7715638986488370459216943 11573458479732555688825415)
      ·
        refine ⟨17360187719598833533238123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11573458479732555688825415 17360187719598833533238123)
        ·
          refine ⟨26040281579398250299857185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17360187719598833533238123 26040281579398250299857185)
          ·
            refine ⟨19530211184548687724892889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26040281579398250299857185 19530211184548687724892889)
            ·
              refine ⟨14647658388411515793669667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19530211184548687724892889 14647658388411515793669667)
              ·
                refine ⟨21971487582617273690504501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14647658388411515793669667 21971487582617273690504501)
                ·
                  refine ⟨2059826960870369408484797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21971487582617273690504501 2059826960870369408484797)
                  ·
                    refine ⟨772435110326388528181799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059826960870369408484797 772435110326388528181799)
                    ·
                      rfl

theorem cell22_2256468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2256468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256468 prefixEnd_2256468 := by exact prefixLift 2256468
  have htrace : WordTrace (prefixWord ++ tailWord_2256468) baseStart_2256468 baseEnd_2256468 := by
    simpa [prefixWord, tailWord_2256468, baseEnd_2256468] using wordTrace_append hprefix tailTrace_2256468
  have hstable : (prefixWord ++ tailWord_2256468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256468).length < 2 ^ (prefixWord ++ tailWord_2256468).sum := by decide
  have hdescent : baseEnd_2256468 < baseStart_2256468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256498 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2256498 : Nat := 118140960795 + 2256498 * 2 ^ 59
def prefixEnd_2256498 : Nat := 4983230072969 + 3 ^ 40 * 2256498 * 2
def baseEnd_2256498 : Nat := 257481793313159483310569

theorem tailTrace_2256498 : CollatzResearch.WordTrace tailWord_2256498 prefixEnd_2256498 257481793313159483310569 := by
  unfold tailWord_2256498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20575310844775150005476537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54867495586067066681270765 20575310844775150005476537)
  ·
    refine ⟨15431483133581362504107403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20575310844775150005476537 15431483133581362504107403)
    ·
      refine ⟨23147224700372043756161105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15431483133581362504107403 23147224700372043756161105)
      ·
        refine ⟨17360418525279032817120829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23147224700372043756161105 17360418525279032817120829)
        ·
          refine ⟨6510156946979637306420311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17360418525279032817120829 6510156946979637306420311)
          ·
            refine ⟨9765235420469455959630467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6510156946979637306420311 9765235420469455959630467)
            ·
              refine ⟨14647853130704183939445701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9765235420469455959630467 14647853130704183939445701)
              ·
                refine ⟨2746472462007034488646069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14647853130704183939445701 2746472462007034488646069)
                ·
                  refine ⟨257481793313159483310569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2746472462007034488646069 257481793313159483310569)
                  ·
                    rfl

theorem cell22_2256498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2256498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256498 prefixEnd_2256498 := by exact prefixLift 2256498
  have htrace : WordTrace (prefixWord ++ tailWord_2256498) baseStart_2256498 baseEnd_2256498 := by
    simpa [prefixWord, tailWord_2256498, baseEnd_2256498] using wordTrace_append hprefix tailTrace_2256498
  have hstable : (prefixWord ++ tailWord_2256498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256498).length < 2 ^ (prefixWord ++ tailWord_2256498).sum := by decide
  have hdescent : baseEnd_2256498 < baseStart_2256498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256513 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2256513 : Nat := 118140960795 + 2256513 * 2 ^ 59
def prefixEnd_2256513 : Nat := 4983230072969 + 3 ^ 40 * 2256513 * 2
def baseEnd_2256513 : Nat := 772450514746023410806661

theorem tailTrace_2256513 : CollatzResearch.WordTrace tailWord_2256513 prefixEnd_2256513 772450514746023410806661 := by
  unfold tailWord_2256513
  simp only [CollatzResearch.WordTrace]
  refine ⟨82301790474046257583702193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54867860316030838389134795 82301790474046257583702193)
  ·
    refine ⟨61726342855534693187776645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82301790474046257583702193 61726342855534693187776645)
    ·
      refine ⟨11573689285412754972708121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61726342855534693187776645 11573689285412754972708121)
      ·
        refine ⟨8680266964059566229531091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11573689285412754972708121 8680266964059566229531091)
        ·
          refine ⟨13020400446089349344296637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680266964059566229531091 13020400446089349344296637)
          ·
            refine ⟨4882650167283506004111239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13020400446089349344296637 4882650167283506004111239)
            ·
              refine ⟨7323975250925259006166859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882650167283506004111239 7323975250925259006166859)
              ·
                refine ⟨10985962876387888509250289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7323975250925259006166859 10985962876387888509250289)
                ·
                  refine ⟨8239472157290916381937717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10985962876387888509250289 8239472157290916381937717)
                  ·
                    refine ⟨772450514746023410806661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8239472157290916381937717 772450514746023410806661)
                    ·
                      rfl

theorem cell22_2256513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2256513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256513 prefixEnd_2256513 := by exact prefixLift 2256513
  have htrace : WordTrace (prefixWord ++ tailWord_2256513) baseStart_2256513 baseEnd_2256513 := by
    simpa [prefixWord, tailWord_2256513, baseEnd_2256513] using wordTrace_append hprefix tailTrace_2256513
  have hstable : (prefixWord ++ tailWord_2256513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256513).length < 2 ^ (prefixWord ++ tailWord_2256513).sum := by decide
  have hdescent : baseEnd_2256513 < baseStart_2256513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256545 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2256545 : Nat := 118140960795 + 2256545 * 2 ^ 59
def prefixEnd_2256545 : Nat := 4983230072969 + 3 ^ 40 * 2256545 * 2
def baseEnd_2256545 : Nat := 772461468999985994006563

theorem tailTrace_2256545 : CollatzResearch.WordTrace tailWord_2256545 prefixEnd_2256545 772461468999985994006563 := by
  unfold tailWord_2256545
  simp only [CollatzResearch.WordTrace]
  refine ⟨82302957609930327048867089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54868638406620218032578059 82302957609930327048867089)
  ·
    refine ⟨61727218207447745286650317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82302957609930327048867089 61727218207447745286650317)
    ·
      refine ⟨23147706827792904482493869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61727218207447745286650317 23147706827792904482493869)
      ·
        refine ⟨8680390060422339180935201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23147706827792904482493869 8680390060422339180935201)
        ·
          refine ⟨6510292545316754385701401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8680390060422339180935201 6510292545316754385701401)
          ·
            refine ⟨4882719408987565789276051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6510292545316754385701401 4882719408987565789276051)
            ·
              refine ⟨7324079113481348683914077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4882719408987565789276051 7324079113481348683914077)
              ·
                refine ⟨2746529667555505756467779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7324079113481348683914077 2746529667555505756467779)
                ·
                  refine ⟨4119794501333258634701669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2746529667555505756467779 4119794501333258634701669)
                  ·
                    refine ⟨772461468999985994006563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4119794501333258634701669 772461468999985994006563)
                    ·
                      rfl

theorem cell22_2256545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2256545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256545 prefixEnd_2256545 := by exact prefixLift 2256545
  have htrace : WordTrace (prefixWord ++ tailWord_2256545) baseStart_2256545 baseEnd_2256545 := by
    simpa [prefixWord, tailWord_2256545, baseEnd_2256545] using wordTrace_append hprefix tailTrace_2256545
  have hstable : (prefixWord ++ tailWord_2256545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256545).length < 2 ^ (prefixWord ++ tailWord_2256545).sum := by decide
  have hdescent : baseEnd_2256545 < baseStart_2256545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256620 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_2256620 : Nat := 118140960795 + 2256620 * 2 ^ 59
def prefixEnd_2256620 : Nat := 4983230072969 + 3 ^ 40 * 2256620 * 2
def baseEnd_2256620 : Nat := 772487143032710798381333

theorem tailTrace_2256620 : CollatzResearch.WordTrace tailWord_2256620 prefixEnd_2256620 772487143032710798381333 := by
  unfold tailWord_2256620
  simp only [CollatzResearch.WordTrace]
  refine ⟨41152846542329307428923657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54870462056439076571898209 41152846542329307428923657)
  ·
    refine ⟨30864634906746980571692743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41152846542329307428923657 30864634906746980571692743)
    ·
      refine ⟨46296952360120470857539115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30864634906746980571692743 46296952360120470857539115)
      ·
        refine ⟨69445428540180706286308673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46296952360120470857539115 69445428540180706286308673)
        ·
          refine ⟨52084071405135529714731505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69445428540180706286308673 52084071405135529714731505)
          ·
            refine ⟨39063053553851647286048629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52084071405135529714731505 39063053553851647286048629)
            ·
              refine ⟨3662161270673591933067059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39063053553851647286048629 3662161270673591933067059)
              ·
                refine ⟨5493241906010387899600589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662161270673591933067059 5493241906010387899600589)
                ·
                  refine ⟨2059965714753895462350221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5493241906010387899600589 2059965714753895462350221)
                  ·
                    refine ⟨772487143032710798381333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2059965714753895462350221 772487143032710798381333)
                    ·
                      rfl

theorem cell22_2256620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_2256620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256620 prefixEnd_2256620 := by exact prefixLift 2256620
  have htrace : WordTrace (prefixWord ++ tailWord_2256620) baseStart_2256620 baseEnd_2256620 := by
    simpa [prefixWord, tailWord_2256620, baseEnd_2256620] using wordTrace_append hprefix tailTrace_2256620
  have hstable : (prefixWord ++ tailWord_2256620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256620).length < 2 ^ (prefixWord ++ tailWord_2256620).sum := by decide
  have hdescent : baseEnd_2256620 < baseStart_2256620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256680 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2256680 : Nat := 118140960795 + 2256680 * 2 ^ 59
def prefixEnd_2256680 : Nat := 4983230072969 + 3 ^ 40 * 2256680 * 2
def baseEnd_2256680 : Nat := 772507682258890641881149

theorem tailTrace_2256680 : CollatzResearch.WordTrace tailWord_2256680 prefixEnd_2256680 772507682258890641881149 := by
  unfold tailWord_2256680
  simp only [CollatzResearch.WordTrace]
  refine ⟨41153940732220622552515747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54871920976294163403354329 41153940732220622552515747)
  ·
    refine ⟨61730911098330933828773621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41153940732220622552515747 61730911098330933828773621)
    ·
      refine ⟨5787272915468525046447527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61730911098330933828773621 5787272915468525046447527)
      ·
        refine ⟨8680909373202787569671291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787272915468525046447527 8680909373202787569671291)
        ·
          refine ⟨13021364059804181354506937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8680909373202787569671291 13021364059804181354506937)
          ·
            refine ⟨9766023044853136015880203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13021364059804181354506937 9766023044853136015880203)
            ·
              refine ⟨14649034567279704023820305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9766023044853136015880203 14649034567279704023820305)
              ·
                refine ⟨10986775925459778017865229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14649034567279704023820305 10986775925459778017865229)
                ·
                  refine ⟨4120040972047416756699461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10986775925459778017865229 4120040972047416756699461)
                  ·
                    refine ⟨772507682258890641881149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120040972047416756699461 772507682258890641881149)
                    ·
                      rfl

theorem cell22_2256680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2256680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256680 prefixEnd_2256680 := by exact prefixLift 2256680
  have htrace : WordTrace (prefixWord ++ tailWord_2256680) baseStart_2256680 baseEnd_2256680 := by
    simpa [prefixWord, tailWord_2256680, baseEnd_2256680] using wordTrace_append hprefix tailTrace_2256680
  have hstable : (prefixWord ++ tailWord_2256680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256680).length < 2 ^ (prefixWord ++ tailWord_2256680).sum := by decide
  have hdescent : baseEnd_2256680 < baseStart_2256680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256712 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_2256712 : Nat := 118140960795 + 2256712 * 2 ^ 59
def prefixEnd_2256712 : Nat := 4983230072969 + 3 ^ 40 * 2256712 * 2
def baseEnd_2256712 : Nat := 257506212170951075027017

theorem tailTrace_2256712 : CollatzResearch.WordTrace tailWord_2256712 prefixEnd_2256712 257506212170951075027017 := by
  unfold tailWord_2256712
  simp only [CollatzResearch.WordTrace]
  refine ⟨41154524300162657285098195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54872699066883543046797593 41154524300162657285098195)
  ·
    refine ⟨61731786450243985927647293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41154524300162657285098195 61731786450243985927647293)
    ·
      refine ⟨23149419918841494722867735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61731786450243985927647293 23149419918841494722867735)
      ·
        refine ⟨34724129878262242084301603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23149419918841494722867735 34724129878262242084301603)
        ·
          refine ⟨52086194817393363126452405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34724129878262242084301603 52086194817393363126452405)
          ·
            refine ⟨4883080764130627793104913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52086194817393363126452405 4883080764130627793104913)
            ·
              refine ⟨3662310573097970844828685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4883080764130627793104913 3662310573097970844828685)
              ·
                refine ⟨1373366464911739066810757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3662310573097970844828685 1373366464911739066810757)
                ·
                  refine ⟨257506212170951075027017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373366464911739066810757 257506212170951075027017)
                  ·
                    rfl

theorem cell22_2256712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_2256712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256712 prefixEnd_2256712 := by exact prefixLift 2256712
  have htrace : WordTrace (prefixWord ++ tailWord_2256712) baseStart_2256712 baseEnd_2256712 := by
    simpa [prefixWord, tailWord_2256712, baseEnd_2256712] using wordTrace_append hprefix tailTrace_2256712
  have hstable : (prefixWord ++ tailWord_2256712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256712).length < 2 ^ (prefixWord ++ tailWord_2256712).sum := by decide
  have hdescent : baseEnd_2256712 < baseStart_2256712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256727 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2256727 : Nat := 118140960795 + 2256727 * 2 ^ 59
def prefixEnd_2256727 : Nat := 4983230072969 + 3 ^ 40 * 2256727 * 2
def baseEnd_2256727 : Nat := 772523771319398185956005

theorem tailTrace_2256727 : CollatzResearch.WordTrace tailWord_2256727 prefixEnd_2256727 772523771319398185956005 := by
  unfold tailWord_2256727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82309595695270972131992435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54873063796847314754661623 82309595695270972131992435)
  ·
    refine ⟨123464393542906458197988653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82309595695270972131992435 123464393542906458197988653)
    ·
      refine ⟨46299147578589921824245745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123464393542906458197988653 46299147578589921824245745)
      ·
        refine ⟨34724360683942441368184309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46299147578589921824245745 34724360683942441368184309)
        ·
          refine ⟨3255408814119603878267279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34724360683942441368184309 3255408814119603878267279)
          ·
            refine ⟨4883113221179405817400919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3255408814119603878267279 4883113221179405817400919)
            ·
              refine ⟨7324669831769108726101379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4883113221179405817400919 7324669831769108726101379)
              ·
                refine ⟨10987004747653663089152069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7324669831769108726101379 10987004747653663089152069)
                ·
                  refine ⟨2060063390185061829216013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10987004747653663089152069 2060063390185061829216013)
                  ·
                    refine ⟨772523771319398185956005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060063390185061829216013 772523771319398185956005)
                    ·
                      rfl

theorem cell22_2256727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2256727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256727 prefixEnd_2256727 := by exact prefixLift 2256727
  have htrace : WordTrace (prefixWord ++ tailWord_2256727) baseStart_2256727 baseEnd_2256727 := by
    simpa [prefixWord, tailWord_2256727, baseEnd_2256727] using wordTrace_append hprefix tailTrace_2256727
  have hstable : (prefixWord ++ tailWord_2256727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256727).length < 2 ^ (prefixWord ++ tailWord_2256727).sum := by decide
  have hdescent : baseEnd_2256727 < baseStart_2256727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256744 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2256744 : Nat := 118140960795 + 2256744 * 2 ^ 59
def prefixEnd_2256744 : Nat := 4983230072969 + 3 ^ 40 * 2256744 * 2
def baseEnd_2256744 : Nat := 772529590766815808280953

theorem tailTrace_2256744 : CollatzResearch.WordTrace tailWord_2256744 prefixEnd_2256744 772529590766815808280953 := by
  unfold tailWord_2256744
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155107868104692017680643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54873477157472922690240857 41155107868104692017680643)
  ·
    refine ⟨61732661802157038026520965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41155107868104692017680643 61732661802157038026520965)
    ·
      refine ⟨11574874087904444629972681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61732661802157038026520965 11574874087904444629972681)
      ·
        refine ⟨8681155565928333472479511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11574874087904444629972681 8681155565928333472479511)
        ·
          refine ⟨13021733348892500208719267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8681155565928333472479511 13021733348892500208719267)
          ·
            refine ⟨19532600023338750313078901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13021733348892500208719267 19532600023338750313078901)
            ·
              refine ⟨1831181252188007841851147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19532600023338750313078901 1831181252188007841851147)
              ·
                refine ⟨2746771878282011762776721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831181252188007841851147 2746771878282011762776721)
                ·
                  refine ⟨2060078908711508822082541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2746771878282011762776721 2060078908711508822082541)
                  ·
                    refine ⟨772529590766815808280953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060078908711508822082541 772529590766815808280953)
                    ·
                      rfl

theorem cell22_2256744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2256744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256744 prefixEnd_2256744 := by exact prefixLift 2256744
  have htrace : WordTrace (prefixWord ++ tailWord_2256744) baseStart_2256744 baseEnd_2256744 := by
    simpa [prefixWord, tailWord_2256744, baseEnd_2256744] using wordTrace_append hprefix tailTrace_2256744
  have hstable : (prefixWord ++ tailWord_2256744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256744).length < 2 ^ (prefixWord ++ tailWord_2256744).sum := by decide
  have hdescent : baseEnd_2256744 < baseStart_2256744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256768 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_2256768 : Nat := 118140960795 + 2256768 * 2 ^ 59
def prefixEnd_2256768 : Nat := 4983230072969 + 3 ^ 40 * 2256768 * 2
def baseEnd_2256768 : Nat := 257512602152429248560293

theorem tailTrace_2256768 : CollatzResearch.WordTrace tailWord_2256768 prefixEnd_2256768 257512602152429248560293 := by
  unfold tailWord_2256768
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155545544061218067117479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54874060725414957422823305 41155545544061218067117479)
  ·
    refine ⟨61733318316091827100676219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41155545544061218067117479 61733318316091827100676219)
    ·
      refine ⟨92599977474137740651014329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61733318316091827100676219 92599977474137740651014329)
      ·
        refine ⟨69449983105603305488260747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92599977474137740651014329 69449983105603305488260747)
        ·
          refine ⟨104174974658404958232391121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69449983105603305488260747 104174974658404958232391121)
          ·
            refine ⟨78131230993803718674293341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104174974658404958232391121 78131230993803718674293341)
            ·
              refine ⟨29299211622676394502860003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78131230993803718674293341 29299211622676394502860003)
              ·
                refine ⟨43948817434014591754290005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29299211622676394502860003 43948817434014591754290005)
                ·
                  refine ⟨257512602152429248560293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43948817434014591754290005 257512602152429248560293)
                  ·
                    rfl

theorem cell22_2256768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_2256768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256768 prefixEnd_2256768 := by exact prefixLift 2256768
  have htrace : WordTrace (prefixWord ++ tailWord_2256768) baseStart_2256768 baseEnd_2256768 := by
    simpa [prefixWord, tailWord_2256768, baseEnd_2256768] using wordTrace_append hprefix tailTrace_2256768
  have hstable : (prefixWord ++ tailWord_2256768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256768).length < 2 ^ (prefixWord ++ tailWord_2256768).sum := by decide
  have hdescent : baseEnd_2256768 < baseStart_2256768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256815 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_2256815 : Nat := 118140960795 + 2256815 * 2 ^ 59
def prefixEnd_2256815 : Nat := 4983230072969 + 3 ^ 40 * 2256815 * 2
def baseEnd_2256815 : Nat := 772553895517795289755735

theorem tailTrace_2256815 : CollatzResearch.WordTrace tailWord_2256815 prefixEnd_2256815 772553895517795289755735 := by
  unfold tailWord_2256815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82312805318952163161195899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54875203545968108774130599 82312805318952163161195899)
  ·
    refine ⟨123469207978428244741793849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82312805318952163161195899 123469207978428244741793849)
    ·
      refine ⟨92601905983821183556345387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123469207978428244741793849 92601905983821183556345387)
      ·
        refine ⟨138902858975731775334518081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92601905983821183556345387 138902858975731775334518081)
        ·
          refine ⟨104177144231798831500888561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138902858975731775334518081 104177144231798831500888561)
          ·
            refine ⟨78132858173849123625666421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104177144231798831500888561 78132858173849123625666421)
            ·
              refine ⟨7324955453798355339906227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78132858173849123625666421 7324955453798355339906227)
              ·
                refine ⟨10987433180697533009859341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7324955453798355339906227 10987433180697533009859341)
                ·
                  refine ⟨4120287442761574878697253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10987433180697533009859341 4120287442761574878697253)
                  ·
                    refine ⟨772553895517795289755735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120287442761574878697253 772553895517795289755735)
                    ·
                      rfl

theorem cell22_2256815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_2256815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256815 prefixEnd_2256815 := by exact prefixLift 2256815
  have htrace : WordTrace (prefixWord ++ tailWord_2256815) baseStart_2256815 baseEnd_2256815 := by
    simpa [prefixWord, tailWord_2256815, baseEnd_2256815] using wordTrace_append hprefix tailTrace_2256815
  have hstable : (prefixWord ++ tailWord_2256815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256815).length < 2 ^ (prefixWord ++ tailWord_2256815).sum := by decide
  have hdescent : baseEnd_2256815 < baseStart_2256815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256847 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 4]
def baseStart_2256847 : Nat := 118140960795 + 2256847 * 2 ^ 59
def prefixEnd_2256847 : Nat := 4983230072969 + 3 ^ 40 * 2256847 * 2
def baseEnd_2256847 : Nat := 257521616590585957651879

theorem tailTrace_2256847 : CollatzResearch.WordTrace tailWord_2256847 prefixEnd_2256847 257521616590585957651879 := by
  unfold tailWord_2256847
  simp only [CollatzResearch.WordTrace]
  refine ⟨82313972454836232626360795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54875981636557488417573863 82313972454836232626360795)
  ·
    refine ⟨123470958682254348939541193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82313972454836232626360795 123470958682254348939541193)
    ·
      refine ⟨92603219011690761704655895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123470958682254348939541193 92603219011690761704655895)
      ·
        refine ⟨138904828517536142556983843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92603219011690761704655895 138904828517536142556983843)
        ·
          refine ⟨208357242776304213835475765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138904828517536142556983843 208357242776304213835475765)
          ·
            refine ⟨19533491510278520047075853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208357242776304213835475765 19533491510278520047075853)
            ·
              refine ⟨7325059316354445017653445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19533491510278520047075853 7325059316354445017653445)
              ·
                refine ⟨1373448621816458440810021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7325059316354445017653445 1373448621816458440810021)
                ·
                  refine ⟨257521616590585957651879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373448621816458440810021 257521616590585957651879)
                  ·
                    rfl

theorem cell22_2256847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 4].length) (baseStart_2256847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256847 prefixEnd_2256847 := by exact prefixLift 2256847
  have htrace : WordTrace (prefixWord ++ tailWord_2256847) baseStart_2256847 baseEnd_2256847 := by
    simpa [prefixWord, tailWord_2256847, baseEnd_2256847] using wordTrace_append hprefix tailTrace_2256847
  have hstable : (prefixWord ++ tailWord_2256847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256847).length < 2 ^ (prefixWord ++ tailWord_2256847).sum := by decide
  have hdescent : baseEnd_2256847 < baseStart_2256847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256924 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2256924 : Nat := 118140960795 + 2256924 * 2 ^ 59
def prefixEnd_2256924 : Nat := 4983230072969 + 3 ^ 40 * 2256924 * 2
def baseEnd_2256924 : Nat := 772591208445355338780401

theorem tailTrace_2256924 : CollatzResearch.WordTrace tailWord_2256924 prefixEnd_2256924 772591208445355338780401 := by
  unfold tailWord_2256924
  simp only [CollatzResearch.WordTrace]
  refine ⟨41158390437778637388456913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54877853917038183184609217 41158390437778637388456913)
  ·
    refine ⟨30868792828333978041342685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41158390437778637388456913 30868792828333978041342685)
    ·
      refine ⟨11575797310625241765503507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30868792828333978041342685 11575797310625241765503507)
      ·
        refine ⟨17363695965937862648255261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11575797310625241765503507 17363695965937862648255261)
        ·
          refine ⟨6511385987226698493095723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17363695965937862648255261 6511385987226698493095723)
          ·
            refine ⟨9767078980840047739643585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511385987226698493095723 9767078980840047739643585)
            ·
              refine ⟨7325309235630035804732689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9767078980840047739643585 7325309235630035804732689)
              ·
                refine ⟨5493981926722526853549517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7325309235630035804732689 5493981926722526853549517)
                ·
                  refine ⟨2060243222520947570081069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5493981926722526853549517 2060243222520947570081069)
                  ·
                    refine ⟨772591208445355338780401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060243222520947570081069 772591208445355338780401)
                    ·
                      rfl

theorem cell22_2256924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2256924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256924 prefixEnd_2256924 := by exact prefixLift 2256924
  have htrace : WordTrace (prefixWord ++ tailWord_2256924) baseStart_2256924 baseEnd_2256924 := by
    simpa [prefixWord, tailWord_2256924, baseEnd_2256924] using wordTrace_append hprefix tailTrace_2256924
  have hstable : (prefixWord ++ tailWord_2256924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256924).length < 2 ^ (prefixWord ++ tailWord_2256924).sum := by decide
  have hdescent : baseEnd_2256924 < baseStart_2256924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256958 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2256958 : Nat := 118140960795 + 2256958 * 2 ^ 59
def prefixEnd_2256958 : Nat := 4983230072969 + 3 ^ 40 * 2256958 * 2
def baseEnd_2256958 : Nat := 772602847340190583430297

theorem tailTrace_2256958 : CollatzResearch.WordTrace tailWord_2256958 prefixEnd_2256958 772602847340190583430297 := by
  unfold tailWord_2256958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289752619679262322956441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54878680638289399055767685 10289752619679262322956441)
  ·
    refine ⟨7717314464759446742217331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10289752619679262322956441 7717314464759446742217331)
    ·
      refine ⟨11575971697139170113325997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7717314464759446742217331 11575971697139170113325997)
      ·
        refine ⟨4340989386427188792497249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11575971697139170113325997 4340989386427188792497249)
        ·
          refine ⟨3255742039820391594372937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4340989386427188792497249 3255742039820391594372937)
          ·
            refine ⟨2441806529865293695779703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3255742039820391594372937 2441806529865293695779703)
            ·
              refine ⟨3662709794797940543669555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441806529865293695779703 3662709794797940543669555)
              ·
                refine ⟨5494064692196910815504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662709794797940543669555 5494064692196910815504333)
                ·
                  refine ⟨2060274259573841555814125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5494064692196910815504333 2060274259573841555814125)
                  ·
                    refine ⟨772602847340190583430297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060274259573841555814125 772602847340190583430297)
                    ·
                      rfl

theorem cell22_2256958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2256958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256958 prefixEnd_2256958 := by exact prefixLift 2256958
  have htrace : WordTrace (prefixWord ++ tailWord_2256958) baseStart_2256958 baseEnd_2256958 := by
    simpa [prefixWord, tailWord_2256958, baseEnd_2256958] using wordTrace_append hprefix tailTrace_2256958
  have hstable : (prefixWord ++ tailWord_2256958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256958).length < 2 ^ (prefixWord ++ tailWord_2256958).sum := by decide
  have hdescent : baseEnd_2256958 < baseStart_2256958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256967 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2256967 : Nat := 118140960795 + 2256967 * 2 ^ 59
def prefixEnd_2256967 : Nat := 4983230072969 + 3 ^ 40 * 2256967 * 2
def baseEnd_2256967 : Nat := 772605928224117559955269

theorem tailTrace_2256967 : CollatzResearch.WordTrace tailWord_2256967 prefixEnd_2256967 772605928224117559955269 := by
  unfold tailWord_2256967
  simp only [CollatzResearch.WordTrace]
  refine ⟨82318349214401493120729155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54878899476267662080486103 82318349214401493120729155)
  ·
    refine ⟨123477523821602239681093733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82318349214401493120729155 123477523821602239681093733)
    ·
      refine ⟨23152035716550419940205075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123477523821602239681093733 23152035716550419940205075)
      ·
        refine ⟨34728053574825629910307613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23152035716550419940205075 34728053574825629910307613)
        ·
          refine ⟨13023020090559611216365355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34728053574825629910307613 13023020090559611216365355)
          ·
            refine ⟨19534530135839416824548033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13023020090559611216365355 19534530135839416824548033)
            ·
              refine ⟨14650897601879562618411025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19534530135839416824548033 14650897601879562618411025)
              ·
                refine ⟨10988173201409671963808269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14650897601879562618411025 10988173201409671963808269)
                ·
                  refine ⟨4120564950528626986428101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10988173201409671963808269 4120564950528626986428101)
                  ·
                    refine ⟨772605928224117559955269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120564950528626986428101 772605928224117559955269)
                    ·
                      rfl

theorem cell22_2256967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2256967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256967 prefixEnd_2256967 := by exact prefixLift 2256967
  have htrace : WordTrace (prefixWord ++ tailWord_2256967) baseStart_2256967 baseEnd_2256967 := by
    simpa [prefixWord, tailWord_2256967, baseEnd_2256967] using wordTrace_append hprefix tailTrace_2256967
  have hstable : (prefixWord ++ tailWord_2256967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256967).length < 2 ^ (prefixWord ++ tailWord_2256967).sum := by decide
  have hdescent : baseEnd_2256967 < baseStart_2256967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256984 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_2256984 : Nat := 118140960795 + 2256984 * 2 ^ 59
def prefixEnd_2256984 : Nat := 4983230072969 + 3 ^ 40 * 2256984 * 2
def baseEnd_2256984 : Nat := 772611747671535182280217

theorem tailTrace_2256984 : CollatzResearch.WordTrace tailWord_2256984 prefixEnd_2256984 772611747671535182280217 := by
  unfold tailWord_2256984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41159484627669952512049003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54879312836893270016065337 41159484627669952512049003)
  ·
    refine ⟨61739226941504928768073505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41159484627669952512049003 61739226941504928768073505)
    ·
      refine ⟨46304420206128696576055129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61739226941504928768073505 46304420206128696576055129)
      ·
        refine ⟨34728315154596522432041347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46304420206128696576055129 34728315154596522432041347)
        ·
          refine ⟨52092472731894783648062021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34728315154596522432041347 52092472731894783648062021)
          ·
            refine ⟨9767338637230271934011629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52092472731894783648062021 9767338637230271934011629)
            ·
              refine ⟨3662751988961351975254361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9767338637230271934011629 3662751988961351975254361)
              ·
                refine ⟨2747063991721013981440771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3662751988961351975254361 2747063991721013981440771)
                ·
                  refine ⟨4120595987581520972161157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2747063991721013981440771 4120595987581520972161157)
                  ·
                    refine ⟨772611747671535182280217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4120595987581520972161157 772611747671535182280217)
                    ·
                      rfl

theorem cell22_2256984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_2256984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256984 prefixEnd_2256984 := by exact prefixLift 2256984
  have htrace : WordTrace (prefixWord ++ tailWord_2256984) baseStart_2256984 baseEnd_2256984 := by
    simpa [prefixWord, tailWord_2256984, baseEnd_2256984] using wordTrace_append hprefix tailTrace_2256984
  have hstable : (prefixWord ++ tailWord_2256984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256984).length < 2 ^ (prefixWord ++ tailWord_2256984).sum := by decide
  have hdescent : baseEnd_2256984 < baseStart_2256984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256997 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2256997 : Nat := 118140960795 + 2256997 * 2 ^ 59
def prefixEnd_2256997 : Nat := 4983230072969 + 3 ^ 40 * 2256997 * 2
def baseEnd_2256997 : Nat := 772616197837207481705177

theorem tailTrace_2256997 : CollatzResearch.WordTrace tailWord_2256997 prefixEnd_2256997 772616197837207481705177 := by
  unfold tailWord_2256997
  simp only [CollatzResearch.WordTrace]
  refine ⟨82319443404292808244321245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54879628936195205496214163 82319443404292808244321245)
  ·
    refine ⟨30869791276609803091620467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82319443404292808244321245 30869791276609803091620467)
    ·
      refine ⟨46304686914914704637430701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30869791276609803091620467 46304686914914704637430701)
      ·
        refine ⟨17364257593093014239036513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46304686914914704637430701 17364257593093014239036513)
        ·
          refine ⟨13023193194819760679277385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17364257593093014239036513 13023193194819760679277385)
          ·
            refine ⟨9767394896114820509458039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13023193194819760679277385 9767394896114820509458039)
            ·
              refine ⟨14651092344172230764187059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9767394896114820509458039 14651092344172230764187059)
              ·
                refine ⟨21976638516258346146280589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14651092344172230764187059 21976638516258346146280589)
                ·
                  refine ⟨8241239443596879804855221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21976638516258346146280589 8241239443596879804855221)
                  ·
                    refine ⟨772616197837207481705177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8241239443596879804855221 772616197837207481705177)
                    ·
                      rfl

theorem cell22_2256997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2256997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256997 prefixEnd_2256997 := by exact prefixLift 2256997
  have htrace : WordTrace (prefixWord ++ tailWord_2256997) baseStart_2256997 baseEnd_2256997 := by
    simpa [prefixWord, tailWord_2256997, baseEnd_2256997] using wordTrace_append hprefix tailTrace_2256997
  have hstable : (prefixWord ++ tailWord_2256997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256997).length < 2 ^ (prefixWord ++ tailWord_2256997).sum := by decide
  have hdescent : baseEnd_2256997 < baseStart_2256997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2256999 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 4]
def baseStart_2256999 : Nat := 118140960795 + 2256999 * 2 ^ 59
def prefixEnd_2256999 : Nat := 4983230072969 + 3 ^ 40 * 2256999 * 2
def baseEnd_2256999 : Nat := 257538960826026714385057

theorem tailTrace_2256999 : CollatzResearch.WordTrace tailWord_2256999 prefixEnd_2256999 257538960826026714385057 := by
  unfold tailWord_2256999
  simp only [CollatzResearch.WordTrace]
  refine ⟨82319516350285562585894051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54879677566857041723929367 82319516350285562585894051)
  ·
    refine ⟨123479274525428343878841077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82319516350285562585894051 123479274525428343878841077)
    ·
      refine ⟨11576181986758907238641351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123479274525428343878841077 11576181986758907238641351)
      ·
        refine ⟨17364272980138360857962027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576181986758907238641351 17364272980138360857962027)
        ·
          refine ⟨26046409470207541286943041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17364272980138360857962027 26046409470207541286943041)
          ·
            refine ⟨19534807102655655965207281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26046409470207541286943041 19534807102655655965207281)
            ·
              refine ⟨14651105326991741973905461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19534807102655655965207281 14651105326991741973905461)
              ·
                refine ⟨1373541124405475810053637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14651105326991741973905461 1373541124405475810053637)
                ·
                  refine ⟨257538960826026714385057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373541124405475810053637 257538960826026714385057)
                  ·
                    rfl

theorem cell22_2256999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 4].length) (baseStart_2256999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2256999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2256999 prefixEnd_2256999 := by exact prefixLift 2256999
  have htrace : WordTrace (prefixWord ++ tailWord_2256999) baseStart_2256999 baseEnd_2256999 := by
    simpa [prefixWord, tailWord_2256999, baseEnd_2256999] using wordTrace_append hprefix tailTrace_2256999
  have hstable : (prefixWord ++ tailWord_2256999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2256999).length < 2 ^ (prefixWord ++ tailWord_2256999).sum := by decide
  have hdescent : baseEnd_2256999 < baseStart_2256999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2256999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257027 : List Nat := [1, 1, 1, 3, 3, 3, 3, 7]
def baseStart_2257027 : Nat := 118140960795 + 2257027 * 2 ^ 59
def prefixEnd_2257027 : Nat := 4983230072969 + 3 ^ 40 * 2257027 * 2
def baseEnd_2257027 : Nat := 85847385272255267050565

theorem tailTrace_2257027 : CollatzResearch.WordTrace tailWord_2257027 prefixEnd_2257027 85847385272255267050565 := by
  unfold tailWord_2257027
  simp only [CollatzResearch.WordTrace]
  refine ⟨82320537594184123367913335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54880358396122748911942223 82320537594184123367913335)
  ·
    refine ⟨123480806391276185051870003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82320537594184123367913335 123480806391276185051870003)
    ·
      refine ⟨185221209586914277577805005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123480806391276185051870003 185221209586914277577805005)
      ·
        refine ⟨69457953595092854091676877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185221209586914277577805005 69457953595092854091676877)
        ·
          refine ⟨26046732598159820284378829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69457953595092854091676877 26046732598159820284378829)
          ·
            refine ⟨9767524724309932606642061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26046732598159820284378829 9767524724309932606642061)
            ·
              refine ⟨3662821771616224727490773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9767524724309932606642061 3662821771616224727490773)
              ·
                refine ⟨85847385272255267050565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3662821771616224727490773 85847385272255267050565)
                ·
                  rfl

theorem cell22_2257027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 7].length) (baseStart_2257027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257027 prefixEnd_2257027 := by exact prefixLift 2257027
  have htrace : WordTrace (prefixWord ++ tailWord_2257027) baseStart_2257027 baseEnd_2257027 := by
    simpa [prefixWord, tailWord_2257027, baseEnd_2257027] using wordTrace_append hprefix tailTrace_2257027
  have hstable : (prefixWord ++ tailWord_2257027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257027).length < 2 ^ (prefixWord ++ tailWord_2257027).sum := by decide
  have hdescent : baseEnd_2257027 < baseStart_2257027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257183 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 2, 3]
def baseStart_2257183 : Nat := 118140960795 + 2257183 * 2 ^ 59
def prefixEnd_2257183 : Nat := 4983230072969 + 3 ^ 40 * 2257183 * 2
def baseEnd_2257183 : Nat := 772679869438364996554607

theorem tailTrace_2257183 : CollatzResearch.WordTrace tailWord_2257183 prefixEnd_2257183 772679869438364996554607 := by
  unfold tailWord_2257183
  simp only [CollatzResearch.WordTrace]
  refine ⟨82326227381618962010592203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54884151587745974673728135 82326227381618962010592203)
  ·
    refine ⟨123489341072428443015888305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82326227381618962010592203 123489341072428443015888305)
    ·
      refine ⟨92617005804321332261916229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123489341072428443015888305 92617005804321332261916229)
      ·
        refine ⟨17365688588310249799109293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92617005804321332261916229 17365688588310249799109293)
        ·
          refine ⟨6512133220616343674665985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17365688588310249799109293 6512133220616343674665985)
          ·
            refine ⟨4884099915462257755999489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6512133220616343674665985 4884099915462257755999489)
            ·
              refine ⟨3663074936596693316999617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4884099915462257755999489 3663074936596693316999617)
              ·
                refine ⟨2747306202447519987749713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3663074936596693316999617 2747306202447519987749713)
                ·
                  refine ⟨2060479651835639990812285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747306202447519987749713 2060479651835639990812285)
                  ·
                    refine ⟨772679869438364996554607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060479651835639990812285 772679869438364996554607)
                    ·
                      rfl

theorem cell22_2257183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_2257183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257183 prefixEnd_2257183 := by exact prefixLift 2257183
  have htrace : WordTrace (prefixWord ++ tailWord_2257183) baseStart_2257183 baseEnd_2257183 := by
    simpa [prefixWord, tailWord_2257183, baseEnd_2257183] using wordTrace_append hprefix tailTrace_2257183
  have hstable : (prefixWord ++ tailWord_2257183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257183).length < 2 ^ (prefixWord ++ tailWord_2257183).sum := by decide
  have hdescent : baseEnd_2257183 < baseStart_2257183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257239 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2257239 : Nat := 118140960795 + 2257239 * 2 ^ 59
def prefixEnd_2257239 : Nat := 4983230072969 + 3 ^ 40 * 2257239 * 2
def baseEnd_2257239 : Nat := 772699039382799517154435

theorem tailTrace_2257239 : CollatzResearch.WordTrace tailWord_2257239 prefixEnd_2257239 772699039382799517154435 := by
  unfold tailWord_2257239
  simp only [CollatzResearch.WordTrace]
  refine ⟨82328269869416083574630771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54885513246277389049753847 82328269869416083574630771)
  ·
    refine ⟨123492404804124125361946157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82328269869416083574630771 123492404804124125361946157)
    ·
      refine ⟨46309651801546547010729809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123492404804124125361946157 46309651801546547010729809)
      ·
        refine ⟨34732238851159910258047357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46309651801546547010729809 34732238851159910258047357)
        ·
          refine ⟨13024589569184966346767759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34732238851159910258047357 13024589569184966346767759)
          ·
            refine ⟨19536884353777449520151639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13024589569184966346767759 19536884353777449520151639)
            ·
              refine ⟨29305326530666174280227459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19536884353777449520151639 29305326530666174280227459)
              ·
                refine ⟨43957989795999261420341189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29305326530666174280227459 43957989795999261420341189)
                ·
                  refine ⟨8242123086749861516313973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43957989795999261420341189 8242123086749861516313973)
                  ·
                    refine ⟨772699039382799517154435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8242123086749861516313973 772699039382799517154435)
                    ·
                      rfl

theorem cell22_2257239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2257239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257239 prefixEnd_2257239 := by exact prefixLift 2257239
  have htrace : WordTrace (prefixWord ++ tailWord_2257239) baseStart_2257239 baseEnd_2257239 := by
    simpa [prefixWord, tailWord_2257239, baseEnd_2257239] using wordTrace_append hprefix tailTrace_2257239
  have hstable : (prefixWord ++ tailWord_2257239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257239).length < 2 ^ (prefixWord ++ tailWord_2257239).sum := by decide
  have hdescent : baseEnd_2257239 < baseStart_2257239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257256 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2257256 : Nat := 118140960795 + 2257256 * 2 ^ 59
def prefixEnd_2257256 : Nat := 4983230072969 + 3 ^ 40 * 2257256 * 2
def baseEnd_2257256 : Nat := 772704858830217139479383

theorem tailTrace_2257256 : CollatzResearch.WordTrace tailWord_2257256 prefixEnd_2257256 772704858830217139479383 := by
  unfold tailWord_2257256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41164444955177247738999811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54885926606902996985333081 41164444955177247738999811)
  ·
    refine ⟨61746667432765871608499717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41164444955177247738999811 61746667432765871608499717)
    ·
      refine ⟨11577500143643600926593697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61746667432765871608499717 11577500143643600926593697)
      ·
        refine ⟨8683125107732700694945273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11577500143643600926593697 8683125107732700694945273)
        ·
          refine ⟨6512343830799525521208955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8683125107732700694945273 6512343830799525521208955)
          ·
            refine ⟨9768515746199288281813433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512343830799525521208955 9768515746199288281813433)
            ·
              refine ⟨7326386809649466211360075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9768515746199288281813433 7326386809649466211360075)
              ·
                refine ⟨10989580214474199317040113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326386809649466211360075 10989580214474199317040113)
                ·
                  refine ⟨8242185160855649487780085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10989580214474199317040113 8242185160855649487780085)
                  ·
                    refine ⟨772704858830217139479383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8242185160855649487780085 772704858830217139479383)
                    ·
                      rfl

theorem cell22_2257256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2257256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257256 prefixEnd_2257256 := by exact prefixLift 2257256
  have htrace : WordTrace (prefixWord ++ tailWord_2257256) baseStart_2257256 baseEnd_2257256 := by
    simpa [prefixWord, tailWord_2257256, baseEnd_2257256] using wordTrace_append hprefix tailTrace_2257256
  have hstable : (prefixWord ++ tailWord_2257256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257256).length < 2 ^ (prefixWord ++ tailWord_2257256).sum := by decide
  have hdescent : baseEnd_2257256 < baseStart_2257256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257322 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2257322 : Nat := 118140960795 + 2257322 * 2 ^ 59
def prefixEnd_2257322 : Nat := 4983230072969 + 3 ^ 40 * 2257322 * 2
def baseEnd_2257322 : Nat := 772727451979014967329181

theorem tailTrace_2257322 : CollatzResearch.WordTrace tailWord_2257322 prefixEnd_2257322 772727451979014967329181 := by
  unfold tailWord_2257322
  simp only [CollatzResearch.WordTrace]
  refine ⟨20582824282028847187475555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54887531418743592499934813 20582824282028847187475555)
  ·
    refine ⟨30874236423043270781213333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20582824282028847187475555 30874236423043270781213333)
    ·
      refine ⟨1447229832330153317869375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30874236423043270781213333 1447229832330153317869375)
      ·
        refine ⟨2170844748495229976804063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447229832330153317869375 2170844748495229976804063)
        ·
          refine ⟨3256267122742844965206095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170844748495229976804063 3256267122742844965206095)
          ·
            refine ⟨4884400684114267447809143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256267122742844965206095 4884400684114267447809143)
            ·
              refine ⟨7326601026171401171713715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884400684114267447809143 7326601026171401171713715)
              ·
                refine ⟨10989901539257101757570573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326601026171401171713715 10989901539257101757570573)
                ·
                  refine ⟨4121213077221413159088965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10989901539257101757570573 4121213077221413159088965)
                  ·
                    refine ⟨772727451979014967329181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121213077221413159088965 772727451979014967329181)
                    ·
                      rfl

theorem cell22_2257322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2257322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257322 prefixEnd_2257322 := by exact prefixLift 2257322
  have htrace : WordTrace (prefixWord ++ tailWord_2257322) baseStart_2257322 baseEnd_2257322 := by
    simpa [prefixWord, tailWord_2257322, baseEnd_2257322] using wordTrace_append hprefix tailTrace_2257322
  have hstable : (prefixWord ++ tailWord_2257322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257322).length < 2 ^ (prefixWord ++ tailWord_2257322).sum := by decide
  have hdescent : baseEnd_2257322 < baseStart_2257322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257348 : List Nat := [2, 3, 3, 2, 3, 9]
def baseStart_2257348 : Nat := 118140960795 + 2257348 * 2 ^ 59
def prefixEnd_2257348 : Nat := 4983230072969 + 3 ^ 40 * 2257348 * 2
def baseEnd_2257348 : Nat := 9539954966794562545421

theorem tailTrace_2257348 : CollatzResearch.WordTrace tailWord_2257348 prefixEnd_2257348 9539954966794562545421 := by
  unfold tailWord_2257348
  simp only [CollatzResearch.WordTrace]
  refine ⟨41166122713010597595174349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54888163617347463460232465 41166122713010597595174349)
  ·
    refine ⟨15437296017378974098190381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41166122713010597595174349 15437296017378974098190381)
    ·
      refine ⟨5788986006517115286821393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15437296017378974098190381 5788986006517115286821393)
      ·
        refine ⟨4341739504887836465116045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5788986006517115286821393 4341739504887836465116045)
        ·
          refine ⟨1628152314332938674418517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4341739504887836465116045 1628152314332938674418517)
          ·
            refine ⟨9539954966794562545421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1628152314332938674418517 9539954966794562545421)
            ·
              rfl

theorem cell22_2257348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 9].length) (baseStart_2257348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257348 prefixEnd_2257348 := by exact prefixLift 2257348
  have htrace : WordTrace (prefixWord ++ tailWord_2257348) baseStart_2257348 baseEnd_2257348 := by
    simpa [prefixWord, tailWord_2257348, baseEnd_2257348] using wordTrace_append hprefix tailTrace_2257348
  have hstable : (prefixWord ++ tailWord_2257348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257348).length < 2 ^ (prefixWord ++ tailWord_2257348).sum := by decide
  have hdescent : baseEnd_2257348 < baseStart_2257348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257376 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_2257376 : Nat := 118140960795 + 2257376 * 2 ^ 59
def prefixEnd_2257376 : Nat := 4983230072969 + 3 ^ 40 * 2257376 * 2
def baseEnd_2257376 : Nat := 257581979094192275493005

theorem tailTrace_2257376 : CollatzResearch.WordTrace tailWord_2257376 prefixEnd_2257376 257581979094192275493005 := by
  unfold tailWord_2257376
  simp only [CollatzResearch.WordTrace]
  refine ⟨41166633334959877986183991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54888844446613170648245321 41166633334959877986183991)
  ·
    refine ⟨61749950002439816979275987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41166633334959877986183991 61749950002439816979275987)
    ·
      refine ⟨92624925003659725468913981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61749950002439816979275987 92624925003659725468913981)
      ·
        refine ⟨34734346876372397050842743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92624925003659725468913981 34734346876372397050842743)
        ·
          refine ⟨52101520314558595576264115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34734346876372397050842743 52101520314558595576264115)
          ·
            refine ⟨78152280471837893364396173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52101520314558595576264115 78152280471837893364396173)
            ·
              refine ⟨29307105176939210011648565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78152280471837893364396173 29307105176939210011648565)
              ·
                refine ⟨2747541110338050938592053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29307105176939210011648565 2747541110338050938592053)
                ·
                  refine ⟨257581979094192275493005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2747541110338050938592053 257581979094192275493005)
                  ·
                    rfl

theorem cell22_2257376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_2257376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257376 prefixEnd_2257376 := by exact prefixLift 2257376
  have htrace : WordTrace (prefixWord ++ tailWord_2257376) baseStart_2257376 baseEnd_2257376 := by
    simpa [prefixWord, tailWord_2257376, baseEnd_2257376] using wordTrace_append hprefix tailTrace_2257376
  have hstable : (prefixWord ++ tailWord_2257376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257376).length < 2 ^ (prefixWord ++ tailWord_2257376).sum := by decide
  have hdescent : baseEnd_2257376 < baseStart_2257376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257410 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2257410 : Nat := 118140960795 + 2257410 * 2 ^ 59
def prefixEnd_2257410 : Nat := 4983230072969 + 3 ^ 40 * 2257410 * 2
def baseEnd_2257410 : Nat := 257585858725804023709637

theorem tailTrace_2257410 : CollatzResearch.WordTrace tailWord_2257410 prefixEnd_2257410 257585858725804023709637 := by
  unfold tailWord_2257410
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583626687949144944776421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54889671167864386519403789 20583626687949144944776421)
  ·
    refine ⟨3859430003990464677145579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20583626687949144944776421 3859430003990464677145579)
    ·
      refine ⟨5789145005985697015718369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3859430003990464677145579 5789145005985697015718369)
      ·
        refine ⟨4341858754489272761788777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5789145005985697015718369 4341858754489272761788777)
        ·
          refine ⟨3256394065866954571341583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4341858754489272761788777 3256394065866954571341583)
          ·
            refine ⟨4884591098800431857012375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256394065866954571341583 4884591098800431857012375)
            ·
              refine ⟨7326886648200647785518563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884591098800431857012375 7326886648200647785518563)
              ·
                refine ⟨10990329972300971678277845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7326886648200647785518563 10990329972300971678277845)
                ·
                  refine ⟨257585858725804023709637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10990329972300971678277845 257585858725804023709637)
                  ·
                    rfl

theorem cell22_2257410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2257410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257410 prefixEnd_2257410 := by exact prefixLift 2257410
  have htrace : WordTrace (prefixWord ++ tailWord_2257410) baseStart_2257410 baseEnd_2257410 := by
    simpa [prefixWord, tailWord_2257410, baseEnd_2257410] using wordTrace_append hprefix tailTrace_2257410
  have hstable : (prefixWord ++ tailWord_2257410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257410).length < 2 ^ (prefixWord ++ tailWord_2257410).sum := by decide
  have hdescent : baseEnd_2257410 < baseStart_2257410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257414 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2257414 : Nat := 118140960795 + 2257414 * 2 ^ 59
def prefixEnd_2257414 : Nat := 4983230072969 + 3 ^ 40 * 2257414 * 2
def baseEnd_2257414 : Nat := 772758945459157394028899

theorem tailTrace_2257414 : CollatzResearch.WordTrace tailWord_2257414 prefixEnd_2257414 772758945459157394028899 := by
  unfold tailWord_2257414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572957895118190264445353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54889768429188058974834197 2572957895118190264445353)
  ·
    refine ⟨1929718421338642698334015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2572957895118190264445353 1929718421338642698334015)
    ·
      refine ⟨2894577632007964047501023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929718421338642698334015 2894577632007964047501023)
      ·
        refine ⟨4341866448011946071251535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894577632007964047501023 4341866448011946071251535)
        ·
          refine ⟨6512799672017919106877303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341866448011946071251535 6512799672017919106877303)
          ·
            refine ⟨9769199508026878660315955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512799672017919106877303 9769199508026878660315955)
            ·
              refine ⟨14653799262040317990473933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769199508026878660315955 14653799262040317990473933)
              ·
                refine ⟨5495174723265119246427725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14653799262040317990473933 5495174723265119246427725)
                ·
                  refine ⟨2060690521224419717410397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5495174723265119246427725 2060690521224419717410397)
                  ·
                    refine ⟨772758945459157394028899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2060690521224419717410397 772758945459157394028899)
                    ·
                      rfl

theorem cell22_2257414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2257414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257414 prefixEnd_2257414 := by exact prefixLift 2257414
  have htrace : WordTrace (prefixWord ++ tailWord_2257414) baseStart_2257414 baseEnd_2257414 := by
    simpa [prefixWord, tailWord_2257414, baseEnd_2257414] using wordTrace_append hprefix tailTrace_2257414
  have hstable : (prefixWord ++ tailWord_2257414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257414).length < 2 ^ (prefixWord ++ tailWord_2257414).sum := by decide
  have hdescent : baseEnd_2257414 < baseStart_2257414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_2257451 : Nat := 118140960795 + 2257451 * 2 ^ 59
def prefixEnd_2257451 : Nat := 4983230072969 + 3 ^ 40 * 2257451 * 2
def baseEnd_2257451 : Nat := 772771611315301630853785

theorem tailTrace_2257451 : CollatzResearch.WordTrace tailWord_2257451 prefixEnd_2257451 772771611315301630853785 := by
  unfold tailWord_2257451
  simp only [CollatzResearch.WordTrace]
  refine ⟨82336002144648043781348207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54890668096432029187565471 82336002144648043781348207)
  ·
    refine ⟨123504003216972065672022311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82336002144648043781348207 123504003216972065672022311)
    ·
      refine ⟨185256004825458098508033467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123504003216972065672022311 185256004825458098508033467)
      ·
        refine ⟨277884007238187147762050201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185256004825458098508033467 277884007238187147762050201)
        ·
          refine ⟨208413005428640360821537651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277884007238187147762050201 208413005428640360821537651)
          ·
            refine ⟨312619508142960541232306477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208413005428640360821537651 312619508142960541232306477)
            ·
              refine ⟨117232315553610202962114929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 312619508142960541232306477 117232315553610202962114929)
              ·
                refine ⟨87924236665207652221586197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117232315553610202962114929 87924236665207652221586197)
                ·
                  refine ⟨4121448593681608697886853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87924236665207652221586197 4121448593681608697886853)
                  ·
                    refine ⟨772771611315301630853785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121448593681608697886853 772771611315301630853785)
                    ·
                      rfl

theorem cell22_2257451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_2257451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257451 prefixEnd_2257451 := by exact prefixLift 2257451
  have htrace : WordTrace (prefixWord ++ tailWord_2257451) baseStart_2257451 baseEnd_2257451 := by
    simpa [prefixWord, tailWord_2257451, baseEnd_2257451] using wordTrace_append hprefix tailTrace_2257451
  have hstable : (prefixWord ++ tailWord_2257451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257451).length < 2 ^ (prefixWord ++ tailWord_2257451).sum := by decide
  have hdescent : baseEnd_2257451 < baseStart_2257451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257466 : List Nat := [3, 1, 1, 1, 3, 3, 10]
def baseStart_2257466 : Nat := 118140960795 + 2257466 * 2 ^ 59
def prefixEnd_2257466 : Nat := 4983230072969 + 3 ^ 40 * 2257466 * 2
def baseEnd_2257466 : Nat := 28621360967475799693657

theorem tailTrace_2257466 : CollatzResearch.WordTrace tailWord_2257466 prefixEnd_2257466 28621360967475799693657 := by
  unfold tailWord_2257466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20584137309898425335786063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54891032826395800895429501 20584137309898425335786063)
  ·
    refine ⟨30876205964847638003679095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20584137309898425335786063 30876205964847638003679095)
    ·
      refine ⟨46314308947271457005518643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30876205964847638003679095 46314308947271457005518643)
      ·
        refine ⟨69471463420907185508277965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46314308947271457005518643 69471463420907185508277965)
        ·
          refine ⟨26051798782840194565604237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69471463420907185508277965 26051798782840194565604237)
          ·
            refine ⟨9769424543565072962101589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26051798782840194565604237 9769424543565072962101589)
            ·
              refine ⟨28621360967475799693657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9769424543565072962101589 28621360967475799693657)
              ·
                rfl

theorem cell22_2257466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 10].length) (baseStart_2257466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257466 prefixEnd_2257466 := by exact prefixLift 2257466
  have htrace : WordTrace (prefixWord ++ tailWord_2257466) baseStart_2257466 baseEnd_2257466 := by
    simpa [prefixWord, tailWord_2257466, baseEnd_2257466] using wordTrace_append hprefix tailTrace_2257466
  have hstable : (prefixWord ++ tailWord_2257466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257466).length < 2 ^ (prefixWord ++ tailWord_2257466).sum := by decide
  have hdescent : baseEnd_2257466 < baseStart_2257466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257468 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2257468 : Nat := 118140960795 + 2257468 * 2 ^ 59
def prefixEnd_2257468 : Nat := 4983230072969 + 3 ^ 40 * 2257468 * 2
def baseEnd_2257468 : Nat := 772777430762719253178733

theorem tailTrace_2257468 : CollatzResearch.WordTrace tailWord_2257468 prefixEnd_2257468 772777430762719253178733 := by
  unfold tailWord_2257468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41168311092793227842358529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54891081457057637123144705 41168311092793227842358529)
  ·
    refine ⟨30876233319594920881768897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41168311092793227842358529 30876233319594920881768897)
    ·
      refine ⟨23157174989696190661326673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30876233319594920881768897 23157174989696190661326673)
      ·
        refine ⟨17367881242272142995995005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23157174989696190661326673 17367881242272142995995005)
        ·
          refine ⟨6512955465852053623498127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17367881242272142995995005 6512955465852053623498127)
          ·
            refine ⟨9769433198778080435247191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6512955465852053623498127 9769433198778080435247191)
            ·
              refine ⟨14654149798167120652870787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9769433198778080435247191 14654149798167120652870787)
              ·
                refine ⟨21981224697250680979306181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14654149798167120652870787 21981224697250680979306181)
                ·
                  refine ⟨4121479630734502683619909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21981224697250680979306181 4121479630734502683619909)
                  ·
                    refine ⟨772777430762719253178733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4121479630734502683619909 772777430762719253178733)
                    ·
                      rfl

theorem cell22_2257468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2257468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257468 prefixEnd_2257468 := by exact prefixLift 2257468
  have htrace : WordTrace (prefixWord ++ tailWord_2257468) baseStart_2257468 baseEnd_2257468 := by
    simpa [prefixWord, tailWord_2257468, baseEnd_2257468] using wordTrace_append hprefix tailTrace_2257468
  have hstable : (prefixWord ++ tailWord_2257468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257468).length < 2 ^ (prefixWord ++ tailWord_2257468).sum := by decide
  have hdescent : baseEnd_2257468 < baseStart_2257468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257543 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2257543 : Nat := 118140960795 + 2257543 * 2 ^ 59
def prefixEnd_2257543 : Nat := 4983230072969 + 3 ^ 40 * 2257543 * 2
def baseEnd_2257543 : Nat := 772803104795444057553503

theorem tailTrace_2257543 : CollatzResearch.WordTrace tailWord_2257543 prefixEnd_2257543 772803104795444057553503 := by
  unfold tailWord_2257543
  simp only [CollatzResearch.WordTrace]
  refine ⟨82339357660314743493697283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54892905106876495662464855 82339357660314743493697283)
  ·
    refine ⟨123509036490472115240545925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82339357660314743493697283 123509036490472115240545925)
    ·
      refine ⟨23157944341963521607602361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123509036490472115240545925 23157944341963521607602361)
      ·
        refine ⟨17368458256472641205701771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23157944341963521607602361 17368458256472641205701771)
        ·
          refine ⟨26052687384708961808552657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17368458256472641205701771 26052687384708961808552657)
          ·
            refine ⟨19539515538531721356414493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26052687384708961808552657 19539515538531721356414493)
            ·
              refine ⟨7327318326949395508655435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19539515538531721356414493 7327318326949395508655435)
              ·
                refine ⟨10990977490424093262983153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7327318326949395508655435 10990977490424093262983153)
                ·
                  refine ⟨8243233117818069947237365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10990977490424093262983153 8243233117818069947237365)
                  ·
                    refine ⟨772803104795444057553503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8243233117818069947237365 772803104795444057553503)
                    ·
                      rfl

theorem cell22_2257543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2257543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257543 prefixEnd_2257543 := by exact prefixLift 2257543
  have htrace : WordTrace (prefixWord ++ tailWord_2257543) baseStart_2257543 baseEnd_2257543 := by
    simpa [prefixWord, tailWord_2257543, baseEnd_2257543] using wordTrace_append hprefix tailTrace_2257543
  have hstable : (prefixWord ++ tailWord_2257543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257543).length < 2 ^ (prefixWord ++ tailWord_2257543).sum := by decide
  have hdescent : baseEnd_2257543 < baseStart_2257543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257635 : List Nat := [1, 1, 1, 7, 1, 3, 8]
def baseStart_2257635 : Nat := 118140960795 + 2257635 * 2 ^ 59
def prefixEnd_2257635 : Nat := 4983230072969 + 3 ^ 40 * 2257635 * 2
def baseEnd_2257635 : Nat := 28623503639836536453823

theorem tailTrace_2257635 : CollatzResearch.WordTrace tailWord_2257635 prefixEnd_2257635 28623503639836536453823 := by
  unfold tailWord_2257635
  simp only [CollatzResearch.WordTrace]
  refine ⟨82342713175981443206046359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54895142117320962137364239 82342713175981443206046359)
  ·
    refine ⟨123514069763972164809069539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82342713175981443206046359 123514069763972164809069539)
    ·
      refine ⟨185271104645958247213604309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123514069763972164809069539 185271104645958247213604309)
      ·
        refine ⟨4342291515139646419068851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 185271104645958247213604309 4342291515139646419068851)
        ·
          refine ⟨6513437272709469628603277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342291515139646419068851 6513437272709469628603277)
          ·
            refine ⟨2442538977266051110726229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6513437272709469628603277 2442538977266051110726229)
            ·
              refine ⟨28623503639836536453823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2442538977266051110726229 28623503639836536453823)
              ·
                rfl

theorem cell22_2257635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 8].length) (baseStart_2257635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257635 prefixEnd_2257635 := by exact prefixLift 2257635
  have htrace : WordTrace (prefixWord ++ tailWord_2257635) baseStart_2257635 baseEnd_2257635 := by
    simpa [prefixWord, tailWord_2257635, baseEnd_2257635] using wordTrace_append hprefix tailTrace_2257635
  have hstable : (prefixWord ++ tailWord_2257635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257635).length < 2 ^ (prefixWord ++ tailWord_2257635).sum := by decide
  have hdescent : baseEnd_2257635 < baseStart_2257635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257648 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_2257648 : Nat := 118140960795 + 2257648 * 2 ^ 59
def prefixEnd_2257648 : Nat := 4983230072969 + 3 ^ 40 * 2257648 * 2
def baseEnd_2257648 : Nat := 772839048441258783678181

theorem tailTrace_2257648 : CollatzResearch.WordTrace tailWord_2257648 prefixEnd_2257648 772839048441258783678181 := by
  unfold tailWord_2257648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41171593662467173213134799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54895458216622897617513065 41171593662467173213134799)
  ·
    refine ⟨61757390493700759819702199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41171593662467173213134799 61757390493700759819702199)
    ·
      refine ⟨92636085740551139729553299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61757390493700759819702199 92636085740551139729553299)
      ·
        refine ⟨138954128610826709594329949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92636085740551139729553299 138954128610826709594329949)
        ·
          refine ⟨52107798229060016097873731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138954128610826709594329949 52107798229060016097873731)
          ·
            refine ⟨78161697343590024146810597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52107798229060016097873731 78161697343590024146810597)
            ·
              refine ⟨14655318251923129527526987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78161697343590024146810597 14655318251923129527526987)
              ·
                refine ⟨21982977377884694291290481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14655318251923129527526987 21982977377884694291290481)
                ·
                  refine ⟨16487233033413520718467861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21982977377884694291290481 16487233033413520718467861)
                  ·
                    refine ⟨772839048441258783678181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16487233033413520718467861 772839048441258783678181)
                    ·
                      rfl

theorem cell22_2257648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_2257648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257648 prefixEnd_2257648 := by exact prefixLift 2257648
  have htrace : WordTrace (prefixWord ++ tailWord_2257648) baseStart_2257648 baseEnd_2257648 := by
    simpa [prefixWord, tailWord_2257648, baseEnd_2257648] using wordTrace_append hprefix tailTrace_2257648
  have hstable : (prefixWord ++ tailWord_2257648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257648).length < 2 ^ (prefixWord ++ tailWord_2257648).sum := by decide
  have hdescent : baseEnd_2257648 < baseStart_2257648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257815 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 7]
def baseStart_2257815 : Nat := 118140960795 + 2257815 * 2 ^ 59
def prefixEnd_2257815 : Nat := 4983230072969 + 3 ^ 40 * 2257815 * 2
def baseEnd_2257815 : Nat := 257632071984708671584223

theorem tailTrace_2257815 : CollatzResearch.WordTrace tailWord_2257815 prefixEnd_2257815 257632071984708671584223 := by
  unfold tailWord_2257815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82349278315329333947598899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54899518876886222631732599 82349278315329333947598899)
  ·
    refine ⟨123523917472994000921398349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82349278315329333947598899 123523917472994000921398349)
    ·
      refine ⟨46321469052372750345524381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123523917472994000921398349 46321469052372750345524381)
      ·
        refine ⟨17370550894639781379571643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46321469052372750345524381 17370550894639781379571643)
        ·
          refine ⟨26055826341959672069357465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17370550894639781379571643 26055826341959672069357465)
          ·
            refine ⟨19541869756469754052018099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26055826341959672069357465 19541869756469754052018099)
            ·
              refine ⟨29312804634704631078027149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19541869756469754052018099 29312804634704631078027149)
              ·
                refine ⟨10992301738014236654260181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29312804634704631078027149 10992301738014236654260181)
                ·
                  refine ⟨257632071984708671584223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10992301738014236654260181 257632071984708671584223)
                  ·
                    rfl

theorem cell22_2257815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_2257815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257815 prefixEnd_2257815 := by exact prefixLift 2257815
  have htrace : WordTrace (prefixWord ++ tailWord_2257815) baseStart_2257815 baseEnd_2257815 := by
    simpa [prefixWord, tailWord_2257815, baseEnd_2257815] using wordTrace_append hprefix tailTrace_2257815
  have hstable : (prefixWord ++ tailWord_2257815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257815).length < 2 ^ (prefixWord ++ tailWord_2257815).sum := by decide
  have hdescent : baseEnd_2257815 < baseStart_2257815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257943 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 2, 3]
def baseStart_2257943 : Nat := 118140960795 + 2257943 * 2 ^ 59
def prefixEnd_2257943 : Nat := 4983230072969 + 3 ^ 40 * 2257943 * 2
def baseEnd_2257943 : Nat := 772940032969976347552277

theorem tailTrace_2257943 : CollatzResearch.WordTrace tailWord_2257943 prefixEnd_2257943 772940032969976347552277 := by
  unfold tailWord_2257943
  simp only [CollatzResearch.WordTrace]
  refine ⟨82353946858865611808258483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54902631239243741205505655 82353946858865611808258483)
  ·
    refine ⟨123530920288298417712387725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82353946858865611808258483 123530920288298417712387725)
    ·
      refine ⟨46324095108111906642145397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123530920288298417712387725 46324095108111906642145397)
      ·
        refine ⟨4342883916385491247701131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46324095108111906642145397 4342883916385491247701131)
        ·
          refine ⟨6514325874578236871551697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342883916385491247701131 6514325874578236871551697)
          ·
            refine ⟨4885744405933677653663773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6514325874578236871551697 4885744405933677653663773)
            ·
              refine ⟨1832154152225129120123915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4885744405933677653663773 1832154152225129120123915)
              ·
                refine ⟨2748231228337693680185873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832154152225129120123915 2748231228337693680185873)
                ·
                  refine ⟨2061173421253270260139405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748231228337693680185873 2061173421253270260139405)
                  ·
                    refine ⟨772940032969976347552277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061173421253270260139405 772940032969976347552277)
                    ·
                      rfl

theorem cell22_2257943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_2257943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257943 prefixEnd_2257943 := by exact prefixLift 2257943
  have htrace : WordTrace (prefixWord ++ tailWord_2257943) baseStart_2257943 baseEnd_2257943 := by
    simpa [prefixWord, tailWord_2257943, baseEnd_2257943] using wordTrace_append hprefix tailTrace_2257943
  have hstable : (prefixWord ++ tailWord_2257943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257943).length < 2 ^ (prefixWord ++ tailWord_2257943).sum := by decide
  have hdescent : baseEnd_2257943 < baseStart_2257943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2257956 : List Nat := [2, 3, 1, 4, 1, 3, 2, 6]
def baseStart_2257956 : Nat := 118140960795 + 2257956 * 2 ^ 59
def prefixEnd_2257956 : Nat := 4983230072969 + 3 ^ 40 * 2257956 * 2
def baseEnd_2257956 : Nat := 85882720348405405219693

theorem tailTrace_2257956 : CollatzResearch.WordTrace tailWord_2257956 prefixEnd_2257956 85882720348405405219693 := by
  unfold tailWord_2257956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41177210503909257514240861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54902947338545676685654481 41177210503909257514240861)
  ·
    refine ⟨15441453938965971567840323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41177210503909257514240861 15441453938965971567840323)
    ·
      refine ⟨23162180908448957351760485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15441453938965971567840323 23162180908448957351760485)
      ·
        refine ⟨4342908920334179503455091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23162180908448957351760485 4342908920334179503455091)
        ·
          refine ⟨6514363380501269255182637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4342908920334179503455091 6514363380501269255182637)
          ·
            refine ⟨2442886267687975970693489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6514363380501269255182637 2442886267687975970693489)
            ·
              refine ⟨1832164700765981978020117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442886267687975970693489 1832164700765981978020117)
              ·
                refine ⟨85882720348405405219693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1832164700765981978020117 85882720348405405219693)
                ·
                  rfl

theorem cell22_2257956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_2257956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2257956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2257956 prefixEnd_2257956 := by exact prefixLift 2257956
  have htrace : WordTrace (prefixWord ++ tailWord_2257956) baseStart_2257956 baseEnd_2257956 := by
    simpa [prefixWord, tailWord_2257956, baseEnd_2257956] using wordTrace_append hprefix tailTrace_2257956
  have hstable : (prefixWord ++ tailWord_2257956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2257956).length < 2 ^ (prefixWord ++ tailWord_2257956).sum := by decide
  have hdescent : baseEnd_2257956 < baseStart_2257956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2257956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258031 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 1, 4]
def baseStart_2258031 : Nat := 118140960795 + 2258031 * 2 ^ 59
def prefixEnd_2258031 : Nat := 4983230072969 + 3 ^ 40 * 2258031 * 2
def baseEnd_2258031 : Nat := 772970157168373451352007

theorem tailTrace_2258031 : CollatzResearch.WordTrace tailWord_2258031 prefixEnd_2258031 772970157168373451352007 := by
  unfold tailWord_2258031
  simp only [CollatzResearch.WordTrace]
  refine ⟨82357156482546802837461947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54904770988364535224974631 82357156482546802837461947)
  ·
    refine ⟨123535734723820204256192921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82357156482546802837461947 123535734723820204256192921)
    ·
      refine ⟨92651801042865153192144691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123535734723820204256192921 92651801042865153192144691)
      ·
        refine ⟨138977701564297729788217037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92651801042865153192144691 138977701564297729788217037)
        ·
          refine ⟨52116638086611648670581389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138977701564297729788217037 52116638086611648670581389)
          ·
            refine ⟨19543739282479368251468021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52116638086611648670581389 19543739282479368251468021)
            ·
              refine ⟨1832225557732440773575127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19543739282479368251468021 1832225557732440773575127)
              ·
                refine ⟨2748338336598661160362691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832225557732440773575127 2748338336598661160362691)
                ·
                  refine ⟨4122507504897991740544037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748338336598661160362691 4122507504897991740544037)
                  ·
                    refine ⟨772970157168373451352007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122507504897991740544037 772970157168373451352007)
                    ·
                      rfl

theorem cell22_2258031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_2258031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258031 prefixEnd_2258031 := by exact prefixLift 2258031
  have htrace : WordTrace (prefixWord ++ tailWord_2258031) baseStart_2258031 baseEnd_2258031 := by
    simpa [prefixWord, tailWord_2258031, baseEnd_2258031] using wordTrace_append hprefix tailTrace_2258031
  have hstable : (prefixWord ++ tailWord_2258031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258031).length < 2 ^ (prefixWord ++ tailWord_2258031).sum := by decide
  have hdescent : baseEnd_2258031 < baseStart_2258031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258076 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2258076 : Nat := 118140960795 + 2258076 * 2 ^ 59
def prefixEnd_2258076 : Nat := 4983230072969 + 3 ^ 40 * 2258076 * 2
def baseEnd_2258076 : Nat := 772985561588008333976869

theorem tailTrace_2258076 : CollatzResearch.WordTrace tailWord_2258076 prefixEnd_2258076 772985561588008333976869 := by
  unfold tailWord_2258076
  simp only [CollatzResearch.WordTrace]
  refine ⟨41179398883691887761425041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54905865178255850348566721 41179398883691887761425041)
  ·
    refine ⟨30884549162768915821068781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41179398883691887761425041 30884549162768915821068781)
    ·
      refine ⟨11581705936038343432900793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30884549162768915821068781 11581705936038343432900793)
      ·
        refine ⟨8686279452028757574675595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11581705936038343432900793 8686279452028757574675595)
        ·
          refine ⟨13029419178043136362013393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8686279452028757574675595 13029419178043136362013393)
          ·
            refine ⟨9772064383532352271510045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13029419178043136362013393 9772064383532352271510045)
            ·
              refine ⟨3664524143824632101816267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9772064383532352271510045 3664524143824632101816267)
              ·
                refine ⟨5496786215736948152724401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664524143824632101816267 5496786215736948152724401)
                ·
                  refine ⟨4122589661802711114543301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5496786215736948152724401 4122589661802711114543301)
                  ·
                    refine ⟨772985561588008333976869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122589661802711114543301 772985561588008333976869)
                    ·
                      rfl

theorem cell22_2258076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2258076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258076 prefixEnd_2258076 := by exact prefixLift 2258076
  have htrace : WordTrace (prefixWord ++ tailWord_2258076) baseStart_2258076 baseEnd_2258076 := by
    simpa [prefixWord, tailWord_2258076, baseEnd_2258076] using wordTrace_append hprefix tailTrace_2258076
  have hstable : (prefixWord ++ tailWord_2258076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258076).length < 2 ^ (prefixWord ++ tailWord_2258076).sum := by decide
  have hdescent : baseEnd_2258076 < baseStart_2258076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258082 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2258082 : Nat := 118140960795 + 2258082 * 2 ^ 59
def prefixEnd_2258082 : Nat := 4983230072969 + 3 ^ 40 * 2258082 * 2
def baseEnd_2258082 : Nat := 772987615510626318326851

theorem tailTrace_2258082 : CollatzResearch.WordTrace tailWord_2258082 prefixEnd_2258082 772987615510626318326851 := by
  unfold tailWord_2258082
  simp only [CollatzResearch.WordTrace]
  refine ⟨20589754151340509636892125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54906011070241359031712333 20589754151340509636892125)
  ·
    refine ⟨7721157806752691113834547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20589754151340509636892125 7721157806752691113834547)
    ·
      refine ⟨11581736710129036670751821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7721157806752691113834547 11581736710129036670751821)
      ·
        refine ⟨4343151266298388751531933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11581736710129036670751821 4343151266298388751531933)
        ·
          refine ⟨1628681724861895781824475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4343151266298388751531933 1628681724861895781824475)
          ·
            refine ⟨2443022587292843672736713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628681724861895781824475 2443022587292843672736713)
            ·
              refine ⟨1832266940469632754552535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443022587292843672736713 1832266940469632754552535)
              ·
                refine ⟨2748400410704449131828803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832266940469632754552535 2748400410704449131828803)
                ·
                  refine ⟨4122600616056673697743205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2748400410704449131828803 4122600616056673697743205)
                  ·
                    refine ⟨772987615510626318326851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122600616056673697743205 772987615510626318326851)
                    ·
                      rfl

theorem cell22_2258082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2258082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258082 prefixEnd_2258082 := by exact prefixLift 2258082
  have htrace : WordTrace (prefixWord ++ tailWord_2258082) baseStart_2258082 baseEnd_2258082 := by
    simpa [prefixWord, tailWord_2258082, baseEnd_2258082] using wordTrace_append hprefix tailTrace_2258082
  have hstable : (prefixWord ++ tailWord_2258082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258082).length < 2 ^ (prefixWord ++ tailWord_2258082).sum := by decide
  have hdescent : baseEnd_2258082 < baseStart_2258082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258119 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 5]
def baseStart_2258119 : Nat := 118140960795 + 2258119 * 2 ^ 59
def prefixEnd_2258119 : Nat := 4983230072969 + 3 ^ 40 * 2258119 * 2
def baseEnd_2258119 : Nat := 257666760455590185050579

theorem tailTrace_2258119 : CollatzResearch.WordTrace tailWord_2258119 prefixEnd_2258119 257666760455590185050579 := by
  unfold tailWord_2258119
  simp only [CollatzResearch.WordTrace]
  refine ⟨82360366106227993866665411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54906910737485329244443607 82360366106227993866665411)
  ·
    refine ⟨123540549159341990799998117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82360366106227993866665411 123540549159341990799998117)
    ·
      refine ⟨23163852967376623274999647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123540549159341990799998117 23163852967376623274999647)
      ·
        refine ⟨34745779451064934912499471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23163852967376623274999647 34745779451064934912499471)
        ·
          refine ⟨52118669176597402368749207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34745779451064934912499471 52118669176597402368749207)
          ·
            refine ⟨78178003764896103553123811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52118669176597402368749207 78178003764896103553123811)
            ·
              refine ⟨117267005647344155329685717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78178003764896103553123811 117267005647344155329685717)
              ·
                refine ⟨2748445444859628640539509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117267005647344155329685717 2748445444859628640539509)
                ·
                  refine ⟨257666760455590185050579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748445444859628640539509 257666760455590185050579)
                  ·
                    rfl

theorem cell22_2258119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 5].length) (baseStart_2258119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258119 prefixEnd_2258119 := by exact prefixLift 2258119
  have htrace : WordTrace (prefixWord ++ tailWord_2258119) baseStart_2258119 baseEnd_2258119 := by
    simpa [prefixWord, tailWord_2258119, baseEnd_2258119] using wordTrace_append hprefix tailTrace_2258119
  have hstable : (prefixWord ++ tailWord_2258119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258119).length < 2 ^ (prefixWord ++ tailWord_2258119).sum := by decide
  have hdescent : baseEnd_2258119 < baseStart_2258119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258157 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2258157 : Nat := 118140960795 + 2258157 * 2 ^ 59
def prefixEnd_2258157 : Nat := 4983230072969 + 3 ^ 40 * 2258157 * 2
def baseEnd_2258157 : Nat := 773013289543351122701621

theorem tailTrace_2258157 : CollatzResearch.WordTrace tailWord_2258157 prefixEnd_2258157 773013289543351122701621 := by
  unfold tailWord_2258157
  simp only [CollatzResearch.WordTrace]
  refine ⟨82361752080090326356548725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54907834720060217571032483 82361752080090326356548725)
  ·
    refine ⟨7721414257508468095926443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82361752080090326356548725 7721414257508468095926443)
    ·
      refine ⟨11582121386262702143889665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7721414257508468095926443 11582121386262702143889665)
      ·
        refine ⟨8686591039697026607917249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11582121386262702143889665 8686591039697026607917249)
        ·
          refine ⟨6514943279772769955937937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8686591039697026607917249 6514943279772769955937937)
          ·
            refine ⟨4886207459829577466953453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6514943279772769955937937 4886207459829577466953453)
            ·
              refine ⟨1832327797436091550107545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4886207459829577466953453 1832327797436091550107545)
              ·
                refine ⟨1374245848077068662580659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1832327797436091550107545 1374245848077068662580659)
                ·
                  refine ⟨2061368772115602993870989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374245848077068662580659 2061368772115602993870989)
                  ·
                    refine ⟨773013289543351122701621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061368772115602993870989 773013289543351122701621)
                    ·
                      rfl

theorem cell22_2258157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2258157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258157 prefixEnd_2258157 := by exact prefixLift 2258157
  have htrace : WordTrace (prefixWord ++ tailWord_2258157) baseStart_2258157 baseEnd_2258157 := by
    simpa [prefixWord, tailWord_2258157, baseEnd_2258157] using wordTrace_append hprefix tailTrace_2258157
  have hstable : (prefixWord ++ tailWord_2258157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258157).length < 2 ^ (prefixWord ++ tailWord_2258157).sum := by decide
  have hdescent : baseEnd_2258157 < baseStart_2258157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258166 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2258166 : Nat := 118140960795 + 2258166 * 2 ^ 59
def prefixEnd_2258166 : Nat := 4983230072969 + 3 ^ 40 * 2258166 * 2
def baseEnd_2258166 : Nat := 773016370427278099226593

theorem tailTrace_2258166 : CollatzResearch.WordTrace tailWord_2258166 prefixEnd_2258166 773016370427278099226593 := by
  unfold tailWord_2258166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147630021066107555851647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 54908053558038480595750901 5147630021066107555851647)
  ·
    refine ⟨7721445031599161333777471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5147630021066107555851647 7721445031599161333777471)
    ·
      refine ⟨11582167547398742000666207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7721445031599161333777471 11582167547398742000666207)
      ·
        refine ⟨17373251321098113000999311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11582167547398742000666207 17373251321098113000999311)
        ·
          refine ⟨26059876981647169501498967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17373251321098113000999311 26059876981647169501498967)
          ·
            refine ⟨39089815472470754252248451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26059876981647169501498967 39089815472470754252248451)
            ·
              refine ⟨58634723208706131378372677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39089815472470754252248451 58634723208706131378372677)
              ·
                refine ⟨10994010601632399633444877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58634723208706131378372677 10994010601632399633444877)
                ·
                  refine ⟨4122753975612149862541829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10994010601632399633444877 4122753975612149862541829)
                  ·
                    refine ⟨773016370427278099226593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122753975612149862541829 773016370427278099226593)
                    ·
                      rfl

theorem cell22_2258166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2258166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258166 prefixEnd_2258166 := by exact prefixLift 2258166
  have htrace : WordTrace (prefixWord ++ tailWord_2258166) baseStart_2258166 baseEnd_2258166 := by
    simpa [prefixWord, tailWord_2258166, baseEnd_2258166] using wordTrace_append hprefix tailTrace_2258166
  have hstable : (prefixWord ++ tailWord_2258166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258166).length < 2 ^ (prefixWord ++ tailWord_2258166).sum := by decide
  have hdescent : baseEnd_2258166 < baseStart_2258166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258211 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_2258211 : Nat := 118140960795 + 2258211 * 2 ^ 59
def prefixEnd_2258211 : Nat := 4983230072969 + 3 ^ 40 * 2258211 * 2
def baseEnd_2258211 : Nat := 773031774846912981851455

theorem tailTrace_2258211 : CollatzResearch.WordTrace tailWord_2258211 prefixEnd_2258211 773031774846912981851455 := by
  unfold tailWord_2258211
  simp only [CollatzResearch.WordTrace]
  refine ⟨82363721621894693579014487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54909147747929795719342991 82363721621894693579014487)
  ·
    refine ⟨123545582432842040368521731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82363721621894693579014487 123545582432842040368521731)
    ·
      refine ⟨185318373649263060552782597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123545582432842040368521731 185318373649263060552782597)
      ·
        refine ⟨34747195059236823853646737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185318373649263060552782597 34747195059236823853646737)
        ·
          refine ⟨26060396294427617890235053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34747195059236823853646737 26060396294427617890235053)
          ·
            refine ⟨9772648610410356708838145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26060396294427617890235053 9772648610410356708838145)
            ·
              refine ⟨7329486457807767531628609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9772648610410356708838145 7329486457807767531628609)
              ·
                refine ⟨5497114843355825648721457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7329486457807767531628609 5497114843355825648721457)
                ·
                  refine ⟨4122836132516869236541093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5497114843355825648721457 4122836132516869236541093)
                  ·
                    refine ⟨773031774846912981851455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4122836132516869236541093 773031774846912981851455)
                    ·
                      rfl

theorem cell22_2258211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_2258211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258211 prefixEnd_2258211 := by exact prefixLift 2258211
  have htrace : WordTrace (prefixWord ++ tailWord_2258211) baseStart_2258211 baseEnd_2258211 := by
    simpa [prefixWord, tailWord_2258211, baseEnd_2258211] using wordTrace_append hprefix tailTrace_2258211
  have hstable : (prefixWord ++ tailWord_2258211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258211).length < 2 ^ (prefixWord ++ tailWord_2258211).sum := by decide
  have hdescent : baseEnd_2258211 < baseStart_2258211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258213 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_2258213 : Nat := 118140960795 + 2258213 * 2 ^ 59
def prefixEnd_2258213 : Nat := 4983230072969 + 3 ^ 40 * 2258213 * 2
def baseEnd_2258213 : Nat := 773032459487785643301449

theorem tailTrace_2258213 : CollatzResearch.WordTrace tailWord_2258213 prefixEnd_2258213 773032459487785643301449 := by
  unfold tailWord_2258213
  simp only [CollatzResearch.WordTrace]
  refine ⟨82363794567887447920587293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54909196378591631947058195 82363794567887447920587293)
  ·
    refine ⟨30886422962957792970220235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82363794567887447920587293 30886422962957792970220235)
    ·
      refine ⟨46329634444436689455330353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30886422962957792970220235 46329634444436689455330353)
      ·
        refine ⟨34747225833327517091497765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46329634444436689455330353 34747225833327517091497765)
        ·
          refine ⟨6515104843748909454655831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34747225833327517091497765 6515104843748909454655831)
          ·
            refine ⟨9772657265623364181983747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515104843748909454655831 9772657265623364181983747)
            ·
              refine ⟨14658985898435046272975621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9772657265623364181983747 14658985898435046272975621)
              ·
                refine ⟨2748559855956571176182929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14658985898435046272975621 2748559855956571176182929)
                ·
                  refine ⟨2061419891967428382137197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748559855956571176182929 2061419891967428382137197)
                  ·
                    refine ⟨773032459487785643301449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061419891967428382137197 773032459487785643301449)
                    ·
                      rfl

theorem cell22_2258213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_2258213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258213 prefixEnd_2258213 := by exact prefixLift 2258213
  have htrace : WordTrace (prefixWord ++ tailWord_2258213) baseStart_2258213 baseEnd_2258213 := by
    simpa [prefixWord, tailWord_2258213, baseEnd_2258213] using wordTrace_append hprefix tailTrace_2258213
  have hstable : (prefixWord ++ tailWord_2258213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258213).length < 2 ^ (prefixWord ++ tailWord_2258213).sum := by decide
  have hdescent : baseEnd_2258213 < baseStart_2258213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258226 : List Nat := [3, 2, 1, 1, 4, 1, 3, 7]
def baseStart_2258226 : Nat := 118140960795 + 2258226 * 2 ^ 59
def prefixEnd_2258226 : Nat := 4983230072969 + 3 ^ 40 * 2258226 * 2
def baseEnd_2258226 : Nat := 85892989961495326969601

theorem tailTrace_2258226 : CollatzResearch.WordTrace tailWord_2258226 prefixEnd_2258226 85892989961495326969601 := by
  unfold tailWord_2258226
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591067179210087785202633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54909512477893567427207021 20591067179210087785202633)
  ·
    refine ⟨15443300384407565838901975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20591067179210087785202633 15443300384407565838901975)
    ·
      refine ⟨23164950576611348758352963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15443300384407565838901975 23164950576611348758352963)
      ·
        refine ⟨34747425864917023137529445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23164950576611348758352963 34747425864917023137529445)
        ·
          refine ⟨6515142349671941838286771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34747425864917023137529445 6515142349671941838286771)
          ·
            refine ⟨9772713524507912757430157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515142349671941838286771 9772713524507912757430157)
            ·
              refine ⟨3664767571690467284036309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9772713524507912757430157 3664767571690467284036309)
              ·
                refine ⟨85892989961495326969601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3664767571690467284036309 85892989961495326969601)
                ·
                  rfl

theorem cell22_2258226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_2258226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258226 prefixEnd_2258226 := by exact prefixLift 2258226
  have htrace : WordTrace (prefixWord ++ tailWord_2258226) baseStart_2258226 baseEnd_2258226 := by
    simpa [prefixWord, tailWord_2258226, baseEnd_2258226] using wordTrace_append hprefix tailTrace_2258226
  have hstable : (prefixWord ++ tailWord_2258226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258226).length < 2 ^ (prefixWord ++ tailWord_2258226).sum := by decide
  have hdescent : baseEnd_2258226 < baseStart_2258226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258275 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 1, 3]
def baseStart_2258275 : Nat := 118140960795 + 2258275 * 2 ^ 59
def prefixEnd_2258275 : Nat := 4983230072969 + 3 ^ 40 * 2258275 * 2
def baseEnd_2258275 : Nat := 773053683354838148251259

theorem tailTrace_2258275 : CollatzResearch.WordTrace tailWord_2258275 prefixEnd_2258275 773053683354838148251259 := by
  unfold tailWord_2258275
  simp only [CollatzResearch.WordTrace]
  refine ⟨82366055893662832509344279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54910703929108555006229519 82366055893662832509344279)
  ·
    refine ⟨123549083840494248764016419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82366055893662832509344279 123549083840494248764016419)
    ·
      refine ⟨185323625760741373146024629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123549083840494248764016419 185323625760741373146024629)
      ·
        refine ⟨17374089915069503732439809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185323625760741373146024629 17374089915069503732439809)
        ·
          refine ⟨13030567436302127799329857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17374089915069503732439809 13030567436302127799329857)
          ·
            refine ⟨9772925577226595849497393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13030567436302127799329857 9772925577226595849497393)
            ·
              refine ⟨7329694182919946887123045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9772925577226595849497393 7329694182919946887123045)
              ·
                refine ⟨1374317659297490041335571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7329694182919946887123045 1374317659297490041335571)
                ·
                  refine ⟨2061476488946235062003357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374317659297490041335571 2061476488946235062003357)
                  ·
                    refine ⟨773053683354838148251259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061476488946235062003357 773053683354838148251259)
                    ·
                      rfl

theorem cell22_2258275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 3].length) (baseStart_2258275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258275 prefixEnd_2258275 := by exact prefixLift 2258275
  have htrace : WordTrace (prefixWord ++ tailWord_2258275) baseStart_2258275 baseEnd_2258275 := by
    simpa [prefixWord, tailWord_2258275, baseEnd_2258275] using wordTrace_append hprefix tailTrace_2258275
  have hstable : (prefixWord ++ tailWord_2258275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258275).length < 2 ^ (prefixWord ++ tailWord_2258275).sum := by decide
  have hdescent : baseEnd_2258275 < baseStart_2258275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258288 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_2258288 : Nat := 118140960795 + 2258288 * 2 ^ 59
def prefixEnd_2258288 : Nat := 4983230072969 + 3 ^ 40 * 2258288 * 2
def baseEnd_2258288 : Nat := 257686044506836815892073

theorem tailTrace_2258288 : CollatzResearch.WordTrace tailWord_2258288 prefixEnd_2258288 257686044506836815892073 := by
  unfold tailWord_2258288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41183265021307867864783759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54911020028410490486378345 41183265021307867864783759)
  ·
    refine ⟨61774897531961801797175639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41183265021307867864783759 61774897531961801797175639)
    ·
      refine ⟨92662346297942702695763459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61774897531961801797175639 92662346297942702695763459)
      ·
        refine ⟨138993519446914054043645189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92662346297942702695763459 138993519446914054043645189)
        ·
          refine ⟨26061284896296385133183473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 138993519446914054043645189 26061284896296385133183473)
          ·
            refine ⟨19545963672222288849887605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26061284896296385133183473 19545963672222288849887605)
            ·
              refine ⟨1832434094270839579676963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19545963672222288849887605 1832434094270839579676963)
              ·
                refine ⟨2748651141406259369515445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832434094270839579676963 2748651141406259369515445)
                ·
                  refine ⟨257686044506836815892073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748651141406259369515445 257686044506836815892073)
                  ·
                    rfl

theorem cell22_2258288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_2258288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258288 prefixEnd_2258288 := by exact prefixLift 2258288
  have htrace : WordTrace (prefixWord ++ tailWord_2258288) baseStart_2258288 baseEnd_2258288 := by
    simpa [prefixWord, tailWord_2258288, baseEnd_2258288] using wordTrace_append hprefix tailTrace_2258288
  have hstable : (prefixWord ++ tailWord_2258288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258288).length < 2 ^ (prefixWord ++ tailWord_2258288).sum := by decide
  have hdescent : baseEnd_2258288 < baseStart_2258288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258333 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 6]
def baseStart_2258333 : Nat := 118140960795 + 2258333 * 2 ^ 59
def prefixEnd_2258333 : Nat := 4983230072969 + 3 ^ 40 * 2258333 * 2
def baseEnd_2258333 : Nat := 257691179313381776767027

theorem tailTrace_2258333 : CollatzResearch.WordTrace tailWord_2258333 prefixEnd_2258333 257691179313381776767027 := by
  unfold tailWord_2258333
  simp only [CollatzResearch.WordTrace]
  refine ⟨82368171327452708414955653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54912114218301805609970435 82368171327452708414955653)
  ·
    refine ⟨15444032123897382827804185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82368171327452708414955653 15444032123897382827804185)
    ·
      refine ⟨11583024092923037120853139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15444032123897382827804185 11583024092923037120853139)
      ·
        refine ⟨17374536139384555681279709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11583024092923037120853139 17374536139384555681279709)
        ·
          refine ⟨6515451052269208380479891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17374536139384555681279709 6515451052269208380479891)
          ·
            refine ⟨9773176578403812570719837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6515451052269208380479891 9773176578403812570719837)
            ·
              refine ⟨3664941216901429714019939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9773176578403812570719837 3664941216901429714019939)
              ·
                refine ⟨5497411825352144571029909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664941216901429714019939 5497411825352144571029909)
                ·
                  refine ⟨257691179313381776767027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5497411825352144571029909 257691179313381776767027)
                  ·
                    rfl

theorem cell22_2258333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_2258333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258333 prefixEnd_2258333 := by exact prefixLift 2258333
  have htrace : WordTrace (prefixWord ++ tailWord_2258333) baseStart_2258333 baseEnd_2258333 := by
    simpa [prefixWord, tailWord_2258333, baseEnd_2258333] using wordTrace_append hprefix tailTrace_2258333
  have hstable : (prefixWord ++ tailWord_2258333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258333).length < 2 ^ (prefixWord ++ tailWord_2258333).sum := by decide
  have hdescent : baseEnd_2258333 < baseStart_2258333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258513 : List Nat := [1, 2, 2, 1, 3, 2, 4, 7]
def baseStart_2258513 : Nat := 118140960795 + 2258513 * 2 ^ 59
def prefixEnd_2258513 : Nat := 4983230072969 + 3 ^ 40 * 2258513 * 2
def baseEnd_2258513 : Nat := 85903906179853873422281

theorem tailTrace_2258513 : CollatzResearch.WordTrace tailWord_2258513 prefixEnd_2258513 85903906179853873422281 := by
  unfold tailWord_2258513
  simp only [CollatzResearch.WordTrace]
  refine ⟨82374736466800599156508193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54916490977867066104338795 82374736466800599156508193)
  ·
    refine ⟨61781052350100449367381145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82374736466800599156508193 61781052350100449367381145)
    ·
      refine ⟨46335789262575337025535859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61781052350100449367381145 46335789262575337025535859)
      ·
        refine ⟨69503683893863005538303789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46335789262575337025535859 69503683893863005538303789)
        ·
          refine ⟨26063881460198627076863921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69503683893863005538303789 26063881460198627076863921)
          ·
            refine ⟨19547911095148970307647941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26063881460198627076863921 19547911095148970307647941)
            ·
              refine ⟨3665233330340431932683989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19547911095148970307647941 3665233330340431932683989)
              ·
                refine ⟨85903906179853873422281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3665233330340431932683989 85903906179853873422281)
                ·
                  rfl

theorem cell22_2258513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 7].length) (baseStart_2258513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258513 prefixEnd_2258513 := by exact prefixLift 2258513
  have htrace : WordTrace (prefixWord ++ tailWord_2258513) baseStart_2258513 baseEnd_2258513 := by
    simpa [prefixWord, tailWord_2258513, baseEnd_2258513] using wordTrace_append hprefix tailTrace_2258513
  have hstable : (prefixWord ++ tailWord_2258513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258513).length < 2 ^ (prefixWord ++ tailWord_2258513).sum := by decide
  have hdescent : baseEnd_2258513 < baseStart_2258513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258620 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_2258620 : Nat := 118140960795 + 2258620 * 2 ^ 59
def prefixEnd_2258620 : Nat := 4983230072969 + 3 ^ 40 * 2258620 * 2
def baseEnd_2258620 : Nat := 257723927968457416125067

theorem tailTrace_2258620 : CollatzResearch.WordTrace tailWord_2258620 prefixEnd_2258620 257723927968457416125067 := by
  unfold tailWord_2258620
  simp only [CollatzResearch.WordTrace]
  refine ⟨41189319538706478215326657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54919092718275304287102209 41189319538706478215326657)
  ·
    refine ⟨30891989654029858661494993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41189319538706478215326657 30891989654029858661494993)
    ·
      refine ⟨23168992240522393996121245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30891989654029858661494993 23168992240522393996121245)
      ·
        refine ⟨8688372090195897748545467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23168992240522393996121245 8688372090195897748545467)
        ·
          refine ⟨13032558135293846622818201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8688372090195897748545467 13032558135293846622818201)
          ·
            refine ⟨9774418601470384967113651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13032558135293846622818201 9774418601470384967113651)
            ·
              refine ⟨14661627902205577450670477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9774418601470384967113651 14661627902205577450670477)
              ·
                refine ⟨5498110463327091544001429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14661627902205577450670477 5498110463327091544001429)
                ·
                  refine ⟨257723927968457416125067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5498110463327091544001429 257723927968457416125067)
                  ·
                    rfl

theorem cell22_2258620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_2258620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258620 prefixEnd_2258620 := by exact prefixLift 2258620
  have htrace : WordTrace (prefixWord ++ tailWord_2258620) baseStart_2258620 baseEnd_2258620 := by
    simpa [prefixWord, tailWord_2258620, baseEnd_2258620] using wordTrace_append hprefix tailTrace_2258620
  have hstable : (prefixWord ++ tailWord_2258620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258620).length < 2 ^ (prefixWord ++ tailWord_2258620).sum := by decide
  have hdescent : baseEnd_2258620 < baseStart_2258620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258650 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_2258650 : Nat := 118140960795 + 2258650 * 2 ^ 59
def prefixEnd_2258650 : Nat := 4983230072969 + 3 ^ 40 * 2258650 * 2
def baseEnd_2258650 : Nat := 773182053518462170125109

theorem tailTrace_2258650 : CollatzResearch.WordTrace tailWord_2258650 prefixEnd_2258650 773182053518462170125109 := by
  unfold tailWord_2258650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20594933316826067888561351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54919822178202847702830269 20594933316826067888561351)
  ·
    refine ⟨30892399975239101832842027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20594933316826067888561351 30892399975239101832842027)
    ·
      refine ⟨46338599962858652749263041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30892399975239101832842027 46338599962858652749263041)
      ·
        refine ⟨34753949972143989561947281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46338599962858652749263041 34753949972143989561947281)
        ·
          refine ⟨26065462479107992171460461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34753949972143989561947281 26065462479107992171460461)
          ·
            refine ⟨9774548429665497064297673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26065462479107992171460461 9774548429665497064297673)
            ·
              refine ⟨7330911322249122798223255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9774548429665497064297673 7330911322249122798223255)
              ·
                refine ⟨10996366983373684197334883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7330911322249122798223255 10996366983373684197334883)
                ·
                  refine ⟨16494550475060526296002325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10996366983373684197334883 16494550475060526296002325)
                  ·
                    refine ⟨773182053518462170125109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16494550475060526296002325 773182053518462170125109)
                    ·
                      rfl

theorem cell22_2258650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_2258650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258650 prefixEnd_2258650 := by exact prefixLift 2258650
  have htrace : WordTrace (prefixWord ++ tailWord_2258650) baseStart_2258650 baseEnd_2258650 := by
    simpa [prefixWord, tailWord_2258650, baseEnd_2258650] using wordTrace_append hprefix tailTrace_2258650
  have hstable : (prefixWord ++ tailWord_2258650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258650).length < 2 ^ (prefixWord ++ tailWord_2258650).sum := by decide
  have hdescent : baseEnd_2258650 < baseStart_2258650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258686 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2258686 : Nat := 118140960795 + 2258686 * 2 ^ 59
def prefixEnd_2258686 : Nat := 4983230072969 + 3 ^ 40 * 2258686 * 2
def baseEnd_2258686 : Nat := 773194377054170076224999

theorem tailTrace_2258686 : CollatzResearch.WordTrace tailWord_2258686 prefixEnd_2258686 773194377054170076224999 := by
  unfold tailWord_2258686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297630786896731212819489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54920697530115899801703941 10297630786896731212819489)
  ·
    refine ⟨7723223090172548409614617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10297630786896731212819489 7723223090172548409614617)
    ·
      refine ⟨5792417317629411307210963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7723223090172548409614617 5792417317629411307210963)
      ·
        refine ⟨8688625976444116960816445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792417317629411307210963 8688625976444116960816445)
        ·
          refine ⟨3258234741166543860306167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8688625976444116960816445 3258234741166543860306167)
          ·
            refine ⟨4887352111749815790459251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258234741166543860306167 4887352111749815790459251)
            ·
              refine ⟨7331028167624723685688877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887352111749815790459251 7331028167624723685688877)
              ·
                refine ⟨2749135562859271382133329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331028167624723685688877 2749135562859271382133329)
                ·
                  refine ⟨2061851672144453536599997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2749135562859271382133329 2061851672144453536599997)
                  ·
                    refine ⟨773194377054170076224999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061851672144453536599997 773194377054170076224999)
                    ·
                      rfl

theorem cell22_2258686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2258686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258686 prefixEnd_2258686 := by exact prefixLift 2258686
  have htrace : WordTrace (prefixWord ++ tailWord_2258686) baseStart_2258686 baseEnd_2258686 := by
    simpa [prefixWord, tailWord_2258686, baseEnd_2258686] using wordTrace_append hprefix tailTrace_2258686
  have hstable : (prefixWord ++ tailWord_2258686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258686).length < 2 ^ (prefixWord ++ tailWord_2258686).sum := by decide
  have hdescent : baseEnd_2258686 < baseStart_2258686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258755 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 8]
def baseStart_2258755 : Nat := 118140960795 + 2258755 * 2 ^ 59
def prefixEnd_2258755 : Nat := 4983230072969 + 3 ^ 40 * 2258755 * 2
def baseEnd_2258755 : Nat := 257739332388092298749929

theorem tailTrace_2258755 : CollatzResearch.WordTrace tailWord_2258755 prefixEnd_2258755 257739332388092298749929 := by
  unfold tailWord_2258755
  simp only [CollatzResearch.WordTrace]
  refine ⟨82383562931923874486817719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54922375287949249657878479 82383562931923874486817719)
  ·
    refine ⟨123575344397885811730226579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82383562931923874486817719 123575344397885811730226579)
    ·
      refine ⟨185363016596828717595339869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123575344397885811730226579 185363016596828717595339869)
      ·
        refine ⟨69511131223810769098252451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185363016596828717595339869 69511131223810769098252451)
        ·
          refine ⟨104266696835716153647378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69511131223810769098252451 104266696835716153647378677)
          ·
            refine ⟨9775002828348389404441751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104266696835716153647378677 9775002828348389404441751)
            ·
              refine ⟨14662504242522584106662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9775002828348389404441751 14662504242522584106662627)
              ·
                refine ⟨21993756363783876159993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14662504242522584106662627 21993756363783876159993941)
                ·
                  refine ⟨257739332388092298749929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21993756363783876159993941 257739332388092298749929)
                  ·
                    rfl

theorem cell22_2258755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_2258755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258755 prefixEnd_2258755 := by exact prefixLift 2258755
  have htrace : WordTrace (prefixWord ++ tailWord_2258755) baseStart_2258755 baseEnd_2258755 := by
    simpa [prefixWord, tailWord_2258755, baseEnd_2258755] using wordTrace_append hprefix tailTrace_2258755
  have hstable : (prefixWord ++ tailWord_2258755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258755).length < 2 ^ (prefixWord ++ tailWord_2258755).sum := by decide
  have hdescent : baseEnd_2258755 < baseStart_2258755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258757 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_2258757 : Nat := 118140960795 + 2258757 * 2 ^ 59
def prefixEnd_2258757 : Nat := 4983230072969 + 3 ^ 40 * 2258757 * 2
def baseEnd_2258757 : Nat := 773218681805149557699781

theorem tailTrace_2258757 : CollatzResearch.WordTrace tailWord_2258757 prefixEnd_2258757 773218681805149557699781 := by
  unfold tailWord_2258757
  simp only [CollatzResearch.WordTrace]
  refine ⟨82383635877916628828390525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54922423918611085885593683 82383635877916628828390525)
  ·
    refine ⟨30893863454218735810646447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82383635877916628828390525 30893863454218735810646447)
    ·
      refine ⟨46340795181328103715969671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30893863454218735810646447 46340795181328103715969671)
      ·
        refine ⟨69511192771992155573954507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46340795181328103715969671 69511192771992155573954507)
        ·
          refine ⟨104266789157988233360931761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69511192771992155573954507 104266789157988233360931761)
          ·
            refine ⟨78200091868491175020698821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104266789157988233360931761 78200091868491175020698821)
            ·
              refine ⟨14662517225342095316381029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78200091868491175020698821 14662517225342095316381029)
              ·
                refine ⟨2749221979751642871821443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14662517225342095316381029 2749221979751642871821443)
                ·
                  refine ⟨4123832969627464307732165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2749221979751642871821443 4123832969627464307732165)
                  ·
                    refine ⟨773218681805149557699781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4123832969627464307732165 773218681805149557699781)
                    ·
                      rfl

theorem cell22_2258757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_2258757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258757 prefixEnd_2258757 := by exact prefixLift 2258757
  have htrace : WordTrace (prefixWord ++ tailWord_2258757) baseStart_2258757 baseEnd_2258757 := by
    simpa [prefixWord, tailWord_2258757, baseEnd_2258757] using wordTrace_append hprefix tailTrace_2258757
  have hstable : (prefixWord ++ tailWord_2258757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258757).length < 2 ^ (prefixWord ++ tailWord_2258757).sum := by decide
  have hdescent : baseEnd_2258757 < baseStart_2258757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258800 : List Nat := [2, 1, 1, 1, 4, 1, 1, 11]
def baseStart_2258800 : Nat := 118140960795 + 2258800 * 2 ^ 59
def prefixEnd_2258800 : Nat := 4983230072969 + 3 ^ 40 * 2258800 * 2
def baseEnd_2258800 : Nat := 85914822398212419874961

theorem tailTrace_2258800 : CollatzResearch.WordTrace tailWord_2258800 prefixEnd_2258800 85914822398212419874961 := by
  unfold tailWord_2258800
  simp only [CollatzResearch.WordTrace]
  refine ⟨41192602108380423586102927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54923469477840564781470569 41192602108380423586102927)
  ·
    refine ⟨61788903162570635379154391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41192602108380423586102927 61788903162570635379154391)
    ·
      refine ⟨92683354743855953068731587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61788903162570635379154391 92683354743855953068731587)
      ·
        refine ⟨139025032115783929603097381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92683354743855953068731587 139025032115783929603097381)
        ·
          refine ⟨26067193521709486800580759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139025032115783929603097381 26067193521709486800580759)
          ·
            refine ⟨39100790282564230200871139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26067193521709486800580759 39100790282564230200871139)
            ·
              refine ⟨58651185423846345301306709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39100790282564230200871139 58651185423846345301306709)
              ·
                refine ⟨85914822398212419874961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58651185423846345301306709 85914822398212419874961)
                ·
                  rfl

theorem cell22_2258800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_2258800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258800 prefixEnd_2258800 := by exact prefixLift 2258800
  have htrace : WordTrace (prefixWord ++ tailWord_2258800) baseStart_2258800 baseEnd_2258800 := by
    simpa [prefixWord, tailWord_2258800, baseEnd_2258800] using wordTrace_append hprefix tailTrace_2258800
  have hstable : (prefixWord ++ tailWord_2258800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258800).length < 2 ^ (prefixWord ++ tailWord_2258800).sum := by decide
  have hdescent : baseEnd_2258800 < baseStart_2258800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258815 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_2258815 : Nat := 118140960795 + 2258815 * 2 ^ 59
def prefixEnd_2258815 : Nat := 4983230072969 + 3 ^ 40 * 2258815 * 2
def baseEnd_2258815 : Nat := 773238536390456739749603

theorem tailTrace_2258815 : CollatzResearch.WordTrace tailWord_2258815 prefixEnd_2258815 773238536390456739749603 := by
  unfold tailWord_2258815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82385751311706504734001899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54923834207804336489334599 82385751311706504734001899)
  ·
    refine ⟨123578626967559757101002849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82385751311706504734001899 123578626967559757101002849)
    ·
      refine ⟨92683970225669817825752137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123578626967559757101002849 92683970225669817825752137)
      ·
        refine ⟨69512977669252363369314103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92683970225669817825752137 69512977669252363369314103)
        ·
          refine ⟨104269466503878545053971155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69512977669252363369314103 104269466503878545053971155)
          ·
            refine ⟨156404199755817817580956733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104269466503878545053971155 156404199755817817580956733)
            ·
              refine ⟨58651574908431681592858775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156404199755817817580956733 58651574908431681592858775)
              ·
                refine ⟨87977362362647522389288163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58651574908431681592858775 87977362362647522389288163)
                ·
                  refine ⟨131966043543971283583932245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87977362362647522389288163 131966043543971283583932245)
                  ·
                    refine ⟨773238536390456739749603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 131966043543971283583932245 773238536390456739749603)
                    ·
                      rfl

theorem cell22_2258815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_2258815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258815 prefixEnd_2258815 := by exact prefixLift 2258815
  have htrace : WordTrace (prefixWord ++ tailWord_2258815) baseStart_2258815 baseEnd_2258815 := by
    simpa [prefixWord, tailWord_2258815, baseEnd_2258815] using wordTrace_append hprefix tailTrace_2258815
  have hstable : (prefixWord ++ tailWord_2258815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258815).length < 2 ^ (prefixWord ++ tailWord_2258815).sum := by decide
  have hdescent : baseEnd_2258815 < baseStart_2258815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258823 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 4]
def baseStart_2258823 : Nat := 118140960795 + 2258823 * 2 ^ 59
def prefixEnd_2258823 : Nat := 4983230072969 + 3 ^ 40 * 2258823 * 2
def baseEnd_2258823 : Nat := 257747091651315795183193

theorem tailTrace_2258823 : CollatzResearch.WordTrace tailWord_2258823 prefixEnd_2258823 257747091651315795183193 := by
  unfold tailWord_2258823
  simp only [CollatzResearch.WordTrace]
  refine ⟨82386043095677522100293123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54924028730451681400195415 82386043095677522100293123)
  ·
    refine ⟨123579064643516283150439685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82386043095677522100293123 123579064643516283150439685)
    ·
      refine ⟨23171074620659303090707441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123579064643516283150439685 23171074620659303090707441)
      ·
        refine ⟨17378305965494477318030581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23171074620659303090707441 17378305965494477318030581)
        ·
          refine ⟨1629216184265107248565367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17378305965494477318030581 1629216184265107248565367)
          ·
            refine ⟨2443824276397660872848051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629216184265107248565367 2443824276397660872848051)
            ·
              refine ⟨3665736414596491309272077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443824276397660872848051 3665736414596491309272077)
              ·
                refine ⟨1374651155473684240977029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665736414596491309272077 1374651155473684240977029)
                ·
                  refine ⟨257747091651315795183193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374651155473684240977029 257747091651315795183193)
                  ·
                    rfl

theorem cell22_2258823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 4].length) (baseStart_2258823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258823 prefixEnd_2258823 := by exact prefixLift 2258823
  have htrace : WordTrace (prefixWord ++ tailWord_2258823) baseStart_2258823 baseEnd_2258823 := by
    simpa [prefixWord, tailWord_2258823, baseEnd_2258823] using wordTrace_append hprefix tailTrace_2258823
  have hstable : (prefixWord ++ tailWord_2258823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258823).length < 2 ^ (prefixWord ++ tailWord_2258823).sum := by decide
  have hdescent : baseEnd_2258823 < baseStart_2258823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258832 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_2258832 : Nat := 118140960795 + 2258832 * 2 ^ 59
def prefixEnd_2258832 : Nat := 4983230072969 + 3 ^ 40 * 2258832 * 2
def baseEnd_2258832 : Nat := 773244355837874362074551

theorem tailTrace_2258832 : CollatzResearch.WordTrace tailWord_2258832 prefixEnd_2258832 773244355837874362074551 := by
  unfold tailWord_2258832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41193185676322458318685375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54924247568429944424913833 41193185676322458318685375)
  ·
    refine ⟨61789778514483687478028063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41193185676322458318685375 61789778514483687478028063)
    ·
      refine ⟨92684667771725531217042095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61789778514483687478028063 92684667771725531217042095)
      ·
        refine ⟨139027001657588296825563143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92684667771725531217042095 139027001657588296825563143)
        ·
          refine ⟨208540502486382445238344715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139027001657588296825563143 208540502486382445238344715)
          ·
            refine ⟨312810753729573667857517073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208540502486382445238344715 312810753729573667857517073)
            ·
              refine ⟨234608065297180250893137805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312810753729573667857517073 234608065297180250893137805)
              ·
                refine ⟨87978024486442594084926677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234608065297180250893137805 87978024486442594084926677)
                ·
                  refine ⟨2061984948900998298865469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87978024486442594084926677 2061984948900998298865469)
                  ·
                    refine ⟨773244355837874362074551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061984948900998298865469 773244355837874362074551)
                    ·
                      rfl

theorem cell22_2258832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_2258832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258832 prefixEnd_2258832 := by exact prefixLift 2258832
  have htrace : WordTrace (prefixWord ++ tailWord_2258832) baseStart_2258832 baseEnd_2258832 := by
    simpa [prefixWord, tailWord_2258832, baseEnd_2258832] using wordTrace_append hprefix tailTrace_2258832
  have hstable : (prefixWord ++ tailWord_2258832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258832).length < 2 ^ (prefixWord ++ tailWord_2258832).sum := by decide
  have hdescent : baseEnd_2258832 < baseStart_2258832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258834 : List Nat := [3, 2, 3, 2, 1, 3, 8]
def baseStart_2258834 : Nat := 118140960795 + 2258834 * 2 ^ 59
def prefixEnd_2258834 : Nat := 4983230072969 + 3 ^ 40 * 2258834 * 2
def baseEnd_2258834 : Nat := 28638705202916556426835

theorem tailTrace_2258834 : CollatzResearch.WordTrace tailWord_2258834 prefixEnd_2258834 28638705202916556426835 := by
  unfold tailWord_2258834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596611074659417744735889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54924296199091780652629037 20596611074659417744735889)
  ·
    refine ⟨15447458305994563308551917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20596611074659417744735889 15447458305994563308551917)
    ·
      refine ⟨5792796864747961240706969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15447458305994563308551917 5792796864747961240706969)
      ·
        refine ⟨4344597648560970930530227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792796864747961240706969 4344597648560970930530227)
        ·
          refine ⟨6516896472841456395795341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344597648560970930530227 6516896472841456395795341)
          ·
            refine ⟨2443836177315546148423253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6516896472841456395795341 2443836177315546148423253)
            ·
              refine ⟨28638705202916556426835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2443836177315546148423253 28638705202916556426835)
              ·
                rfl

theorem cell22_2258834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 8].length) (baseStart_2258834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258834 prefixEnd_2258834 := by exact prefixLift 2258834
  have htrace : WordTrace (prefixWord ++ tailWord_2258834) baseStart_2258834 baseEnd_2258834 := by
    simpa [prefixWord, tailWord_2258834, baseEnd_2258834] using wordTrace_append hprefix tailTrace_2258834
  have hstable : (prefixWord ++ tailWord_2258834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258834).length < 2 ^ (prefixWord ++ tailWord_2258834).sum := by decide
  have hdescent : baseEnd_2258834 < baseStart_2258834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258952 : List Nat := [2, 1, 3, 2, 1, 2, 11]
def baseStart_2258952 : Nat := 118140960795 + 2258952 * 2 ^ 59
def prefixEnd_2258952 : Nat := 4983230072969 + 3 ^ 40 * 2258952 * 2
def baseEnd_2258952 : Nat := 28640201270008668484229

theorem tailTrace_2258952 : CollatzResearch.WordTrace tailWord_2258952 prefixEnd_2258952 28640201270008668484229 := by
  unfold tailWord_2258952
  simp only [CollatzResearch.WordTrace]
  refine ⟨41195374056105088565869555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54927165408140118087826073 41195374056105088565869555)
  ·
    refine ⟨61793061084157632848804333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41195374056105088565869555 61793061084157632848804333)
    ·
      refine ⟨23172397906559112318301625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61793061084157632848804333 23172397906559112318301625)
      ·
        refine ⟨17379298429919334238726219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23172397906559112318301625 17379298429919334238726219)
        ·
          refine ⟨26068947644879001358089329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379298429919334238726219 26068947644879001358089329)
          ·
            refine ⟨19551710733659251018566997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26068947644879001358089329 19551710733659251018566997)
            ·
              refine ⟨28640201270008668484229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19551710733659251018566997 28640201270008668484229)
              ·
                rfl

theorem cell22_2258952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 11].length) (baseStart_2258952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258952 prefixEnd_2258952 := by exact prefixLift 2258952
  have htrace : WordTrace (prefixWord ++ tailWord_2258952) baseStart_2258952 baseEnd_2258952 := by
    simpa [prefixWord, tailWord_2258952, baseEnd_2258952] using wordTrace_append hprefix tailTrace_2258952
  have hstable : (prefixWord ++ tailWord_2258952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258952).length < 2 ^ (prefixWord ++ tailWord_2258952).sum := by decide
  have hdescent : baseEnd_2258952 < baseStart_2258952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2258986 : List Nat := [3, 1, 4, 1, 2, 1, 4, 6]
def baseStart_2258986 : Nat := 118140960795 + 2258986 * 2 ^ 59
def prefixEnd_2258986 : Nat := 4983230072969 + 3 ^ 40 * 2258986 * 2
def baseEnd_2258986 : Nat := 85921897020563254858231

theorem tailTrace_2258986 : CollatzResearch.WordTrace tailWord_2258986 prefixEnd_2258986 85921897020563254858231 := by
  unfold tailWord_2258986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20597997048521750234619203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54927992129391333958984541 20597997048521750234619203)
  ·
    refine ⟨30896995572782625351928805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20597997048521750234619203 30896995572782625351928805)
    ·
      refine ⟨5793186669896742253486651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30896995572782625351928805 5793186669896742253486651)
      ·
        refine ⟨8689780004845113380229977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793186669896742253486651 8689780004845113380229977)
        ·
          refine ⟨6517335003633835035172483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689780004845113380229977 6517335003633835035172483)
          ·
            refine ⟨9776002505450752552758725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6517335003633835035172483 9776002505450752552758725)
            ·
              refine ⟨1833000469772016103642261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9776002505450752552758725 1833000469772016103642261)
              ·
                refine ⟨85921897020563254858231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1833000469772016103642261 85921897020563254858231)
                ·
                  rfl

theorem cell22_2258986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_2258986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2258986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2258986 prefixEnd_2258986 := by exact prefixLift 2258986
  have htrace : WordTrace (prefixWord ++ tailWord_2258986) baseStart_2258986 baseEnd_2258986 := by
    simpa [prefixWord, tailWord_2258986, baseEnd_2258986] using wordTrace_append hprefix tailTrace_2258986
  have hstable : (prefixWord ++ tailWord_2258986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2258986).length < 2 ^ (prefixWord ++ tailWord_2258986).sum := by decide
  have hdescent : baseEnd_2258986 < baseStart_2258986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2258986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259031 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 5]
def baseStart_2259031 : Nat := 118140960795 + 2259031 * 2 ^ 59
def prefixEnd_2259031 : Nat := 4983230072969 + 3 ^ 40 * 2259031 * 2
def baseEnd_2259031 : Nat := 257770825868234725449647

theorem tailTrace_2259031 : CollatzResearch.WordTrace tailWord_2259031 prefixEnd_2259031 257770825868234725449647 := by
  unfold tailWord_2259031
  simp only [CollatzResearch.WordTrace]
  refine ⟨82393629478923973623864947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54929086319282649082576631 82393629478923973623864947)
  ·
    refine ⟨123590444218385960435797421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82393629478923973623864947 123590444218385960435797421)
    ·
      refine ⟨46346416581894735163424033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123590444218385960435797421 46346416581894735163424033)
      ·
        refine ⟨34759812436421051372568025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46346416581894735163424033 34759812436421051372568025)
        ·
          refine ⟨26069859327315788529426019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34759812436421051372568025 26069859327315788529426019)
          ·
            refine ⟨39104788990973682794139029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26069859327315788529426019 39104788990973682794139029)
            ·
              refine ⟨1833036983951891380975267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39104788990973682794139029 1833036983951891380975267)
              ·
                refine ⟨2749555475927837071462901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833036983951891380975267 2749555475927837071462901)
                ·
                  refine ⟨257770825868234725449647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749555475927837071462901 257770825868234725449647)
                  ·
                    rfl

theorem cell22_2259031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 5].length) (baseStart_2259031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259031 prefixEnd_2259031 := by exact prefixLift 2259031
  have htrace : WordTrace (prefixWord ++ tailWord_2259031) baseStart_2259031 baseEnd_2259031 := by
    simpa [prefixWord, tailWord_2259031, baseEnd_2259031] using wordTrace_append hprefix tailTrace_2259031
  have hstable : (prefixWord ++ tailWord_2259031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259031).length < 2 ^ (prefixWord ++ tailWord_2259031).sum := by decide
  have hdescent : baseEnd_2259031 < baseStart_2259031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259121 : List Nat := [1, 2, 2, 5, 2, 1, 9]
def baseStart_2259121 : Nat := 118140960795 + 2259121 * 2 ^ 59
def prefixEnd_2259121 : Nat := 4983230072969 + 3 ^ 40 * 2259121 * 2
def baseEnd_2259121 : Nat := 28642343942369405244395

theorem tailTrace_2259121 : CollatzResearch.WordTrace tailWord_2259121 prefixEnd_2259121 28642343942369405244395 := by
  unfold tailWord_2259121
  simp only [CollatzResearch.WordTrace]
  refine ⟨82396912048597918994641217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54931274699065279329760811 82396912048597918994641217)
  ·
    refine ⟨61797684036448439245980913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82396912048597918994641217 61797684036448439245980913)
    ·
      refine ⟨46348263027336329434485685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61797684036448439245980913 46348263027336329434485685)
      ·
        refine ⟨4345149658812780884483033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46348263027336329434485685 4345149658812780884483033)
        ·
          refine ⟨3258862244109585663362275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345149658812780884483033 3258862244109585663362275)
          ·
            refine ⟨4888293366164378495043413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258862244109585663362275 4888293366164378495043413)
            ·
              refine ⟨28642343942369405244395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4888293366164378495043413 28642343942369405244395)
              ·
                rfl

theorem cell22_2259121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 9].length) (baseStart_2259121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259121 prefixEnd_2259121 := by exact prefixLift 2259121
  have htrace : WordTrace (prefixWord ++ tailWord_2259121) baseStart_2259121 baseEnd_2259121 := by
    simpa [prefixWord, tailWord_2259121, baseEnd_2259121] using wordTrace_append hprefix tailTrace_2259121
  have hstable : (prefixWord ++ tailWord_2259121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259121).length < 2 ^ (prefixWord ++ tailWord_2259121).sum := by decide
  have hdescent : baseEnd_2259121 < baseStart_2259121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259125 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2259125 : Nat := 118140960795 + 2259125 * 2 ^ 59
def prefixEnd_2259125 : Nat := 4983230072969 + 3 ^ 40 * 2259125 * 2
def baseEnd_2259125 : Nat := 773344655725719264498653

theorem tailTrace_2259125 : CollatzResearch.WordTrace tailWord_2259125 prefixEnd_2259125 773344655725719264498653 := by
  unfold tailWord_2259125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82397057940583427677786829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54931371960388951785191219 82397057940583427677786829)
  ·
    refine ⟨30898896727718785379170061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82397057940583427677786829 30898896727718785379170061)
    ·
      refine ⟨11587086272894544517188773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30898896727718785379170061 11587086272894544517188773)
      ·
        refine ⟨2172578676167727096972895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11587086272894544517188773 2172578676167727096972895)
        ·
          refine ⟨3258868014251590645459343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172578676167727096972895 3258868014251590645459343)
          ·
            refine ⟨4888302021377385968189015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258868014251590645459343 4888302021377385968189015)
            ·
              refine ⟨7332453032066078952283523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888302021377385968189015 7332453032066078952283523)
              ·
                refine ⟨10998679548099118428425285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7332453032066078952283523 10998679548099118428425285)
                ·
                  refine ⟨2062252415268584705329741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10998679548099118428425285 2062252415268584705329741)
                  ·
                    refine ⟨773344655725719264498653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062252415268584705329741 773344655725719264498653)
                    ·
                      rfl

theorem cell22_2259125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2259125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259125 prefixEnd_2259125 := by exact prefixLift 2259125
  have htrace : WordTrace (prefixWord ++ tailWord_2259125) baseStart_2259125 baseEnd_2259125 := by
    simpa [prefixWord, tailWord_2259125, baseEnd_2259125] using wordTrace_append hprefix tailTrace_2259125
  have hstable : (prefixWord ++ tailWord_2259125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259125).length < 2 ^ (prefixWord ++ tailWord_2259125).sum := by decide
  have hdescent : baseEnd_2259125 < baseStart_2259125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259228 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_2259228 : Nat := 118140960795 + 2259228 * 2 ^ 59
def prefixEnd_2259228 : Nat := 4983230072969 + 3 ^ 40 * 2259228 * 2
def baseEnd_2259228 : Nat := 257793304910220443057779

theorem tailTrace_2259228 : CollatzResearch.WordTrace tailWord_2259228 prefixEnd_2259228 257793304910220443057779 := by
  unfold tailWord_2259228
  simp only [CollatzResearch.WordTrace]
  refine ⟨41200407329605138134393169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54933876439473517512524225 41200407329605138134393169)
  ·
    refine ⟨30900305497203853600794877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41200407329605138134393169 30900305497203853600794877)
    ·
      refine ⟨11587614561451445100298079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30900305497203853600794877 11587614561451445100298079)
      ·
        refine ⟨17381421842177167650447119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587614561451445100298079 17381421842177167650447119)
        ·
          refine ⟨26072132763265751475670679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17381421842177167650447119 26072132763265751475670679)
          ·
            refine ⟨39108199144898627213506019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26072132763265751475670679 39108199144898627213506019)
            ·
              refine ⟨58662298717347940820259029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39108199144898627213506019 58662298717347940820259029)
              ·
                refine ⟨1374897626187842362974821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58662298717347940820259029 1374897626187842362974821)
                ·
                  refine ⟨257793304910220443057779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374897626187842362974821 257793304910220443057779)
                  ·
                    rfl

theorem cell22_2259228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_2259228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259228 prefixEnd_2259228 := by exact prefixLift 2259228
  have htrace : WordTrace (prefixWord ++ tailWord_2259228) baseStart_2259228 baseEnd_2259228 := by
    simpa [prefixWord, tailWord_2259228, baseEnd_2259228] using wordTrace_append hprefix tailTrace_2259228
  have hstable : (prefixWord ++ tailWord_2259228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259228).length < 2 ^ (prefixWord ++ tailWord_2259228).sum := by decide
  have hdescent : baseEnd_2259228 < baseStart_2259228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259256 : List Nat := [2, 1, 2, 1, 3, 1, 5, 7]
def baseStart_2259256 : Nat := 118140960795 + 2259256 * 2 ^ 59
def prefixEnd_2259256 : Nat := 4983230072969 + 3 ^ 40 * 2259256 * 2
def baseEnd_2259256 : Nat := 85932166633653176608139

theorem tailTrace_2259256 : CollatzResearch.WordTrace tailWord_2259256 prefixEnd_2259256 85932166633653176608139 := by
  unfold tailWord_2259256
  simp only [CollatzResearch.WordTrace]
  refine ⟨41200917951554418525402811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54934557268739224700537081 41200917951554418525402811)
  ·
    refine ⟨61801376927331627788104217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41200917951554418525402811 61801376927331627788104217)
    ·
      refine ⟨46351032695498720841078163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61801376927331627788104217 46351032695498720841078163)
      ·
        refine ⟨69526549043248081261617245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46351032695498720841078163 69526549043248081261617245)
        ·
          refine ⟨26072455891218030473106467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69526549043248081261617245 26072455891218030473106467)
          ·
            refine ⟨39108683836827045709659701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26072455891218030473106467 39108683836827045709659701)
            ·
              refine ⟨3666439109702535535280597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39108683836827045709659701 3666439109702535535280597)
              ·
                refine ⟨85932166633653176608139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3666439109702535535280597 85932166633653176608139)
                ·
                  rfl

theorem cell22_2259256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_2259256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259256 prefixEnd_2259256 := by exact prefixLift 2259256
  have htrace : WordTrace (prefixWord ++ tailWord_2259256) baseStart_2259256 baseEnd_2259256 := by
    simpa [prefixWord, tailWord_2259256, baseEnd_2259256] using wordTrace_append hprefix tailTrace_2259256
  have hstable : (prefixWord ++ tailWord_2259256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259256).length < 2 ^ (prefixWord ++ tailWord_2259256).sum := by decide
  have hdescent : baseEnd_2259256 < baseStart_2259256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259305 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 1, 3]
def baseStart_2259305 : Nat := 118140960795 + 2259305 * 2 ^ 59
def prefixEnd_2259305 : Nat := 4983230072969 + 3 ^ 40 * 2259305 * 2
def baseEnd_2259305 : Nat := 773406273404258794998101

theorem tailTrace_2259305 : CollatzResearch.WordTrace tailWord_2259305 prefixEnd_2259305 773406273404258794998101 := by
  unfold tailWord_2259305
  simp only [CollatzResearch.WordTrace]
  refine ⟨82403623079931318419339369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54935748719954212279559579 82403623079931318419339369)
  ·
    refine ⟨61802717309948488814504527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82403623079931318419339369 61802717309948488814504527)
    ·
      refine ⟨92704075964922733221756791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61802717309948488814504527 92704075964922733221756791)
      ·
        refine ⟨139056113947384099832635187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92704075964922733221756791 139056113947384099832635187)
        ·
          refine ⟨208584170921076149748952781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139056113947384099832635187 208584170921076149748952781)
          ·
            refine ⟨78219064095403556155857293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208584170921076149748952781 78219064095403556155857293)
            ·
              refine ⟨29332149035776333558446485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78219064095403556155857293 29332149035776333558446485)
              ·
                refine ⟨1374944486052015635552179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29332149035776333558446485 1374944486052015635552179)
                ·
                  refine ⟨2062416729078023453328269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374944486052015635552179 2062416729078023453328269)
                  ·
                    refine ⟨773406273404258794998101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062416729078023453328269 773406273404258794998101)
                    ·
                      rfl

theorem cell22_2259305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_2259305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259305 prefixEnd_2259305 := by exact prefixLift 2259305
  have htrace : WordTrace (prefixWord ++ tailWord_2259305) baseStart_2259305 baseEnd_2259305 := by
    simpa [prefixWord, tailWord_2259305, baseEnd_2259305] using wordTrace_append hprefix tailTrace_2259305
  have hstable : (prefixWord ++ tailWord_2259305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259305).length < 2 ^ (prefixWord ++ tailWord_2259305).sum := by decide
  have hdescent : baseEnd_2259305 < baseStart_2259305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259363 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 6]
def baseStart_2259363 : Nat := 118140960795 + 2259363 * 2 ^ 59
def prefixEnd_2259363 : Nat := 4983230072969 + 3 ^ 40 * 2259363 * 2
def baseEnd_2259363 : Nat := 257808709329855325682641

theorem tailTrace_2259363 : CollatzResearch.WordTrace tailWord_2259363 prefixEnd_2259363 257808709329855325682641 := by
  unfold tailWord_2259363
  simp only [CollatzResearch.WordTrace]
  refine ⟨82405738513721194324950743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54937159009147462883300495 82405738513721194324950743)
  ·
    refine ⟨123608607770581791487426115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82405738513721194324950743 123608607770581791487426115)
    ·
      refine ⟨185412911655872687231139173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123608607770581791487426115 185412911655872687231139173)
      ·
        refine ⟨34764920935476128855838595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185412911655872687231139173 34764920935476128855838595)
        ·
          refine ⟨52147381403214193283757893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34764920935476128855838595 52147381403214193283757893)
          ·
            refine ⟨9777634013102661240704605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52147381403214193283757893 9777634013102661240704605)
            ·
              refine ⟨3666612754913497965264227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9777634013102661240704605 3666612754913497965264227)
              ·
                refine ⟨5499919132370246947896341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666612754913497965264227 5499919132370246947896341)
                ·
                  refine ⟨257808709329855325682641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5499919132370246947896341 257808709329855325682641)
                  ·
                    rfl

theorem cell22_2259363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_2259363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259363 prefixEnd_2259363 := by exact prefixLift 2259363
  have htrace : WordTrace (prefixWord ++ tailWord_2259363) baseStart_2259363 baseEnd_2259363 := by
    simpa [prefixWord, tailWord_2259363, baseEnd_2259363] using wordTrace_append hprefix tailTrace_2259363
  have hstable : (prefixWord ++ tailWord_2259363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259363).length < 2 ^ (prefixWord ++ tailWord_2259363).sum := by decide
  have hdescent : baseEnd_2259363 < baseStart_2259363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259378 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2259378 : Nat := 118140960795 + 2259378 * 2 ^ 59
def prefixEnd_2259378 : Nat := 4983230072969 + 3 ^ 40 * 2259378 * 2
def baseEnd_2259378 : Nat := 773431262796110937922877

theorem tailTrace_2259378 : CollatzResearch.WordTrace tailWord_2259378 prefixEnd_2259378 773431262796110937922877 := by
  unfold tailWord_2259378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601571402166712971686697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54937523739111234591164525 20601571402166712971686697)
  ·
    refine ⟨15451178551625034728765023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20601571402166712971686697 15451178551625034728765023)
    ·
      refine ⟨23176767827437552093147535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451178551625034728765023 23176767827437552093147535)
      ·
        refine ⟨34765151741156328139721303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23176767827437552093147535 34765151741156328139721303)
        ·
          refine ⟨52147727611734492209581955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34765151741156328139721303 52147727611734492209581955)
          ·
            refine ⟨78221591417601738314372933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52147727611734492209581955 78221591417601738314372933)
            ·
              refine ⟨14666548390800325933944925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78221591417601738314372933 14666548390800325933944925)
              ·
                refine ⟨5499955646550122225229347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14666548390800325933944925 5499955646550122225229347)
                ·
                  refine ⟨8249933469825183337844021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5499955646550122225229347 8249933469825183337844021)
                  ·
                    refine ⟨773431262796110937922877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8249933469825183337844021 773431262796110937922877)
                    ·
                      rfl

theorem cell22_2259378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2259378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259378 prefixEnd_2259378 := by exact prefixLift 2259378
  have htrace : WordTrace (prefixWord ++ tailWord_2259378) baseStart_2259378 baseEnd_2259378 := by
    simpa [prefixWord, tailWord_2259378, baseEnd_2259378] using wordTrace_append hprefix tailTrace_2259378
  have hstable : (prefixWord ++ tailWord_2259378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259378).length < 2 ^ (prefixWord ++ tailWord_2259378).sum := by decide
  have hdescent : baseEnd_2259378 < baseStart_2259378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259412 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2259412 : Nat := 118140960795 + 2259412 * 2 ^ 59
def prefixEnd_2259412 : Nat := 4983230072969 + 3 ^ 40 * 2259412 * 2
def baseEnd_2259412 : Nat := 773442901690946182572773

theorem tailTrace_2259412 : CollatzResearch.WordTrace tailWord_2259412 prefixEnd_2259412 773442901690946182572773 := by
  unfold tailWord_2259412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41203762845271837846742245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54938350460362450462322993 41203762845271837846742245)
  ·
    refine ⟨7725705533488469596264171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41203762845271837846742245 7725705533488469596264171)
    ·
      refine ⟨11588558300232704394396257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7725705533488469596264171 11588558300232704394396257)
      ·
        refine ⟨8691418725174528295797193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11588558300232704394396257 8691418725174528295797193)
        ·
          refine ⟨6518564043880896221847895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8691418725174528295797193 6518564043880896221847895)
          ·
            refine ⟨9777846065821344332771843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518564043880896221847895 9777846065821344332771843)
            ·
              refine ⟨14666769098732016499157765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9777846065821344332771843 14666769098732016499157765)
              ·
                refine ⟨2750019206012253093592081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14666769098732016499157765 2750019206012253093592081)
                ·
                  refine ⟨2062514404509189820194061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750019206012253093592081 2062514404509189820194061)
                  ·
                    refine ⟨773442901690946182572773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062514404509189820194061 773442901690946182572773)
                    ·
                      rfl

theorem cell22_2259412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2259412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259412 prefixEnd_2259412 := by exact prefixLift 2259412
  have htrace : WordTrace (prefixWord ++ tailWord_2259412) baseStart_2259412 baseEnd_2259412 := by
    simpa [prefixWord, tailWord_2259412, baseEnd_2259412] using wordTrace_append hprefix tailTrace_2259412
  have hstable : (prefixWord ++ tailWord_2259412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259412).length < 2 ^ (prefixWord ++ tailWord_2259412).sum := by decide
  have hdescent : baseEnd_2259412 < baseStart_2259412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259440 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_2259440 : Nat := 118140960795 + 2259440 * 2 ^ 59
def prefixEnd_2259440 : Nat := 4983230072969 + 3 ^ 40 * 2259440 * 2
def baseEnd_2259440 : Nat := 773452486663163442872687

theorem tailTrace_2259440 : CollatzResearch.WordTrace tailWord_2259440 prefixEnd_2259440 773452486663163442872687 := by
  unfold tailWord_2259440
  simp only [CollatzResearch.WordTrace]
  refine ⟨41204273467221118237751887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54939031289628157650335849 41204273467221118237751887)
  ·
    refine ⟨61806410200831677356627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41204273467221118237751887 61806410200831677356627831)
    ·
      refine ⟨92709615301247516034941747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61806410200831677356627831 92709615301247516034941747)
      ·
        refine ⟨139064422951871274052412621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92709615301247516034941747 139064422951871274052412621)
        ·
          refine ⟨52149158606951727769654733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139064422951871274052412621 52149158606951727769654733)
          ·
            refine ⟨19555934477606897913620525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52149158606951727769654733 19555934477606897913620525)
            ·
              refine ⟨7333475429102586717607697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19555934477606897913620525 7333475429102586717607697)
              ·
                refine ⟨5500106571826940038205773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7333475429102586717607697 5500106571826940038205773)
                ·
                  refine ⟨2062539964435102514327165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5500106571826940038205773 2062539964435102514327165)
                  ·
                    refine ⟨773452486663163442872687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062539964435102514327165 773452486663163442872687)
                    ·
                      rfl

theorem cell22_2259440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_2259440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259440 prefixEnd_2259440 := by exact prefixLift 2259440
  have htrace : WordTrace (prefixWord ++ tailWord_2259440) baseStart_2259440 baseEnd_2259440 := by
    simpa [prefixWord, tailWord_2259440, baseEnd_2259440] using wordTrace_append hprefix tailTrace_2259440
  have hstable : (prefixWord ++ tailWord_2259440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259440).length < 2 ^ (prefixWord ++ tailWord_2259440).sum := by decide
  have hdescent : baseEnd_2259440 < baseStart_2259440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259442 : List Nat := [3, 2, 1, 4, 2, 1, 3, 6]
def baseStart_2259442 : Nat := 118140960795 + 2259442 * 2 ^ 59
def prefixEnd_2259442 : Nat := 4983230072969 + 3 ^ 40 * 2259442 * 2
def baseEnd_2259442 : Nat := 85939241256004011591409

theorem tailTrace_2259442 : CollatzResearch.WordTrace tailWord_2259442 prefixEnd_2259442 85939241256004011591409 := by
  unfold tailWord_2259442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20602154970108747704269145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54939079920289993878051053 20602154970108747704269145)
  ·
    refine ⟨15451616227581560778201859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20602154970108747704269145 15451616227581560778201859)
    ·
      refine ⟨23177424341372341167302789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451616227581560778201859 23177424341372341167302789)
      ·
        refine ⟨4345767064007313968869273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23177424341372341167302789 4345767064007313968869273)
        ·
          refine ⟨3259325298005485476651955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345767064007313968869273 3259325298005485476651955)
          ·
            refine ⟨4888987947008228214977933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259325298005485476651955 4888987947008228214977933)
            ·
              refine ⟨1833370480128085580616725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4888987947008228214977933 1833370480128085580616725)
              ·
                refine ⟨85939241256004011591409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1833370480128085580616725 85939241256004011591409)
                ·
                  rfl

theorem cell22_2259442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_2259442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259442 prefixEnd_2259442 := by exact prefixLift 2259442
  have htrace : WordTrace (prefixWord ++ tailWord_2259442) baseStart_2259442 baseEnd_2259442 := by
    simpa [prefixWord, tailWord_2259442, baseEnd_2259442] using wordTrace_append hprefix tailTrace_2259442
  have hstable : (prefixWord ++ tailWord_2259442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259442).length < 2 ^ (prefixWord ++ tailWord_2259442).sum := by decide
  have hdescent : baseEnd_2259442 < baseStart_2259442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259453 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2259453 : Nat := 118140960795 + 2259453 * 2 ^ 59
def prefixEnd_2259453 : Nat := 4983230072969 + 3 ^ 40 * 2259453 * 2
def baseEnd_2259453 : Nat := 257818978942945247432549

theorem tailTrace_2259453 : CollatzResearch.WordTrace tailWord_2259453 prefixEnd_2259453 257818978942945247432549 := by
  unfold tailWord_2259453
  simp only [CollatzResearch.WordTrace]
  refine ⟨82409021083395139695727013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54939347388930093130484675 82409021083395139695727013)
  ·
    refine ⟨15451691453136588692948815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82409021083395139695727013 15451691453136588692948815)
    ·
      refine ⟨23177537179704883039423223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451691453136588692948815 23177537179704883039423223)
      ·
        refine ⟨34766305769557324559134835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23177537179704883039423223 34766305769557324559134835)
        ·
          refine ⟨52149458654335986838702253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34766305769557324559134835 52149458654335986838702253)
          ·
            refine ⟨19556046995375995064513345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52149458654335986838702253 19556046995375995064513345)
            ·
              refine ⟨14667035246531996298385009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19556046995375995064513345 14667035246531996298385009)
              ·
                refine ⟨11000276434898997223788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14667035246531996298385009 11000276434898997223788757)
                ·
                  refine ⟨257818978942945247432549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11000276434898997223788757 257818978942945247432549)
                  ·
                    rfl

theorem cell22_2259453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2259453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259453 prefixEnd_2259453 := by exact prefixLift 2259453
  have htrace : WordTrace (prefixWord ++ tailWord_2259453) baseStart_2259453 baseEnd_2259453 := by
    simpa [prefixWord, tailWord_2259453, baseEnd_2259453] using wordTrace_append hprefix tailTrace_2259453
  have hstable : (prefixWord ++ tailWord_2259453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259453).length < 2 ^ (prefixWord ++ tailWord_2259453).sum := by decide
  have hdescent : baseEnd_2259453 < baseStart_2259453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259470 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2259470 : Nat := 118140960795 + 2259470 * 2 ^ 59
def prefixEnd_2259470 : Nat := 4983230072969 + 3 ^ 40 * 2259470 * 2
def baseEnd_2259470 : Nat := 257820918758751121540865

theorem tailTrace_2259470 : CollatzResearch.WordTrace tailWord_2259470 prefixEnd_2259470 257820918758751121540865 := by
  unfold tailWord_2259470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301205140541693949886983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54939760749555701066063909 10301205140541693949886983)
  ·
    refine ⟨15451807710812540924830475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10301205140541693949886983 15451807710812540924830475)
    ·
      refine ⟨23177711566218811387245713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15451807710812540924830475 23177711566218811387245713)
      ·
        refine ⟨17383283674664108540434285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23177711566218811387245713 17383283674664108540434285)
        ·
          refine ⟨6518731377999040702662857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17383283674664108540434285 6518731377999040702662857)
          ·
            refine ⟨4889048533499280526997143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6518731377999040702662857 4889048533499280526997143)
            ·
              refine ⟨7333572800248920790495715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889048533499280526997143 7333572800248920790495715)
              ·
                refine ⟨11000359200373381185743573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333572800248920790495715 11000359200373381185743573)
                ·
                  refine ⟨257820918758751121540865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11000359200373381185743573 257820918758751121540865)
                  ·
                    rfl

theorem cell22_2259470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2259470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259470 prefixEnd_2259470 := by exact prefixLift 2259470
  have htrace : WordTrace (prefixWord ++ tailWord_2259470) baseStart_2259470 baseEnd_2259470 := by
    simpa [prefixWord, tailWord_2259470, baseEnd_2259470] using wordTrace_append hprefix tailTrace_2259470
  have hstable : (prefixWord ++ tailWord_2259470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259470).length < 2 ^ (prefixWord ++ tailWord_2259470).sum := by decide
  have hdescent : baseEnd_2259470 < baseStart_2259470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259485 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2259485 : Nat := 118140960795 + 2259485 * 2 ^ 59
def prefixEnd_2259485 : Nat := 4983230072969 + 3 ^ 40 * 2259485 * 2
def baseEnd_2259485 : Nat := 773467891082798325497549

theorem tailTrace_2259485 : CollatzResearch.WordTrace tailWord_2259485 prefixEnd_2259485 773467891082798325497549 := by
  unfold tailWord_2259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨82410188219279209160891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54940125479519472773927939 82410188219279209160891909)
  ·
    refine ⟨15451910291114851717667233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82410188219279209160891909 15451910291114851717667233)
    ·
      refine ⟨11588932718336138788250425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15451910291114851717667233 11588932718336138788250425)
      ·
        refine ⟨8691699538752104091187819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11588932718336138788250425 8691699538752104091187819)
        ·
          refine ⟨13037549308128156136781729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691699538752104091187819 13037549308128156136781729)
          ·
            refine ⟨9778161981096117102586297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13037549308128156136781729 9778161981096117102586297)
            ·
              refine ⟨7333621485822087826939723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778161981096117102586297 7333621485822087826939723)
              ·
                refine ⟨11000432228733131740409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7333621485822087826939723 11000432228733131740409585)
                ·
                  refine ⟨8250324171549848805307189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11000432228733131740409585 8250324171549848805307189)
                  ·
                    refine ⟨773467891082798325497549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8250324171549848805307189 773467891082798325497549)
                    ·
                      rfl

theorem cell22_2259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2259485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259485 prefixEnd_2259485 := by exact prefixLift 2259485
  have htrace : WordTrace (prefixWord ++ tailWord_2259485) baseStart_2259485 baseEnd_2259485 := by
    simpa [prefixWord, tailWord_2259485, baseEnd_2259485] using wordTrace_append hprefix tailTrace_2259485
  have hstable : (prefixWord ++ tailWord_2259485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259485).length < 2 ^ (prefixWord ++ tailWord_2259485).sum := by decide
  have hdescent : baseEnd_2259485 < baseStart_2259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259517 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2259517 : Nat := 118140960795 + 2259517 * 2 ^ 59
def prefixEnd_2259517 : Nat := 4983230072969 + 3 ^ 40 * 2259517 * 2
def baseEnd_2259517 : Nat := 773478845336760908697451

theorem tailTrace_2259517 : CollatzResearch.WordTrace tailWord_2259517 prefixEnd_2259517 773478845336760908697451 := by
  unfold tailWord_2259517
  simp only [CollatzResearch.WordTrace]
  refine ⟨82411355355163278626056805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54940903570108852417371203 82411355355163278626056805)
  ·
    refine ⟨15452129129093114742385651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82411355355163278626056805 15452129129093114742385651)
    ·
      refine ⟨23178193693639672113578477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15452129129093114742385651 23178193693639672113578477)
      ·
        refine ⟨8691822635114877042591929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23178193693639672113578477 8691822635114877042591929)
        ·
          refine ⟨6518866976336157781943947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8691822635114877042591929 6518866976336157781943947)
          ·
            refine ⟨9778300464504236672915921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518866976336157781943947 9778300464504236672915921)
            ·
              refine ⟨7333725348378177504686941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778300464504236672915921 7333725348378177504686941)
              ·
                refine ⟨2750147005641816564257603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7333725348378177504686941 2750147005641816564257603)
                ·
                  refine ⟨4125220508462724846386405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750147005641816564257603 4125220508462724846386405)
                  ·
                    refine ⟨773478845336760908697451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125220508462724846386405 773478845336760908697451)
                    ·
                      rfl

theorem cell22_2259517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2259517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259517 prefixEnd_2259517 := by exact prefixLift 2259517
  have htrace : WordTrace (prefixWord ++ tailWord_2259517) baseStart_2259517 baseEnd_2259517 := by
    simpa [prefixWord, tailWord_2259517, baseEnd_2259517] using wordTrace_append hprefix tailTrace_2259517
  have hstable : (prefixWord ++ tailWord_2259517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259517).length < 2 ^ (prefixWord ++ tailWord_2259517).sum := by decide
  have hdescent : baseEnd_2259517 < baseStart_2259517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259562 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2259562 : Nat := 118140960795 + 2259562 * 2 ^ 59
def prefixEnd_2259562 : Nat := 4983230072969 + 3 ^ 40 * 2259562 * 2
def baseEnd_2259562 : Nat := 773494249756395791322313

theorem tailTrace_2259562 : CollatzResearch.WordTrace tailWord_2259562 prefixEnd_2259562 773494249756395791322313 := by
  unfold tailWord_2259562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603249160000062827861235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54941997760000167540963293 20603249160000062827861235)
  ·
    refine ⟨30904873740000094241791853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20603249160000062827861235 30904873740000094241791853)
    ·
      refine ⟨11589327652500035340671945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30904873740000094241791853 11589327652500035340671945)
      ·
        refine ⟨8691995739375026505503959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11589327652500035340671945 8691995739375026505503959)
        ·
          refine ⟨13037993609062539758255939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8691995739375026505503959 13037993609062539758255939)
          ·
            refine ⟨19556990413593809637383909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13037993609062539758255939 19556990413593809637383909)
            ·
              refine ⟨3666935702548839307009483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19556990413593809637383909 3666935702548839307009483)
              ·
                refine ⟨5500403553823258960514225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666935702548839307009483 5500403553823258960514225)
                ·
                  refine ⟨4125302665367444220385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500403553823258960514225 4125302665367444220385669)
                  ·
                    refine ⟨773494249756395791322313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125302665367444220385669 773494249756395791322313)
                    ·
                      rfl

theorem cell22_2259562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2259562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259562 prefixEnd_2259562 := by exact prefixLift 2259562
  have htrace : WordTrace (prefixWord ++ tailWord_2259562) baseStart_2259562 baseEnd_2259562 := by
    simpa [prefixWord, tailWord_2259562, baseEnd_2259562] using wordTrace_append hprefix tailTrace_2259562
  have hstable : (prefixWord ++ tailWord_2259562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259562).length < 2 ^ (prefixWord ++ tailWord_2259562).sum := by decide
  have hdescent : baseEnd_2259562 < baseStart_2259562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259594 : List Nat := [3, 1, 2, 3, 4, 1, 1, 7]
def baseStart_2259594 : Nat := 118140960795 + 2259594 * 2 ^ 59
def prefixEnd_2259594 : Nat := 4983230072969 + 3 ^ 40 * 2259594 * 2
def baseEnd_2259594 : Nat := 85945022667817597169135

theorem tailTrace_2259594 : CollatzResearch.WordTrace tailWord_2259594 prefixEnd_2259594 85945022667817597169135 := by
  unfold tailWord_2259594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603540943971080194152459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54942775850589547184406557 20603540943971080194152459)
  ·
    refine ⟨30905311415956620291228689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20603540943971080194152459 30905311415956620291228689)
    ·
      refine ⟨23178983561967465218421517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30905311415956620291228689 23178983561967465218421517)
      ·
        refine ⟨8692118835737799456908069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23178983561967465218421517 8692118835737799456908069)
        ·
          refine ⟨1629772281700837398170263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8692118835737799456908069 1629772281700837398170263)
          ·
            refine ⟨2444658422551256097255395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629772281700837398170263 2444658422551256097255395)
            ·
              refine ⟨3666987633826884145883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444658422551256097255395 3666987633826884145883093)
              ·
                refine ⟨85945022667817597169135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3666987633826884145883093 85945022667817597169135)
                ·
                  rfl

theorem cell22_2259594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_2259594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259594 prefixEnd_2259594 := by exact prefixLift 2259594
  have htrace : WordTrace (prefixWord ++ tailWord_2259594) baseStart_2259594 baseEnd_2259594 := by
    simpa [prefixWord, tailWord_2259594, baseEnd_2259594] using wordTrace_append hprefix tailTrace_2259594
  have hstable : (prefixWord ++ tailWord_2259594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259594).length < 2 ^ (prefixWord ++ tailWord_2259594).sum := by decide
  have hdescent : baseEnd_2259594 < baseStart_2259594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259620 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2259620 : Nat := 118140960795 + 2259620 * 2 ^ 59
def prefixEnd_2259620 : Nat := 4983230072969 + 3 ^ 40 * 2259620 * 2
def baseEnd_2259620 : Nat := 773514104341702973372135

theorem tailTrace_2259620 : CollatzResearch.WordTrace tailWord_2259620 prefixEnd_2259620 773514104341702973372135 := by
  unfold tailWord_2259620
  simp only [CollatzResearch.WordTrace]
  refine ⟨41207556036895063608528157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54943408049193418144704209 41207556036895063608528157)
  ·
    refine ⟨15452833513835648853198059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41207556036895063608528157 15452833513835648853198059)
    ·
      refine ⟨23179250270753473279797089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15452833513835648853198059 23179250270753473279797089)
      ·
        refine ⟨17384437703065104959847817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23179250270753473279797089 17384437703065104959847817)
        ·
          refine ⟨13038328277298828719885863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17384437703065104959847817 13038328277298828719885863)
          ·
            refine ⟨19557492415948243079828795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13038328277298828719885863 19557492415948243079828795)
            ·
              refine ⟨29336238623922364619743193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19557492415948243079828795 29336238623922364619743193)
              ·
                refine ⟨22002178967941773464807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29336238623922364619743193 22002178967941773464807395)
                ·
                  refine ⟨33003268451912660197211093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22002178967941773464807395 33003268451912660197211093)
                  ·
                    refine ⟨773514104341702973372135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33003268451912660197211093 773514104341702973372135)
                    ·
                      rfl

theorem cell22_2259620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2259620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259620 prefixEnd_2259620 := by exact prefixLift 2259620
  have htrace : WordTrace (prefixWord ++ tailWord_2259620) baseStart_2259620 baseEnd_2259620 := by
    simpa [prefixWord, tailWord_2259620, baseEnd_2259620] using wordTrace_append hprefix tailTrace_2259620
  have hstable : (prefixWord ++ tailWord_2259620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259620).length < 2 ^ (prefixWord ++ tailWord_2259620).sum := by decide
  have hdescent : baseEnd_2259620 < baseStart_2259620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259637 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2259637 : Nat := 118140960795 + 2259637 * 2 ^ 59
def prefixEnd_2259637 : Nat := 4983230072969 + 3 ^ 40 * 2259637 * 2
def baseEnd_2259637 : Nat := 773519923789120595697083

theorem tailTrace_2259637 : CollatzResearch.WordTrace tailWord_2259637 prefixEnd_2259637 773519923789120595697083 := by
  unfold tailWord_2259637
  simp only [CollatzResearch.WordTrace]
  refine ⟨82415732114728539120425165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54943821409819026080283443 82415732114728539120425165)
  ·
    refine ⟨30905899543023202170159437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82415732114728539120425165 30905899543023202170159437)
    ·
      refine ⟨11589712328633700813809789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30905899543023202170159437 11589712328633700813809789)
      ·
        refine ⟨4346142123237637805178671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11589712328633700813809789 4346142123237637805178671)
        ·
          refine ⟨6519213184856456707768007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346142123237637805178671 6519213184856456707768007)
          ·
            refine ⟨9778819777284685061652011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6519213184856456707768007 9778819777284685061652011)
            ·
              refine ⟨14668229665927027592478017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9778819777284685061652011 14668229665927027592478017)
              ·
                refine ⟨11001172249445270694358513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14668229665927027592478017 11001172249445270694358513)
                ·
                  refine ⟨8250879187083953020768885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11001172249445270694358513 8250879187083953020768885)
                  ·
                    refine ⟨773519923789120595697083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8250879187083953020768885 773519923789120595697083)
                    ·
                      rfl

theorem cell22_2259637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2259637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259637 prefixEnd_2259637 := by exact prefixLift 2259637
  have htrace : WordTrace (prefixWord ++ tailWord_2259637) baseStart_2259637 baseEnd_2259637 := by
    simpa [prefixWord, tailWord_2259637, baseEnd_2259637] using wordTrace_append hprefix tailTrace_2259637
  have hstable : (prefixWord ++ tailWord_2259637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259637).length < 2 ^ (prefixWord ++ tailWord_2259637).sum := by decide
  have hdescent : baseEnd_2259637 < baseStart_2259637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259639 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 5]
def baseStart_2259639 : Nat := 118140960795 + 2259639 * 2 ^ 59
def prefixEnd_2259639 : Nat := 4983230072969 + 3 ^ 40 * 2259639 * 2
def baseEnd_2259639 : Nat := 257840202809997752382359

theorem tailTrace_2259639 : CollatzResearch.WordTrace tailWord_2259639 prefixEnd_2259639 257840202809997752382359 := by
  unfold tailWord_2259639
  simp only [CollatzResearch.WordTrace]
  refine ⟨82415805060721293461997971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54943870040480862307998647 82415805060721293461997971)
  ·
    refine ⟨123623707591081940192996957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82415805060721293461997971 123623707591081940192996957)
    ·
      refine ⟨46358890346655727572373859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123623707591081940192996957 46358890346655727572373859)
      ·
        refine ⟨69538335519983591358560789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46358890346655727572373859 69538335519983591358560789)
        ·
          refine ⟨3259609477499230844932537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69538335519983591358560789 3259609477499230844932537)
          ·
            refine ⟨2444707108124423133699403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3259609477499230844932537 2444707108124423133699403)
            ·
              refine ⟨3667060662186634700549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444707108124423133699403 3667060662186634700549105)
              ·
                refine ⟨2750295496639976025411829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3667060662186634700549105 2750295496639976025411829)
                ·
                  refine ⟨257840202809997752382359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2750295496639976025411829 257840202809997752382359)
                  ·
                    rfl

theorem cell22_2259639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 5].length) (baseStart_2259639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259639 prefixEnd_2259639 := by exact prefixLift 2259639
  have htrace : WordTrace (prefixWord ++ tailWord_2259639) baseStart_2259639 baseEnd_2259639 := by
    simpa [prefixWord, tailWord_2259639, baseEnd_2259639] using wordTrace_append hprefix tailTrace_2259639
  have hstable : (prefixWord ++ tailWord_2259639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259639).length < 2 ^ (prefixWord ++ tailWord_2259639).sum := by decide
  have hdescent : baseEnd_2259639 < baseStart_2259639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259684 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2259684 : Nat := 118140960795 + 2259684 * 2 ^ 59
def prefixEnd_2259684 : Nat := 4983230072969 + 3 ^ 40 * 2259684 * 2
def baseEnd_2259684 : Nat := 257845337616542713257313

theorem tailTrace_2259684 : CollatzResearch.WordTrace tailWord_2259684 prefixEnd_2259684 257845337616542713257313 := by
  unfold tailWord_2259684
  simp only [CollatzResearch.WordTrace]
  refine ⟨41208723172779133073693053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54944964230372177431590737 41208723172779133073693053)
  ·
    refine ⟨15453271189792174902634895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41208723172779133073693053 15453271189792174902634895)
    ·
      refine ⟨23179906784688262353952343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15453271189792174902634895 23179906784688262353952343)
      ·
        refine ⟨34769860177032393530928515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23179906784688262353952343 34769860177032393530928515)
        ·
          refine ⟨52154790265548590296392773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34769860177032393530928515 52154790265548590296392773)
          ·
            refine ⟨9779023174790360680573645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52154790265548590296392773 9779023174790360680573645)
            ·
              refine ⟨3667133690546385255215117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9779023174790360680573645 3667133690546385255215117)
              ·
                refine ⟨1375175133954894470705669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3667133690546385255215117 1375175133954894470705669)
                ·
                  refine ⟨257845337616542713257313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375175133954894470705669 257845337616542713257313)
                  ·
                    rfl

theorem cell22_2259684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2259684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259684 prefixEnd_2259684 := by exact prefixLift 2259684
  have htrace : WordTrace (prefixWord ++ tailWord_2259684) baseStart_2259684 baseEnd_2259684 := by
    simpa [prefixWord, tailWord_2259684, baseEnd_2259684] using wordTrace_append hprefix tailTrace_2259684
  have hstable : (prefixWord ++ tailWord_2259684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259684).length < 2 ^ (prefixWord ++ tailWord_2259684).sum := by decide
  have hdescent : baseEnd_2259684 < baseStart_2259684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259695 : List Nat := [1, 1, 2, 1, 5, 2, 10]
def baseStart_2259695 : Nat := 118140960795 + 2259695 * 2 ^ 59
def prefixEnd_2259695 : Nat := 4983230072969 + 3 ^ 40 * 2259695 * 2
def baseEnd_2259695 : Nat := 28649621421275102879515

theorem tailTrace_2259695 : CollatzResearch.WordTrace tailWord_2259695 prefixEnd_2259695 28649621421275102879515 := by
  unfold tailWord_2259695
  simp only [CollatzResearch.WordTrace]
  refine ⟨82417847548518415026036539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54945231699012276684024359 82417847548518415026036539)
  ·
    refine ⟨123626771322777622539054809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82417847548518415026036539 123626771322777622539054809)
    ·
      refine ⟨92720078492083216904291107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123626771322777622539054809 92720078492083216904291107)
      ·
        refine ⟨139080117738124825356436661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92720078492083216904291107 139080117738124825356436661)
        ·
          refine ⟨13038761037949202377165937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139080117738124825356436661 13038761037949202377165937)
          ·
            refine ⟨9779070778461901782874453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13038761037949202377165937 9779070778461901782874453)
            ·
              refine ⟨28649621421275102879515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9779070778461901782874453 28649621421275102879515)
              ·
                rfl

theorem cell22_2259695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 10].length) (baseStart_2259695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259695 prefixEnd_2259695 := by exact prefixLift 2259695
  have htrace : WordTrace (prefixWord ++ tailWord_2259695) baseStart_2259695 baseEnd_2259695 := by
    simpa [prefixWord, tailWord_2259695, baseEnd_2259695] using wordTrace_append hprefix tailTrace_2259695
  have hstable : (prefixWord ++ tailWord_2259695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259695).length < 2 ^ (prefixWord ++ tailWord_2259695).sum := by decide
  have hdescent : baseEnd_2259695 < baseStart_2259695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259697 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_2259697 : Nat := 118140960795 + 2259697 * 2 ^ 59
def prefixEnd_2259697 : Nat := 4983230072969 + 3 ^ 40 * 2259697 * 2
def baseEnd_2259697 : Nat := 773540463015300439196899

theorem tailTrace_2259697 : CollatzResearch.WordTrace tailWord_2259697 prefixEnd_2259697 773540463015300439196899 := by
  unfold tailWord_2259697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82417920494511169367609345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54945280329674112911739563 82417920494511169367609345)
  ·
    refine ⟨61813440370883377025707009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82417920494511169367609345 61813440370883377025707009)
    ·
      refine ⟨46360080278162532769280257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61813440370883377025707009 46360080278162532769280257)
      ·
        refine ⟨34770060208621899576960193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46360080278162532769280257 34770060208621899576960193)
        ·
          refine ⟨26077545156466424682720145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34770060208621899576960193 26077545156466424682720145)
          ·
            refine ⟨19558158867349818512040109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26077545156466424682720145 19558158867349818512040109)
            ·
              refine ⟨7334309575256181942015041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19558158867349818512040109 7334309575256181942015041)
              ·
                refine ⟨5500732181442136456511281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334309575256181942015041 5500732181442136456511281)
                ·
                  refine ⟨4125549136081602342383461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5500732181442136456511281 4125549136081602342383461)
                  ·
                    refine ⟨773540463015300439196899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125549136081602342383461 773540463015300439196899)
                    ·
                      rfl

theorem cell22_2259697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_2259697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259697 prefixEnd_2259697 := by exact prefixLift 2259697
  have htrace : WordTrace (prefixWord ++ tailWord_2259697) baseStart_2259697 baseEnd_2259697 := by
    simpa [prefixWord, tailWord_2259697, baseEnd_2259697] using wordTrace_append hprefix tailTrace_2259697
  have hstable : (prefixWord ++ tailWord_2259697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259697).length < 2 ^ (prefixWord ++ tailWord_2259697).sum := by decide
  have hdescent : baseEnd_2259697 < baseStart_2259697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259727 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 5, 3]
def baseStart_2259727 : Nat := 118140960795 + 2259727 * 2 ^ 59
def prefixEnd_2259727 : Nat := 4983230072969 + 3 ^ 40 * 2259727 * 2
def baseEnd_2259727 : Nat := 773550732628390360946807

theorem tailTrace_2259727 : CollatzResearch.WordTrace tailWord_2259727 prefixEnd_2259727 773550732628390360946807 := by
  unfold tailWord_2259727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82419014684402484491201435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54946009789601656327467623 82419014684402484491201435)
  ·
    refine ⟨123628522026603726736802153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82419014684402484491201435 123628522026603726736802153)
    ·
      refine ⟨92721391519952795052601615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123628522026603726736802153 92721391519952795052601615)
      ·
        refine ⟨139082087279929192578902423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92721391519952795052601615 139082087279929192578902423)
        ·
          refine ⟨208623130919893788868353635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139082087279929192578902423 208623130919893788868353635)
          ·
            refine ⟨312934696379840683302530453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208623130919893788868353635 312934696379840683302530453)
            ·
              refine ⟨14668813892805032029806115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312934696379840683302530453 14668813892805032029806115)
              ·
                refine ⟨22003220839207548044709173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14668813892805032029806115 22003220839207548044709173)
                ·
                  refine ⟨2062801953675707629191485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22003220839207548044709173 2062801953675707629191485)
                  ·
                    refine ⟨773550732628390360946807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062801953675707629191485 773550732628390360946807)
                    ·
                      rfl

theorem cell22_2259727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_2259727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259727 prefixEnd_2259727 := by exact prefixLift 2259727
  have htrace : WordTrace (prefixWord ++ tailWord_2259727) baseStart_2259727 baseEnd_2259727 := by
    simpa [prefixWord, tailWord_2259727, baseEnd_2259727] using wordTrace_append hprefix tailTrace_2259727
  have hstable : (prefixWord ++ tailWord_2259727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259727).length < 2 ^ (prefixWord ++ tailWord_2259727).sum := by decide
  have hdescent : baseEnd_2259727 < baseStart_2259727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259761 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 1, 3]
def baseStart_2259761 : Nat := 118140960795 + 2259761 * 2 ^ 59
def prefixEnd_2259761 : Nat := 4983230072969 + 3 ^ 40 * 2259761 * 2
def baseEnd_2259761 : Nat := 773562371523225605596703

theorem tailTrace_2259761 : CollatzResearch.WordTrace tailWord_2259761 prefixEnd_2259761 773562371523225605596703 := by
  unfold tailWord_2259761
  simp only [CollatzResearch.WordTrace]
  refine ⟨82420254766279308297939137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54946836510852872198626091 82420254766279308297939137)
  ·
    refine ⟨61815191074709481223454353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82420254766279308297939137 61815191074709481223454353)
    ·
      refine ⟨46361393306032110917590765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61815191074709481223454353 46361393306032110917590765)
      ·
        refine ⟨17385522489762041594096537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46361393306032110917590765 17385522489762041594096537)
        ·
          refine ⟨13039141867321531195572403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17385522489762041594096537 13039141867321531195572403)
          ·
            refine ⟨19558712800982296793358605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13039141867321531195572403 19558712800982296793358605)
            ·
              refine ⟨7334517300368361297509477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19558712800982296793358605 7334517300368361297509477)
              ·
                refine ⟨1375221993819067743283027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7334517300368361297509477 1375221993819067743283027)
                ·
                  refine ⟨2062832990728601614924541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375221993819067743283027 2062832990728601614924541)
                  ·
                    refine ⟨773562371523225605596703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062832990728601614924541 773562371523225605596703)
                    ·
                      rfl

theorem cell22_2259761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_2259761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259761 prefixEnd_2259761 := by exact prefixLift 2259761
  have htrace : WordTrace (prefixWord ++ tailWord_2259761) baseStart_2259761 baseEnd_2259761 := by
    simpa [prefixWord, tailWord_2259761, baseEnd_2259761] using wordTrace_append hprefix tailTrace_2259761
  have hstable : (prefixWord ++ tailWord_2259761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259761).length < 2 ^ (prefixWord ++ tailWord_2259761).sum := by decide
  have hdescent : baseEnd_2259761 < baseStart_2259761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259819 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 4]
def baseStart_2259819 : Nat := 118140960795 + 2259819 * 2 ^ 59
def prefixEnd_2259819 : Nat := 4983230072969 + 3 ^ 40 * 2259819 * 2
def baseEnd_2259819 : Nat := 257860742036177595882175

theorem tailTrace_2259819 : CollatzResearch.WordTrace tailWord_2259819 prefixEnd_2259819 257860742036177595882175 := by
  unfold tailWord_2259819
  simp only [CollatzResearch.WordTrace]
  refine ⟨82422370200069184203550511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54948246800046122802367007 82422370200069184203550511)
  ·
    refine ⟨123633555300103776305325767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82422370200069184203550511 123633555300103776305325767)
    ·
      refine ⟨185450332950155664457988651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123633555300103776305325767 185450332950155664457988651)
      ·
        refine ⟨278175499425233496686982977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185450332950155664457988651 278175499425233496686982977)
        ·
          refine ⟨208631624568925122515237233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278175499425233496686982977 208631624568925122515237233)
          ·
            refine ⟨156473718426693841886427925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208631624568925122515237233 156473718426693841886427925)
            ·
              refine ⟨7334705551251273838426309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 156473718426693841886427925 7334705551251273838426309)
              ·
                refine ⟨1375257290859613844704933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7334705551251273838426309 1375257290859613844704933)
                ·
                  refine ⟨257860742036177595882175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375257290859613844704933 257860742036177595882175)
                  ·
                    rfl

theorem cell22_2259819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 4].length) (baseStart_2259819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259819 prefixEnd_2259819 := by exact prefixLift 2259819
  have htrace : WordTrace (prefixWord ++ tailWord_2259819) baseStart_2259819 baseEnd_2259819 := by
    simpa [prefixWord, tailWord_2259819, baseEnd_2259819] using wordTrace_append hprefix tailTrace_2259819
  have hstable : (prefixWord ++ tailWord_2259819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259819).length < 2 ^ (prefixWord ++ tailWord_2259819).sum := by decide
  have hdescent : baseEnd_2259819 < baseStart_2259819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_2259832 : Nat := 118140960795 + 2259832 * 2 ^ 59
def prefixEnd_2259832 : Nat := 4983230072969 + 3 ^ 40 * 2259832 * 2
def baseEnd_2259832 : Nat := 773586676274205087071485

theorem tailTrace_2259832 : CollatzResearch.WordTrace tailWord_2259832 prefixEnd_2259832 773586676274205087071485 := by
  unfold tailWord_2259832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41211422174511043711886875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54948562899348058282515833 41211422174511043711886875)
  ·
    refine ⟨61817133261766565567830313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41211422174511043711886875 61817133261766565567830313)
    ·
      refine ⟨46362849946324924175872735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61817133261766565567830313 46362849946324924175872735)
      ·
        refine ⟨69544274919487386263809103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46362849946324924175872735 69544274919487386263809103)
        ·
          refine ⟨104316412379231079395713655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69544274919487386263809103 104316412379231079395713655)
          ·
            refine ⟨156474618568846619093570483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104316412379231079395713655 156474618568846619093570483)
            ·
              refine ⟨234711927853269928640355725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156474618568846619093570483 234711927853269928640355725)
              ·
                refine ⟨88016972944976223240133397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234711927853269928640355725 88016972944976223240133397)
                ·
                  refine ⟨4125795606795760464381253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88016972944976223240133397 4125795606795760464381253)
                  ·
                    refine ⟨773586676274205087071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125795606795760464381253 773586676274205087071485)
                    ·
                      rfl

theorem cell22_2259832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_2259832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259832 prefixEnd_2259832 := by exact prefixLift 2259832
  have htrace : WordTrace (prefixWord ++ tailWord_2259832) baseStart_2259832 baseEnd_2259832 := by
    simpa [prefixWord, tailWord_2259832, baseEnd_2259832] using wordTrace_append hprefix tailTrace_2259832
  have hstable : (prefixWord ++ tailWord_2259832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259832).length < 2 ^ (prefixWord ++ tailWord_2259832).sum := by decide
  have hdescent : baseEnd_2259832 < baseStart_2259832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259866 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_2259866 : Nat := 118140960795 + 2259866 * 2 ^ 59
def prefixEnd_2259866 : Nat := 4983230072969 + 3 ^ 40 * 2259866 * 2
def baseEnd_2259866 : Nat := 773598315169040331721381

theorem tailTrace_2259866 : CollatzResearch.WordTrace tailWord_2259866 prefixEnd_2259866 773598315169040331721381 := by
  unfold tailWord_2259866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606021107724727807627863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54949389620599274153674301 20606021107724727807627863)
  ·
    refine ⟨30909031661587091711441795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20606021107724727807627863 30909031661587091711441795)
    ·
      refine ⟨46363547492380637567162693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30909031661587091711441795 46363547492380637567162693)
      ·
        refine ⟨8693165154821369543843005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46363547492380637567162693 8693165154821369543843005)
        ·
          refine ⟨3259936933058013578941127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8693165154821369543843005 3259936933058013578941127)
          ·
            refine ⟨4889905399587020368411691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259936933058013578941127 4889905399587020368411691)
            ·
              refine ⟨7334858099380530552617537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889905399587020368411691 7334858099380530552617537)
              ·
                refine ⟨5501143574535397914463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7334858099380530552617537 5501143574535397914463153)
                ·
                  refine ⟨4125857680901548435847365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5501143574535397914463153 4125857680901548435847365)
                  ·
                    refine ⟨773598315169040331721381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125857680901548435847365 773598315169040331721381)
                    ·
                      rfl

theorem cell22_2259866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_2259866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259866 prefixEnd_2259866 := by exact prefixLift 2259866
  have htrace : WordTrace (prefixWord ++ tailWord_2259866) baseStart_2259866 baseEnd_2259866 := by
    simpa [prefixWord, tailWord_2259866, baseEnd_2259866] using wordTrace_append hprefix tailTrace_2259866
  have hstable : (prefixWord ++ tailWord_2259866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259866).length < 2 ^ (prefixWord ++ tailWord_2259866).sum := by decide
  have hdescent : baseEnd_2259866 < baseStart_2259866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259885 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2259885 : Nat := 118140960795 + 2259885 * 2 ^ 59
def prefixEnd_2259885 : Nat := 4983230072969 + 3 ^ 40 * 2259885 * 2
def baseEnd_2259885 : Nat := 773604819257330615496323

theorem tailTrace_2259885 : CollatzResearch.WordTrace tailWord_2259885 prefixEnd_2259885 773604819257330615496323 := by
  unfold tailWord_2259885
  simp only [CollatzResearch.WordTrace]
  refine ⟨82424777417830077475453109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54949851611886718316968739 82424777417830077475453109)
  ·
    refine ⟨7727322882921569763323729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82424777417830077475453109 7727322882921569763323729)
    ·
      refine ⟨5795492162191177322492797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7727322882921569763323729 5795492162191177322492797)
      ·
        refine ⟨2173309560821691495934799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5795492162191177322492797 2173309560821691495934799)
        ·
          refine ⟨3259964341232537243902199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173309560821691495934799 3259964341232537243902199)
          ·
            refine ⟨4889946511848805865853299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259964341232537243902199 4889946511848805865853299)
            ·
              refine ⟨7334919767773208798779949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4889946511848805865853299 7334919767773208798779949)
              ·
                refine ⟨2750594912914953299542481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7334919767773208798779949 2750594912914953299542481)
                ·
                  refine ⟨2062946184686214974656861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2750594912914953299542481 2062946184686214974656861)
                  ·
                    refine ⟨773604819257330615496323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062946184686214974656861 773604819257330615496323)
                    ·
                      rfl

theorem cell22_2259885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2259885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259885 prefixEnd_2259885 := by exact prefixLift 2259885
  have htrace : WordTrace (prefixWord ++ tailWord_2259885) baseStart_2259885 baseEnd_2259885 := by
    simpa [prefixWord, tailWord_2259885, baseEnd_2259885] using wordTrace_append hprefix tailTrace_2259885
  have hstable : (prefixWord ++ tailWord_2259885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259885).length < 2 ^ (prefixWord ++ tailWord_2259885).sum := by decide
  have hdescent : baseEnd_2259885 < baseStart_2259885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259907 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_2259907 : Nat := 118140960795 + 2259907 * 2 ^ 59
def prefixEnd_2259907 : Nat := 4983230072969 + 3 ^ 40 * 2259907 * 2
def baseEnd_2259907 : Nat := 773612350306929891446255

theorem tailTrace_2259907 : CollatzResearch.WordTrace tailWord_2259907 prefixEnd_2259907 773612350306929891446255 := by
  unfold tailWord_2259907
  simp only [CollatzResearch.WordTrace]
  refine ⟨82425579823750375232753975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54950386549166916821835983 82425579823750375232753975)
  ·
    refine ⟨123638369735625562849130963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82425579823750375232753975 123638369735625562849130963)
    ·
      refine ⟨185457554603438344273696445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123638369735625562849130963 185457554603438344273696445)
      ·
        refine ⟨69546582976289379102636167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185457554603438344273696445 69546582976289379102636167)
        ·
          refine ⟨104319874464434068653954251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69546582976289379102636167 104319874464434068653954251)
          ·
            refine ⟨156479811696651102980931377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104319874464434068653954251 156479811696651102980931377)
            ·
              refine ⟨117359858772488327235698533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156479811696651102980931377 117359858772488327235698533)
              ·
                refine ⟨22004973519841561356693475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117359858772488327235698533 22004973519841561356693475)
                ·
                  refine ⟨33007460279762342035040213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22004973519841561356693475 33007460279762342035040213)
                  ·
                    refine ⟨773612350306929891446255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33007460279762342035040213 773612350306929891446255)
                    ·
                      rfl

theorem cell22_2259907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_2259907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259907 prefixEnd_2259907 := by exact prefixLift 2259907
  have htrace : WordTrace (prefixWord ++ tailWord_2259907) baseStart_2259907 baseEnd_2259907 := by
    simpa [prefixWord, tailWord_2259907, baseEnd_2259907] using wordTrace_append hprefix tailTrace_2259907
  have hstable : (prefixWord ++ tailWord_2259907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259907).length < 2 ^ (prefixWord ++ tailWord_2259907).sum := by decide
  have hdescent : baseEnd_2259907 < baseStart_2259907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259930 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_2259930 : Nat := 118140960795 + 2259930 * 2 ^ 59
def prefixEnd_2259930 : Nat := 4983230072969 + 3 ^ 40 * 2259930 * 2
def baseEnd_2259930 : Nat := 773620223676965498121185

theorem tailTrace_2259930 : CollatzResearch.WordTrace tailWord_2259930 prefixEnd_2259930 773620223676965498121185 := by
  unfold tailWord_2259930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606604675666762540210311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54950945801778033440560829 20606604675666762540210311)
  ·
    refine ⟨30909907013500143810315467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20606604675666762540210311 30909907013500143810315467)
    ·
      refine ⟨46364860520250215715473201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30909907013500143810315467 46364860520250215715473201)
      ·
        refine ⟨34773645390187661786604901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46364860520250215715473201 34773645390187661786604901)
        ·
          refine ⟨6520058510660186584988419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34773645390187661786604901 6520058510660186584988419)
          ·
            refine ⟨9780087765990279877482629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520058510660186584988419 9780087765990279877482629)
            ·
              refine ⟨1833766456123177477027993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9780087765990279877482629 1833766456123177477027993)
              ·
                refine ⟨1375324842092383107770995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833766456123177477027993 1375324842092383107770995)
                ·
                  refine ⟨2062987263138574661656493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375324842092383107770995 2062987263138574661656493)
                  ·
                    refine ⟨773620223676965498121185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062987263138574661656493 773620223676965498121185)
                    ·
                      rfl

theorem cell22_2259930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_2259930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259930 prefixEnd_2259930 := by exact prefixLift 2259930
  have htrace : WordTrace (prefixWord ++ tailWord_2259930) baseStart_2259930 baseEnd_2259930 := by
    simpa [prefixWord, tailWord_2259930, baseEnd_2259930] using wordTrace_append hprefix tailTrace_2259930
  have hstable : (prefixWord ++ tailWord_2259930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259930).length < 2 ^ (prefixWord ++ tailWord_2259930).sum := by decide
  have hdescent : baseEnd_2259930 < baseStart_2259930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2259939 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_2259939 : Nat := 118140960795 + 2259939 * 2 ^ 59
def prefixEnd_2259939 : Nat := 4983230072969 + 3 ^ 40 * 2259939 * 2
def baseEnd_2259939 : Nat := 773623304560892474646157

theorem tailTrace_2259939 : CollatzResearch.WordTrace tailWord_2259939 prefixEnd_2259939 773623304560892474646157 := by
  unfold tailWord_2259939
  simp only [CollatzResearch.WordTrace]
  refine ⟨82426746959634444697918871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54951164639756296465279247 82426746959634444697918871)
  ·
    refine ⟨123640120439451667046878307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82426746959634444697918871 123640120439451667046878307)
    ·
      refine ⟨185460180659177500570317461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123640120439451667046878307 185460180659177500570317461)
      ·
        refine ⟨8693445968398945339233631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185460180659177500570317461 8693445968398945339233631)
        ·
          refine ⟨13040168952598418008850447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8693445968398945339233631 13040168952598418008850447)
          ·
            refine ⟨19560253428897627013275671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13040168952598418008850447 19560253428897627013275671)
            ·
              refine ⟨29340380143346440519913507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19560253428897627013275671 29340380143346440519913507)
              ·
                refine ⟨44010570215019660779870261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29340380143346440519913507 44010570215019660779870261)
                ·
                  refine ⟨4125990957658093198112837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44010570215019660779870261 4125990957658093198112837)
                  ·
                    refine ⟨773623304560892474646157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4125990957658093198112837 773623304560892474646157)
                    ·
                      rfl

theorem cell22_2259939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_2259939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2259939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2259939 prefixEnd_2259939 := by exact prefixLift 2259939
  have htrace : WordTrace (prefixWord ++ tailWord_2259939) baseStart_2259939 baseEnd_2259939 := by
    simpa [prefixWord, tailWord_2259939, baseEnd_2259939] using wordTrace_append hprefix tailTrace_2259939
  have hstable : (prefixWord ++ tailWord_2259939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2259939).length < 2 ^ (prefixWord ++ tailWord_2259939).sum := by decide
  have hdescent : baseEnd_2259939 < baseStart_2259939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2259939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260033 : List Nat := [1, 2, 5, 1, 4, 1, 8]
def baseStart_2260033 : Nat := 118140960795 + 2260033 * 2 ^ 59
def prefixEnd_2260033 : Nat := 4983230072969 + 3 ^ 40 * 2260033 * 2
def baseEnd_2260033 : Nat := 28653906765996576399847

theorem tailTrace_2260033 : CollatzResearch.WordTrace tailWord_2260033 prefixEnd_2260033 28653906765996576399847 := by
  unfold tailWord_2260033
  simp only [CollatzResearch.WordTrace]
  refine ⟨82430175421293898751840753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54953450280862599167893835 82430175421293898751840753)
  ·
    refine ⟨61822631565970424063880565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82430175421293898751840753 61822631565970424063880565)
    ·
      refine ⟨5795871709309727255988803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61822631565970424063880565 5795871709309727255988803)
      ·
        refine ⟨8693807563964590883983205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795871709309727255988803 8693807563964590883983205)
        ·
          refine ⟨1630088918243360790746851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8693807563964590883983205 1630088918243360790746851)
          ·
            refine ⟨2445133377365041186120277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630088918243360790746851 2445133377365041186120277)
            ·
              refine ⟨28653906765996576399847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2445133377365041186120277 28653906765996576399847)
              ·
                rfl

theorem cell22_2260033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 8].length) (baseStart_2260033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260033 prefixEnd_2260033 := by exact prefixLift 2260033
  have htrace : WordTrace (prefixWord ++ tailWord_2260033) baseStart_2260033 baseEnd_2260033 := by
    simpa [prefixWord, tailWord_2260033, baseEnd_2260033] using wordTrace_append hprefix tailTrace_2260033
  have hstable : (prefixWord ++ tailWord_2260033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260033).length < 2 ^ (prefixWord ++ tailWord_2260033).sum := by decide
  have hdescent : baseEnd_2260033 < baseStart_2260033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260048 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_2260048 : Nat := 118140960795 + 2260048 * 2 ^ 59
def prefixEnd_2260048 : Nat := 4983230072969 + 3 ^ 40 * 2260048 * 2
def baseEnd_2260048 : Nat := 773660617488452523670823

theorem tailTrace_2260048 : CollatzResearch.WordTrace tailWord_2260048 prefixEnd_2260048 773660617488452523670823 := by
  unfold tailWord_2260048
  simp only [CollatzResearch.WordTrace]
  refine ⟨41215361258119778156818399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54953815010826370875757865 41215361258119778156818399)
  ·
    refine ⟨61823041887179667235227599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41215361258119778156818399 61823041887179667235227599)
    ·
      refine ⟨92734562830769500852841399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61823041887179667235227599 92734562830769500852841399)
      ·
        refine ⟨139101844246154251279262099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92734562830769500852841399 139101844246154251279262099)
        ·
          refine ⟨208652766369231376918893149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139101844246154251279262099 208652766369231376918893149)
          ·
            refine ⟨78244787388461766344584931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 208652766369231376918893149 78244787388461766344584931)
            ·
              refine ⟨117367181082692649516877397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78244787388461766344584931 117367181082692649516877397)
              ·
                refine ⟨1375396653312804486525907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 117367181082692649516877397 1375396653312804486525907)
                ·
                  refine ⟨2063094979969206729788861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375396653312804486525907 2063094979969206729788861)
                  ·
                    refine ⟨773660617488452523670823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063094979969206729788861 773660617488452523670823)
                    ·
                      rfl

theorem cell22_2260048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_2260048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260048 prefixEnd_2260048 := by exact prefixLift 2260048
  have htrace : WordTrace (prefixWord ++ tailWord_2260048) baseStart_2260048 baseEnd_2260048 := by
    simpa [prefixWord, tailWord_2260048, baseEnd_2260048] using wordTrace_append hprefix tailTrace_2260048
  have hstable : (prefixWord ++ tailWord_2260048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260048).length < 2 ^ (prefixWord ++ tailWord_2260048).sum := by decide
  have hdescent : baseEnd_2260048 < baseStart_2260048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260091 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 1, 4]
def baseStart_2260091 : Nat := 118140960795 + 2260091 * 2 ^ 59
def prefixEnd_2260091 : Nat := 4983230072969 + 3 ^ 40 * 2260091 * 2
def baseEnd_2260091 : Nat := 773675337267214744845691

theorem tailTrace_2260091 : CollatzResearch.WordTrace tailWord_2260091 prefixEnd_2260091 773675337267214744845691 := by
  unfold tailWord_2260091
  simp only [CollatzResearch.WordTrace]
  refine ⟨82432290855083774657452127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54954860570055849771634751 82432290855083774657452127)
  ·
    refine ⟨123648436282625661986178191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82432290855083774657452127 123648436282625661986178191)
    ·
      refine ⟨185472654423938492979267287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123648436282625661986178191 185472654423938492979267287)
      ·
        refine ⟨278208981635907739468900931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185472654423938492979267287 278208981635907739468900931)
        ·
          refine ⟨417313472453861609203351397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278208981635907739468900931 417313472453861609203351397)
          ·
            refine ⟨78246276085099051725628387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 417313472453861609203351397 78246276085099051725628387)
            ·
              refine ⟨117369414127648577588442581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78246276085099051725628387 117369414127648577588442581)
              ·
                refine ⟨2750845643616763537229123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117369414127648577588442581 2750845643616763537229123)
                ·
                  refine ⟨4126268465425145305843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750845643616763537229123 4126268465425145305843685)
                  ·
                    refine ⟨773675337267214744845691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126268465425145305843685 773675337267214744845691)
                    ·
                      rfl

theorem cell22_2260091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_2260091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260091 prefixEnd_2260091 := by exact prefixLift 2260091
  have htrace : WordTrace (prefixWord ++ tailWord_2260091) baseStart_2260091 baseEnd_2260091 := by
    simpa [prefixWord, tailWord_2260091, baseEnd_2260091] using wordTrace_append hprefix tailTrace_2260091
  have hstable : (prefixWord ++ tailWord_2260091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260091).length < 2 ^ (prefixWord ++ tailWord_2260091).sum := by decide
  have hdescent : baseEnd_2260091 < baseStart_2260091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260106 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_2260106 : Nat := 118140960795 + 2260106 * 2 ^ 59
def prefixEnd_2260106 : Nat := 4983230072969 + 3 ^ 40 * 2260106 * 2
def baseEnd_2260106 : Nat := 257893490691253235240215

theorem tailTrace_2260106 : CollatzResearch.WordTrace tailWord_2260106 prefixEnd_2260106 257893490691253235240215 := by
  unfold tailWord_2260106
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608209487507358054812043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54955225300019621479498781 20608209487507358054812043)
  ·
    refine ⟨30912314231261037082218065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20608209487507358054812043 30912314231261037082218065)
    ·
      refine ⟨23184235673445777811663549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30912314231261037082218065 23184235673445777811663549)
      ·
        refine ⟨8694088377542166679373831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23184235673445777811663549 8694088377542166679373831)
        ·
          refine ⟨13041132566313250019060747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694088377542166679373831 13041132566313250019060747)
          ·
            refine ⟨19561698849469875028591121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13041132566313250019060747 19561698849469875028591121)
            ·
              refine ⟨14671274137102406271443341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19561698849469875028591121 14671274137102406271443341)
              ·
                refine ⟨5501727801413402351791253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14671274137102406271443341 5501727801413402351791253)
                ·
                  refine ⟨257893490691253235240215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5501727801413402351791253 257893490691253235240215)
                  ·
                    rfl

theorem cell22_2260106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_2260106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260106 prefixEnd_2260106 := by exact prefixLift 2260106
  have htrace : WordTrace (prefixWord ++ tailWord_2260106) baseStart_2260106 baseEnd_2260106 := by
    simpa [prefixWord, tailWord_2260106, baseEnd_2260106] using wordTrace_append hprefix tailTrace_2260106
  have hstable : (prefixWord ++ tailWord_2260106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260106).length < 2 ^ (prefixWord ++ tailWord_2260106).sum := by decide
  have hdescent : baseEnd_2260106 < baseStart_2260106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260121 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 8, 3]
def baseStart_2260121 : Nat := 118140960795 + 2260121 * 2 ^ 59
def prefixEnd_2260121 : Nat := 4983230072969 + 3 ^ 40 * 2260121 * 2
def baseEnd_2260121 : Nat := 773685606880304666595599

theorem tailTrace_2260121 : CollatzResearch.WordTrace tailWord_2260121 prefixEnd_2260121 773685606880304666595599 := by
  unfold tailWord_2260121
  simp only [CollatzResearch.WordTrace]
  refine ⟨82433385044975089781044217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54955590029983393187362811 82433385044975089781044217)
  ·
    refine ⟨61825038783731317335783163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82433385044975089781044217 61825038783731317335783163)
    ·
      refine ⟨92737558175596976003674745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61825038783731317335783163 92737558175596976003674745)
      ·
        refine ⟨69553168631697732002756059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92737558175596976003674745 69553168631697732002756059)
        ·
          refine ⟨104329752947546598004134089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69553168631697732002756059 104329752947546598004134089)
          ·
            refine ⟨78247314710659948503100567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104329752947546598004134089 78247314710659948503100567)
            ·
              refine ⟨117370972065989922754650851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78247314710659948503100567 117370972065989922754650851)
              ·
                refine ⟨176056458098984884131976277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117370972065989922754650851 176056458098984884131976277)
                ·
                  refine ⟨2063161618347479110921597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 176056458098984884131976277 2063161618347479110921597)
                  ·
                    refine ⟨773685606880304666595599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063161618347479110921597 773685606880304666595599)
                    ·
                      rfl

theorem cell22_2260121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 3].length) (baseStart_2260121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260121 prefixEnd_2260121 := by exact prefixLift 2260121
  have htrace : WordTrace (prefixWord ++ tailWord_2260121) baseStart_2260121 baseEnd_2260121 := by
    simpa [prefixWord, tailWord_2260121, baseEnd_2260121] using wordTrace_append hprefix tailTrace_2260121
  have hstable : (prefixWord ++ tailWord_2260121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260121).length < 2 ^ (prefixWord ++ tailWord_2260121).sum := by decide
  have hdescent : baseEnd_2260121 < baseStart_2260121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260183 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 3, 3]
def baseStart_2260183 : Nat := 118140960795 + 2260183 * 2 ^ 59
def prefixEnd_2260183 : Nat := 4983230072969 + 3 ^ 40 * 2260183 * 2
def baseEnd_2260183 : Nat := 773706830747357171545409

theorem tailTrace_2260183 : CollatzResearch.WordTrace tailWord_2260183 prefixEnd_2260183 773706830747357171545409 := by
  unfold tailWord_2260183
  simp only [CollatzResearch.WordTrace]
  refine ⟨82435646370750474369801203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54957097580500316246534135 82435646370750474369801203)
  ·
    refine ⟨123653469556125711554701805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82435646370750474369801203 123653469556125711554701805)
    ·
      refine ⟨46370051083547141833013177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123653469556125711554701805 46370051083547141833013177)
      ·
        refine ⟨34777538312660356374759883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46370051083547141833013177 34777538312660356374759883)
        ·
          refine ⟨52166307468990534562139825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34777538312660356374759883 52166307468990534562139825)
          ·
            refine ⟨39124730601742900921604869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52166307468990534562139825 39124730601742900921604869)
            ·
              refine ⟨7335886987826793922800913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39124730601742900921604869 7335886987826793922800913)
              ·
                refine ⟨5501915240870095442100685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7335886987826793922800913 5501915240870095442100685)
                ·
                  refine ⟨2063218215326285790787757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5501915240870095442100685 2063218215326285790787757)
                  ·
                    refine ⟨773706830747357171545409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063218215326285790787757 773706830747357171545409)
                    ·
                      rfl

theorem cell22_2260183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_2260183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260183 prefixEnd_2260183 := by exact prefixLift 2260183
  have htrace : WordTrace (prefixWord ++ tailWord_2260183) baseStart_2260183 baseEnd_2260183 := by
    simpa [prefixWord, tailWord_2260183, baseEnd_2260183] using wordTrace_append hprefix tailTrace_2260183
  have hstable : (prefixWord ++ tailWord_2260183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260183).length < 2 ^ (prefixWord ++ tailWord_2260183).sum := by decide
  have hdescent : baseEnd_2260183 < baseStart_2260183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260196 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_2260196 : Nat := 118140960795 + 2260196 * 2 ^ 59
def prefixEnd_2260196 : Nat := 4983230072969 + 3 ^ 40 * 2260196 * 2
def baseEnd_2260196 : Nat := 257903760304343156990123

theorem tailTrace_2260196 : CollatzResearch.WordTrace tailWord_2260196 prefixEnd_2260196 257903760304343156990123 := by
  unfold tailWord_2260196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41218060259851688795012221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54957413679802251726682961 41218060259851688795012221)
  ·
    refine ⟨15456772597444383298129583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41218060259851688795012221 15456772597444383298129583)
    ·
      refine ⟨23185158896166574947194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15456772597444383298129583 23185158896166574947194375)
      ·
        refine ⟨34777738344249862420791563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23185158896166574947194375 34777738344249862420791563)
        ·
          refine ⟨52166607516374793631187345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34777738344249862420791563 52166607516374793631187345)
          ·
            refine ⟨39124955637281095223390509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52166607516374793631187345 39124955637281095223390509)
            ·
              refine ⟨14671858363980410708771441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39124955637281095223390509 14671858363980410708771441)
              ·
                refine ⟨11003893772985308031578581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14671858363980410708771441 11003893772985308031578581)
                ·
                  refine ⟨257903760304343156990123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11003893772985308031578581 257903760304343156990123)
                  ·
                    rfl

theorem cell22_2260196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_2260196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260196 prefixEnd_2260196 := by exact prefixLift 2260196
  have htrace : WordTrace (prefixWord ++ tailWord_2260196) baseStart_2260196 baseEnd_2260196 := by
    simpa [prefixWord, tailWord_2260196, baseEnd_2260196] using wordTrace_append hprefix tailTrace_2260196
  have hstable : (prefixWord ++ tailWord_2260196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260196).length < 2 ^ (prefixWord ++ tailWord_2260196).sum := by decide
  have hdescent : baseEnd_2260196 < baseStart_2260196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260217 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 1, 3]
def baseStart_2260217 : Nat := 118140960795 + 2260217 * 2 ^ 59
def prefixEnd_2260217 : Nat := 4983230072969 + 3 ^ 40 * 2260217 * 2
def baseEnd_2260217 : Nat := 773718469642192416195305

theorem tailTrace_2260217 : CollatzResearch.WordTrace tailWord_2260217 prefixEnd_2260217 773718469642192416195305 := by
  unfold tailWord_2260217
  simp only [CollatzResearch.WordTrace]
  refine ⟨82436886452627298176538905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54957924301751532117692603 82436886452627298176538905)
  ·
    refine ⟨61827664839470473632404179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82436886452627298176538905 61827664839470473632404179)
    ·
      refine ⟨92741497259205710448606269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61827664839470473632404179 92741497259205710448606269)
      ·
        refine ⟨34778061472202141418227351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92741497259205710448606269 34778061472202141418227351)
        ·
          refine ⟨52167092208303212127341027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34778061472202141418227351 52167092208303212127341027)
          ·
            refine ⟨78250638312454818191011541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52167092208303212127341027 78250638312454818191011541)
            ·
              refine ⟨1833999335448159801351833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78250638312454818191011541 1833999335448159801351833)
              ·
                refine ⟨1375499501586119851013875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833999335448159801351833 1375499501586119851013875)
                ·
                  refine ⟨2063249252379179776520813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375499501586119851013875 2063249252379179776520813)
                  ·
                    refine ⟨773718469642192416195305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063249252379179776520813 773718469642192416195305)
                    ·
                      rfl

theorem cell22_2260217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 3].length) (baseStart_2260217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260217 prefixEnd_2260217 := by exact prefixLift 2260217
  have htrace : WordTrace (prefixWord ++ tailWord_2260217) baseStart_2260217 baseEnd_2260217 := by
    simpa [prefixWord, tailWord_2260217, baseEnd_2260217] using wordTrace_append hprefix tailTrace_2260217
  have hstable : (prefixWord ++ tailWord_2260217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260217).length < 2 ^ (prefixWord ++ tailWord_2260217).sum := by decide
  have hdescent : baseEnd_2260217 < baseStart_2260217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260241 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 8]
def baseStart_2260241 : Nat := 118140960795 + 2260241 * 2 ^ 59
def prefixEnd_2260241 : Nat := 4983230072969 + 3 ^ 40 * 2260241 * 2
def baseEnd_2260241 : Nat := 257908895110888117865077

theorem tailTrace_2260241 : CollatzResearch.WordTrace tailWord_2260241 prefixEnd_2260241 257908895110888117865077 := by
  unfold tailWord_2260241
  simp only [CollatzResearch.WordTrace]
  refine ⟨82437761804540350275412577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54958507869693566850275051 82437761804540350275412577)
  ·
    refine ⟨61828321353405262706559433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82437761804540350275412577 61828321353405262706559433)
    ·
      refine ⟨46371241015053947029919575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61828321353405262706559433 46371241015053947029919575)
      ·
        refine ⟨69556861522580920544879363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46371241015053947029919575 69556861522580920544879363)
        ·
          refine ⟨104335292283871380817319045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69556861522580920544879363 104335292283871380817319045)
          ·
            refine ⟨19562867303225883903247321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104335292283871380817319045 19562867303225883903247321)
            ·
              refine ⟨14672150477419412927435491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19562867303225883903247321 14672150477419412927435491)
              ·
                refine ⟨22008225716129119391153237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14672150477419412927435491 22008225716129119391153237)
                ·
                  refine ⟨257908895110888117865077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22008225716129119391153237 257908895110888117865077)
                  ·
                    rfl

theorem cell22_2260241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_2260241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260241 prefixEnd_2260241 := by exact prefixLift 2260241
  have htrace : WordTrace (prefixWord ++ tailWord_2260241) baseStart_2260241 baseEnd_2260241 := by
    simpa [prefixWord, tailWord_2260241, baseEnd_2260241] using wordTrace_append hprefix tailTrace_2260241
  have hstable : (prefixWord ++ tailWord_2260241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260241).length < 2 ^ (prefixWord ++ tailWord_2260241).sum := by decide
  have hdescent : baseEnd_2260241 < baseStart_2260241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260271 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_2260271 : Nat := 118140960795 + 2260271 * 2 ^ 59
def prefixEnd_2260271 : Nat := 4983230072969 + 3 ^ 40 * 2260271 * 2
def baseEnd_2260271 : Nat := 773736954945754275345139

theorem tailTrace_2260271 : CollatzResearch.WordTrace tailWord_2260271 prefixEnd_2260271 773736954945754275345139 := by
  unfold tailWord_2260271
  simp only [CollatzResearch.WordTrace]
  refine ⟨82438855994431665399004667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54959237329621110266003111 82438855994431665399004667)
  ·
    refine ⟨123658283991647498098507001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82438855994431665399004667 123658283991647498098507001)
    ·
      refine ⟨92743712993735623573880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123658283991647498098507001 92743712993735623573880251)
      ·
        refine ⟨139115569490603435360820377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92743712993735623573880251 139115569490603435360820377)
        ·
          refine ⟨104336677117952576520615283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139115569490603435360820377 104336677117952576520615283)
          ·
            refine ⟨156505015676928864780922925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104336677117952576520615283 156505015676928864780922925)
            ·
              refine ⟨58689380878848324292846097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156505015676928864780922925 58689380878848324292846097)
              ·
                refine ⟨44017035659136243219634573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58689380878848324292846097 44017035659136243219634573)
                ·
                  refine ⟨16506388372176091207362965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44017035659136243219634573 16506388372176091207362965)
                  ·
                    refine ⟨773736954945754275345139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16506388372176091207362965 773736954945754275345139)
                    ·
                      rfl

theorem cell22_2260271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_2260271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260271 prefixEnd_2260271 := by exact prefixLift 2260271
  have htrace : WordTrace (prefixWord ++ tailWord_2260271) baseStart_2260271 baseEnd_2260271 := by
    simpa [prefixWord, tailWord_2260271, baseEnd_2260271] using wordTrace_append hprefix tailTrace_2260271
  have hstable : (prefixWord ++ tailWord_2260271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260271).length < 2 ^ (prefixWord ++ tailWord_2260271).sum := by decide
  have hdescent : baseEnd_2260271 < baseStart_2260271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260275 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 4]
def baseStart_2260275 : Nat := 118140960795 + 2260275 * 2 ^ 59
def prefixEnd_2260275 : Nat := 4983230072969 + 3 ^ 40 * 2260275 * 2
def baseEnd_2260275 : Nat := 257912774742499866081709

theorem tailTrace_2260275 : CollatzResearch.WordTrace tailWord_2260275 prefixEnd_2260275 257912774742499866081709 := by
  unfold tailWord_2260275
  simp only [CollatzResearch.WordTrace]
  refine ⟨82439001886417174082150279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54959334590944782721433519 82439001886417174082150279)
  ·
    refine ⟨123658502829625761123225419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82439001886417174082150279 123658502829625761123225419)
    ·
      refine ⟨185487754244438641684838129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123658502829625761123225419 185487754244438641684838129)
      ·
        refine ⟨139115815683328981263628597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185487754244438641684838129 139115815683328981263628597)
        ·
          refine ⟨13042107720312091993465181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139115815683328981263628597 13042107720312091993465181)
          ·
            refine ⟨4890790395117034497549443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13042107720312091993465181 4890790395117034497549443)
            ·
              refine ⟨7336185592675551746324165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4890790395117034497549443 7336185592675551746324165)
              ·
                refine ⟨1375534798626665952435781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7336185592675551746324165 1375534798626665952435781)
                ·
                  refine ⟨257912774742499866081709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375534798626665952435781 257912774742499866081709)
                  ·
                    rfl

theorem cell22_2260275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 4].length) (baseStart_2260275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260275 prefixEnd_2260275 := by exact prefixLift 2260275
  have htrace : WordTrace (prefixWord ++ tailWord_2260275) baseStart_2260275 baseEnd_2260275 := by
    simpa [prefixWord, tailWord_2260275, baseEnd_2260275] using wordTrace_append hprefix tailTrace_2260275
  have hstable : (prefixWord ++ tailWord_2260275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260275).length < 2 ^ (prefixWord ++ tailWord_2260275).sum := by decide
  have hdescent : baseEnd_2260275 < baseStart_2260275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260335 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 3, 3]
def baseStart_2260335 : Nat := 118140960795 + 2260335 * 2 ^ 59
def prefixEnd_2260335 : Nat := 4983230072969 + 3 ^ 40 * 2260335 * 2
def baseEnd_2260335 : Nat := 773758863453679441744943

theorem tailTrace_2260335 : CollatzResearch.WordTrace tailWord_2260335 prefixEnd_2260335 773758863453679441744943 := by
  unfold tailWord_2260335
  simp only [CollatzResearch.WordTrace]
  refine ⟨82441190266199804329334459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54960793510799869552889639 82441190266199804329334459)
  ·
    refine ⟨123661785399299706494001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82441190266199804329334459 123661785399299706494001689)
    ·
      refine ⟨92746339049474779870501267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123661785399299706494001689 92746339049474779870501267)
      ·
        refine ⟨139119508574212169805751901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92746339049474779870501267 139119508574212169805751901)
        ·
          refine ⟨52169815715329563677156963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139119508574212169805751901 52169815715329563677156963)
          ·
            refine ⟨78254723572994345515735445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52169815715329563677156963 78254723572994345515735445)
            ·
              refine ⟨3668190167484109946050099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78254723572994345515735445 3668190167484109946050099)
              ·
                refine ⟨5502285251226164919075149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668190167484109946050099 5502285251226164919075149)
                ·
                  refine ⟨2063356969209811844653181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5502285251226164919075149 2063356969209811844653181)
                  ·
                    refine ⟨773758863453679441744943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063356969209811844653181 773758863453679441744943)
                    ·
                      rfl

theorem cell22_2260335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_2260335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260335 prefixEnd_2260335 := by exact prefixLift 2260335
  have htrace : WordTrace (prefixWord ++ tailWord_2260335) baseStart_2260335 baseEnd_2260335 := by
    simpa [prefixWord, tailWord_2260335, baseEnd_2260335] using wordTrace_append hprefix tailTrace_2260335
  have hstable : (prefixWord ++ tailWord_2260335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260335).length < 2 ^ (prefixWord ++ tailWord_2260335).sum := by decide
  have hdescent : baseEnd_2260335 < baseStart_2260335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260354 : List Nat := [3, 4, 2, 1, 1, 3, 2, 6]
def baseStart_2260354 : Nat := 118140960795 + 2260354 * 2 ^ 59
def prefixEnd_2260354 : Nat := 4983230072969 + 3 ^ 40 * 2260354 * 2
def baseEnd_2260354 : Nat := 85973929726885525057765

theorem tailTrace_2260354 : CollatzResearch.WordTrace tailWord_2260354 prefixEnd_2260354 85973929726885525057765 := by
  unfold tailWord_2260354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20610470813282742643569029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54961255502087313716184077 20610470813282742643569029)
  ·
    refine ⟨3864463277490514245669193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20610470813282742643569029 3864463277490514245669193)
    ·
      refine ⟨2898347458117885684251895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3864463277490514245669193 2898347458117885684251895)
      ·
        refine ⟨4347521187176828526377843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898347458117885684251895 4347521187176828526377843)
        ·
          refine ⟨6521281780765242789566765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4347521187176828526377843 6521281780765242789566765)
          ·
            refine ⟨2445480667786966046087537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6521281780765242789566765 2445480667786966046087537)
            ·
              refine ⟨1834110500840224534565653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445480667786966046087537 1834110500840224534565653)
              ·
                refine ⟨85973929726885525057765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1834110500840224534565653 85973929726885525057765)
                ·
                  rfl

theorem cell22_2260354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_2260354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260354 prefixEnd_2260354 := by exact prefixLift 2260354
  have htrace : WordTrace (prefixWord ++ tailWord_2260354) baseStart_2260354 baseEnd_2260354 := by
    simpa [prefixWord, tailWord_2260354, baseEnd_2260354] using wordTrace_append hprefix tailTrace_2260354
  have hstable : (prefixWord ++ tailWord_2260354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260354).length < 2 ^ (prefixWord ++ tailWord_2260354).sum := by decide
  have hdescent : baseEnd_2260354 < baseStart_2260354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260386 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2260386 : Nat := 118140960795 + 2260386 * 2 ^ 59
def prefixEnd_2260386 : Nat := 4983230072969 + 3 ^ 40 * 2260386 * 2
def baseEnd_2260386 : Nat := 773776321795932308719787

theorem tailTrace_2260386 : CollatzResearch.WordTrace tailWord_2260386 prefixEnd_2260386 773776321795932308719787 := by
  unfold tailWord_2260386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20610762597253760009860253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54962033592676693359627341 20610762597253760009860253)
  ·
    refine ⟨7729035973970160003697595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20610762597253760009860253 7729035973970160003697595)
    ·
      refine ⟨11593553960955240005546393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729035973970160003697595 11593553960955240005546393)
      ·
        refine ⟨8695165470716430004159795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11593553960955240005546393 8695165470716430004159795)
        ·
          refine ⟨13042748206074645006239693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695165470716430004159795 13042748206074645006239693)
          ·
            refine ⟨4891030577277991877339885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13042748206074645006239693 4891030577277991877339885)
            ·
              refine ⟨1834136466479246954002457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4891030577277991877339885 1834136466479246954002457)
              ·
                refine ⟨1375602349859435215501843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834136466479246954002457 1375602349859435215501843)
                ·
                  refine ⟨2063403524789152823252765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375602349859435215501843 2063403524789152823252765)
                  ·
                    refine ⟨773776321795932308719787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063403524789152823252765 773776321795932308719787)
                    ·
                      rfl

theorem cell22_2260386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2260386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260386 prefixEnd_2260386 := by exact prefixLift 2260386
  have htrace : WordTrace (prefixWord ++ tailWord_2260386) baseStart_2260386 baseEnd_2260386 := by
    simpa [prefixWord, tailWord_2260386, baseEnd_2260386] using wordTrace_append hprefix tailTrace_2260386
  have hstable : (prefixWord ++ tailWord_2260386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260386).length < 2 ^ (prefixWord ++ tailWord_2260386).sum := by decide
  have hdescent : baseEnd_2260386 < baseStart_2260386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260412 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_2260412 : Nat := 118140960795 + 2260412 * 2 ^ 59
def prefixEnd_2260412 : Nat := 4983230072969 + 3 ^ 40 * 2260412 * 2
def baseEnd_2260412 : Nat := 773785222127276907569707

theorem tailTrace_2260412 : CollatzResearch.WordTrace tailWord_2260412 prefixEnd_2260412 773785222127276907569707 := by
  unfold tailWord_2260412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41221999343460423239943745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54962665791280564319924993 41221999343460423239943745)
  ·
    refine ⟨30916499507595317429957809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41221999343460423239943745 30916499507595317429957809)
    ·
      refine ⟨23187374630696488072468357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30916499507595317429957809 23187374630696488072468357)
      ·
        refine ⟨4347632743255591513587817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23187374630696488072468357 4347632743255591513587817)
        ·
          refine ⟨3260724557441693635190863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4347632743255591513587817 3260724557441693635190863)
          ·
            refine ⟨4891086836162540452786295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260724557441693635190863 4891086836162540452786295)
            ·
              refine ⟨7336630254243810679179443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891086836162540452786295 7336630254243810679179443)
              ·
                refine ⟨11004945381365716018769165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7336630254243810679179443 11004945381365716018769165)
                ·
                  refine ⟨4126854518012143507038437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11004945381365716018769165 4126854518012143507038437)
                  ·
                    refine ⟨773785222127276907569707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126854518012143507038437 773785222127276907569707)
                    ·
                      rfl

theorem cell22_2260412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_2260412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260412 prefixEnd_2260412 := by exact prefixLift 2260412
  have htrace : WordTrace (prefixWord ++ tailWord_2260412) baseStart_2260412 baseEnd_2260412 := by
    simpa [prefixWord, tailWord_2260412, baseEnd_2260412] using wordTrace_append hprefix tailTrace_2260412
  have hstable : (prefixWord ++ tailWord_2260412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260412).length < 2 ^ (prefixWord ++ tailWord_2260412).sum := by decide
  have hdescent : baseEnd_2260412 < baseStart_2260412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260440 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_2260440 : Nat := 118140960795 + 2260440 * 2 ^ 59
def prefixEnd_2260440 : Nat := 4983230072969 + 3 ^ 40 * 2260440 * 2
def baseEnd_2260440 : Nat := 773794807099494167869621

theorem tailTrace_2260440 : CollatzResearch.WordTrace tailWord_2260440 prefixEnd_2260440 773794807099494167869621 := by
  unfold tailWord_2260440
  simp only [CollatzResearch.WordTrace]
  refine ⟨41222509965409703630953387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54963346620546271507937849 41222509965409703630953387)
  ·
    refine ⟨61833764948114555446430081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41222509965409703630953387 61833764948114555446430081)
    ·
      refine ⟨46375323711085916584822561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61833764948114555446430081 46375323711085916584822561)
      ·
        refine ⟨34781492783314437438616921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46375323711085916584822561 34781492783314437438616921)
        ·
          refine ⟨26086119587485828078962691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34781492783314437438616921 26086119587485828078962691)
          ·
            refine ⟨39129179381228742118444037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26086119587485828078962691 39129179381228742118444037)
            ·
              refine ⟨7336721133980389147208257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39129179381228742118444037 7336721133980389147208257)
              ·
                refine ⟨5502540850485291860406193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7336721133980389147208257 5502540850485291860406193)
                ·
                  refine ⟨4126905637863968895304645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502540850485291860406193 4126905637863968895304645)
                  ·
                    refine ⟨773794807099494167869621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4126905637863968895304645 773794807099494167869621)
                    ·
                      rfl

theorem cell22_2260440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_2260440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260440 prefixEnd_2260440 := by exact prefixLift 2260440
  have htrace : WordTrace (prefixWord ++ tailWord_2260440) baseStart_2260440 baseEnd_2260440 := by
    simpa [prefixWord, tailWord_2260440, baseEnd_2260440] using wordTrace_append hprefix tailTrace_2260440
  have hstable : (prefixWord ++ tailWord_2260440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260440).length < 2 ^ (prefixWord ++ tailWord_2260440).sum := by decide
  have hdescent : baseEnd_2260440 < baseStart_2260440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260442 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_2260442 : Nat := 118140960795 + 2260442 * 2 ^ 59
def prefixEnd_2260442 : Nat := 4983230072969 + 3 ^ 40 * 2260442 * 2
def baseEnd_2260442 : Nat := 773795491740366829319615

theorem tailTrace_2260442 : CollatzResearch.WordTrace tailWord_2260442 prefixEnd_2260442 773795491740366829319615 := by
  unfold tailWord_2260442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611273219203040400869895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54963395251208107735653053 20611273219203040400869895)
  ·
    refine ⟨30916909828804560601304843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20611273219203040400869895 30916909828804560601304843)
    ·
      refine ⟨46375364743206840901957265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30916909828804560601304843 46375364743206840901957265)
      ·
        refine ⟨34781523557405130676467949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46375364743206840901957265 34781523557405130676467949)
        ·
          refine ⟨13043071334026924003675481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34781523557405130676467949 13043071334026924003675481)
          ·
            refine ⟨9782303500520193002756611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13043071334026924003675481 9782303500520193002756611)
            ·
              refine ⟨14673455250780289504134917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9782303500520193002756611 14673455250780289504134917)
              ·
                refine ⟨2751272859521304282025297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14673455250780289504134917 2751272859521304282025297)
                ·
                  refine ⟨2063454644640978211518973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751272859521304282025297 2063454644640978211518973)
                  ·
                    refine ⟨773795491740366829319615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063454644640978211518973 773795491740366829319615)
                    ·
                      rfl

theorem cell22_2260442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_2260442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260442 prefixEnd_2260442 := by exact prefixLift 2260442
  have htrace : WordTrace (prefixWord ++ tailWord_2260442) baseStart_2260442 baseEnd_2260442 := by
    simpa [prefixWord, tailWord_2260442, baseEnd_2260442] using wordTrace_append hprefix tailTrace_2260442
  have hstable : (prefixWord ++ tailWord_2260442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260442).length < 2 ^ (prefixWord ++ tailWord_2260442).sum := by decide
  have hdescent : baseEnd_2260442 < baseStart_2260442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260455 : List Nat := [1, 1, 5, 2, 1, 2, 3, 7]
def baseStart_2260455 : Nat := 118140960795 + 2260455 * 2 ^ 59
def prefixEnd_2260455 : Nat := 4983230072969 + 3 ^ 40 * 2260455 * 2
def baseEnd_2260455 : Nat := 85977771322893236527175

theorem tailTrace_2260455 : CollatzResearch.WordTrace tailWord_2260455 prefixEnd_2260455 85977771322893236527175 := by
  unfold tailWord_2260455
  simp only [CollatzResearch.WordTrace]
  refine ⟨82445567025765064823702819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54963711350510043215801879 82445567025765064823702819)
  ·
    refine ⟨123668350538647597235554229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82445567025765064823702819 123668350538647597235554229)
    ·
      refine ⟨11593907862998212240833209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123668350538647597235554229 11593907862998212240833209)
      ·
        refine ⟨8695430897248659180624907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11593907862998212240833209 8695430897248659180624907)
        ·
          refine ⟨13043146345872988770937361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8695430897248659180624907 13043146345872988770937361)
          ·
            refine ⟨9782359759404741578203021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13043146345872988770937361 9782359759404741578203021)
            ·
              refine ⟨3668384909776778091826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9782359759404741578203021 3668384909776778091826133)
              ·
                refine ⟨85977771322893236527175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3668384909776778091826133 85977771322893236527175)
                ·
                  rfl

theorem cell22_2260455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 7].length) (baseStart_2260455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260455 prefixEnd_2260455 := by exact prefixLift 2260455
  have htrace : WordTrace (prefixWord ++ tailWord_2260455) baseStart_2260455 baseEnd_2260455 := by
    simpa [prefixWord, tailWord_2260455, baseEnd_2260455] using wordTrace_append hprefix tailTrace_2260455
  have hstable : (prefixWord ++ tailWord_2260455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260455).length < 2 ^ (prefixWord ++ tailWord_2260455).sum := by decide
  have hdescent : baseEnd_2260455 < baseStart_2260455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260504 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_2260504 : Nat := 118140960795 + 2260504 * 2 ^ 59
def prefixEnd_2260504 : Nat := 4983230072969 + 3 ^ 40 * 2260504 * 2
def baseEnd_2260504 : Nat := 773816715607419334269425

theorem tailTrace_2260504 : CollatzResearch.WordTrace tailWord_2260504 prefixEnd_2260504 773816715607419334269425 := by
  unfold tailWord_2260504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41223677101293773096118283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54964902801725030794824377 41223677101293773096118283)
  ·
    refine ⟨61835515651940659644177425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41223677101293773096118283 61835515651940659644177425)
    ·
      refine ⟨46376636738955494733133069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61835515651940659644177425 46376636738955494733133069)
      ·
        refine ⟨17391238777108310524924901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46376636738955494733133069 17391238777108310524924901)
        ·
          refine ⟨3260857270707808223423419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17391238777108310524924901 3260857270707808223423419)
          ·
            refine ⟨4891285906061712335135129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260857270707808223423419 4891285906061712335135129)
            ·
              refine ⟨3668464429546284251351347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4891285906061712335135129 3668464429546284251351347)
              ·
                refine ⟨5502696644319426377027021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668464429546284251351347 5502696644319426377027021)
                ·
                  refine ⟨2063511241619784891385133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5502696644319426377027021 2063511241619784891385133)
                  ·
                    refine ⟨773816715607419334269425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063511241619784891385133 773816715607419334269425)
                    ·
                      rfl

theorem cell22_2260504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_2260504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260504 prefixEnd_2260504 := by exact prefixLift 2260504
  have htrace : WordTrace (prefixWord ++ tailWord_2260504) baseStart_2260504 baseEnd_2260504 := by
    simpa [prefixWord, tailWord_2260504, baseEnd_2260504] using wordTrace_append hprefix tailTrace_2260504
  have hstable : (prefixWord ++ tailWord_2260504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260504).length < 2 ^ (prefixWord ++ tailWord_2260504).sum := by decide
  have hdescent : baseEnd_2260504 < baseStart_2260504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260510 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2260510 : Nat := 118140960795 + 2260510 * 2 ^ 59
def prefixEnd_2260510 : Nat := 4983230072969 + 3 ^ 40 * 2260510 * 2
def baseEnd_2260510 : Nat := 773818769530037318619407

theorem tailTrace_2260510 : CollatzResearch.WordTrace tailWord_2260510 prefixEnd_2260510 773818769530037318619407 := by
  unfold tailWord_2260510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305946630070726152119373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54965048693710539477969989 10305946630070726152119373)
  ·
    refine ⟨3864729986276522307044765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10305946630070726152119373 3864729986276522307044765)
    ·
      refine ⟨1449273744853695865141787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3864729986276522307044765 1449273744853695865141787)
      ·
        refine ⟨2173910617280543797712681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449273744853695865141787 2173910617280543797712681)
        ·
          refine ⟨1630432962960407848284511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2173910617280543797712681 1630432962960407848284511)
          ·
            refine ⟨2445649444440611772426767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630432962960407848284511 2445649444440611772426767)
            ·
              refine ⟨3668474166660917658640151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445649444440611772426767 3668474166660917658640151)
              ·
                refine ⟨5502711249991376487960227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668474166660917658640151 5502711249991376487960227)
                ·
                  refine ⟨8254066874987064731940341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5502711249991376487960227 8254066874987064731940341)
                  ·
                    refine ⟨773818769530037318619407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8254066874987064731940341 773818769530037318619407)
                    ·
                      rfl

theorem cell22_2260510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2260510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260510 prefixEnd_2260510 := by exact prefixLift 2260510
  have htrace : WordTrace (prefixWord ++ tailWord_2260510) baseStart_2260510 baseEnd_2260510 := by
    simpa [prefixWord, tailWord_2260510, baseEnd_2260510] using wordTrace_append hprefix tailTrace_2260510
  have hstable : (prefixWord ++ tailWord_2260510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260510).length < 2 ^ (prefixWord ++ tailWord_2260510).sum := by decide
  have hdescent : baseEnd_2260510 < baseStart_2260510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260562 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_2260562 : Nat := 118140960795 + 2260562 * 2 ^ 59
def prefixEnd_2260562 : Nat := 4983230072969 + 3 ^ 40 * 2260562 * 2
def baseEnd_2260562 : Nat := 257945523397575505439749

theorem tailTrace_2260562 : CollatzResearch.WordTrace tailWord_2260562 prefixEnd_2260562 257945523397575505439749 := by
  unfold tailWord_2260562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612367409094355524461985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54966313090918281398565293 20612367409094355524461985)
  ·
    refine ⟨15459275556820766643346489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20612367409094355524461985 15459275556820766643346489)
    ·
      refine ⟨11594456667615574982509867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15459275556820766643346489 11594456667615574982509867)
      ·
        refine ⟨17391685001423362473764801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594456667615574982509867 17391685001423362473764801)
        ·
          refine ⟨13043763751067521855323601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17391685001423362473764801 13043763751067521855323601)
          ·
            refine ⟨9782822813300641391492701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13043763751067521855323601 9782822813300641391492701)
            ·
              refine ⟨3668558554987740521809763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9782822813300641391492701 3668558554987740521809763)
              ·
                refine ⟨5502837832481610782714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668558554987740521809763 5502837832481610782714645)
                ·
                  refine ⟨257945523397575505439749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5502837832481610782714645 257945523397575505439749)
                  ·
                    rfl

theorem cell22_2260562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_2260562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260562 prefixEnd_2260562 := by exact prefixLift 2260562
  have htrace : WordTrace (prefixWord ++ tailWord_2260562) baseStart_2260562 baseEnd_2260562 := by
    simpa [prefixWord, tailWord_2260562, baseEnd_2260562] using wordTrace_append hprefix tailTrace_2260562
  have hstable : (prefixWord ++ tailWord_2260562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260562).length < 2 ^ (prefixWord ++ tailWord_2260562).sum := by decide
  have hdescent : baseEnd_2260562 < baseStart_2260562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260592 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_2260592 : Nat := 118140960795 + 2260592 * 2 ^ 59
def prefixEnd_2260592 : Nat := 4983230072969 + 3 ^ 40 * 2260592 * 2
def baseEnd_2260592 : Nat := 773846839805816438069155

theorem tailTrace_2260592 : CollatzResearch.WordTrace tailWord_2260592 prefixEnd_2260592 773846839805816438069155 := by
  unfold tailWord_2260592
  simp only [CollatzResearch.WordTrace]
  refine ⟨41225281913134368610720015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54967042550845824814293353 41225281913134368610720015)
  ·
    refine ⟨61837922869701552916080023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41225281913134368610720015 61837922869701552916080023)
    ·
      refine ⟨92756884304552329374120035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61837922869701552916080023 92756884304552329374120035)
      ·
        refine ⟨139135326456828494061180053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92756884304552329374120035 139135326456828494061180053)
        ·
          refine ⟨6521968427663835659117815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139135326456828494061180053 6521968427663835659117815)
          ·
            refine ⟨9782952641495753488676723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6521968427663835659117815 9782952641495753488676723)
            ·
              refine ⟨14674428962243630233015085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9782952641495753488676723 14674428962243630233015085)
              ·
                refine ⟨5502910860841361337380657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14674428962243630233015085 5502910860841361337380657)
                ·
                  refine ⟨4127183145631021003035493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5502910860841361337380657 4127183145631021003035493)
                  ·
                    refine ⟨773846839805816438069155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127183145631021003035493 773846839805816438069155)
                    ·
                      rfl

theorem cell22_2260592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_2260592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260592 prefixEnd_2260592 := by exact prefixLift 2260592
  have htrace : WordTrace (prefixWord ++ tailWord_2260592) baseStart_2260592 baseEnd_2260592 := by
    simpa [prefixWord, tailWord_2260592, baseEnd_2260592] using wordTrace_append hprefix tailTrace_2260592
  have hstable : (prefixWord ++ tailWord_2260592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260592).length < 2 ^ (prefixWord ++ tailWord_2260592).sum := by decide
  have hdescent : baseEnd_2260592 < baseStart_2260592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260620 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_2260620 : Nat := 118140960795 + 2260620 * 2 ^ 59
def prefixEnd_2260620 : Nat := 4983230072969 + 3 ^ 40 * 2260620 * 2
def baseEnd_2260620 : Nat := 773856424778033698369069

theorem tailTrace_2260620 : CollatzResearch.WordTrace tailWord_2260620 prefixEnd_2260620 773856424778033698369069 := by
  unfold tailWord_2260620
  simp only [CollatzResearch.WordTrace]
  refine ⟨41225792535083649001729657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54967723380111532002306209 41225792535083649001729657)
  ·
    refine ⟨30919344401312736751297243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41225792535083649001729657 30919344401312736751297243)
    ·
      refine ⟨46379016601969105126945865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30919344401312736751297243 46379016601969105126945865)
      ·
        refine ⟨34784262451476828845209399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46379016601969105126945865 34784262451476828845209399)
        ·
          refine ⟨52176393677215243267814099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34784262451476828845209399 52176393677215243267814099)
          ·
            refine ⟨78264590515822864901721149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52176393677215243267814099 78264590515822864901721149)
            ·
              refine ⟨29349221443433574338145431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78264590515822864901721149 29349221443433574338145431)
              ·
                refine ⟨44023832165150361507218147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29349221443433574338145431 44023832165150361507218147)
                ·
                  refine ⟨66035748247725542260827221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44023832165150361507218147 66035748247725542260827221)
                  ·
                    refine ⟨773856424778033698369069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66035748247725542260827221 773856424778033698369069)
                    ·
                      rfl

theorem cell22_2260620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_2260620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260620 prefixEnd_2260620 := by exact prefixLift 2260620
  have htrace : WordTrace (prefixWord ++ tailWord_2260620) baseStart_2260620 baseEnd_2260620 := by
    simpa [prefixWord, tailWord_2260620, baseEnd_2260620] using wordTrace_append hprefix tailTrace_2260620
  have hstable : (prefixWord ++ tailWord_2260620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260620).length < 2 ^ (prefixWord ++ tailWord_2260620).sum := by decide
  have hdescent : baseEnd_2260620 < baseStart_2260620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260697 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 6]
def baseStart_2260697 : Nat := 118140960795 + 2260697 * 2 ^ 59
def prefixEnd_2260697 : Nat := 4983230072969 + 3 ^ 40 * 2260697 * 2
def baseEnd_2260697 : Nat := 257960927817210388064611

theorem tailTrace_2260697 : CollatzResearch.WordTrace tailWord_2260697 prefixEnd_2260697 257960927817210388064611 := by
  unfold tailWord_2260697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82454393490888340154012345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54969595660592226769341563 82454393490888340154012345)
  ·
    refine ⟨61840795118166255115509259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82454393490888340154012345 61840795118166255115509259)
    ·
      refine ⟨92761192677249382673263889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61840795118166255115509259 92761192677249382673263889)
      ·
        refine ⟨69570894507937037004947917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92761192677249382673263889 69570894507937037004947917)
        ·
          refine ⟨26089085440476388876855469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69570894507937037004947917 26089085440476388876855469)
          ·
            refine ⟨9783407040178645828820801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26089085440476388876855469 9783407040178645828820801)
            ·
              refine ⟨7337555280133984371615601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9783407040178645828820801 7337555280133984371615601)
              ·
                refine ⟨5503166460100488278711701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7337555280133984371615601 5503166460100488278711701)
                ·
                  refine ⟨257960927817210388064611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5503166460100488278711701 257960927817210388064611)
                  ·
                    rfl

theorem cell22_2260697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_2260697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260697 prefixEnd_2260697 := by exact prefixLift 2260697
  have htrace : WordTrace (prefixWord ++ tailWord_2260697) baseStart_2260697 baseEnd_2260697 := by
    simpa [prefixWord, tailWord_2260697, baseEnd_2260697] using wordTrace_append hprefix tailTrace_2260697
  have hstable : (prefixWord ++ tailWord_2260697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260697).length < 2 ^ (prefixWord ++ tailWord_2260697).sum := by decide
  have hdescent : baseEnd_2260697 < baseStart_2260697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260727 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2260727 : Nat := 118140960795 + 2260727 * 2 ^ 59
def prefixEnd_2260727 : Nat := 4983230072969 + 3 ^ 40 * 2260727 * 2
def baseEnd_2260727 : Nat := 773893053064721085943741

theorem tailTrace_2260727 : CollatzResearch.WordTrace tailWord_2260727 prefixEnd_2260727 773893053064721085943741 := by
  unfold tailWord_2260727
  simp only [CollatzResearch.WordTrace]
  refine ⟨82455487680779655277604435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54970325120519770185069623 82455487680779655277604435)
  ·
    refine ⟨123683231521169482916406653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82455487680779655277604435 123683231521169482916406653)
    ·
      refine ⟨46381211820438556093652495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123683231521169482916406653 46381211820438556093652495)
      ·
        refine ⟨69571817730657834140478743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46381211820438556093652495 69571817730657834140478743)
        ·
          refine ⟨104357726595986751210718115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69571817730657834140478743 104357726595986751210718115)
          ·
            refine ⟨156536589893980126816077173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104357726595986751210718115 156536589893980126816077173)
            ·
              refine ⟨14675305302560636889007235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156536589893980126816077173 14675305302560636889007235)
              ·
                refine ⟨22012957953840955333510853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14675305302560636889007235 22012957953840955333510853)
                ·
                  refine ⟨4127429616345179125033285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22012957953840955333510853 4127429616345179125033285)
                  ·
                    refine ⟨773893053064721085943741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127429616345179125033285 773893053064721085943741)
                    ·
                      rfl

theorem cell22_2260727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2260727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260727 prefixEnd_2260727 := by exact prefixLift 2260727
  have htrace : WordTrace (prefixWord ++ tailWord_2260727) baseStart_2260727 baseEnd_2260727 := by
    simpa [prefixWord, tailWord_2260727, baseEnd_2260727] using wordTrace_append hprefix tailTrace_2260727
  have hstable : (prefixWord ++ tailWord_2260727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260727).length < 2 ^ (prefixWord ++ tailWord_2260727).sum := by decide
  have hdescent : baseEnd_2260727 < baseStart_2260727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260746 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_2260746 : Nat := 118140960795 + 2260746 * 2 ^ 59
def prefixEnd_2260746 : Nat := 4983230072969 + 3 ^ 40 * 2260746 * 2
def baseEnd_2260746 : Nat := 773899557153011369718683

theorem tailTrace_2260746 : CollatzResearch.WordTrace tailWord_2260746 prefixEnd_2260746 773899557153011369718683 := by
  unfold tailWord_2260746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20614045166927705380636523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54970787111807214348364061 20614045166927705380636523)
  ·
    refine ⟨30921067750391558070954785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20614045166927705380636523 30921067750391558070954785)
    ·
      refine ⟨23190800812793668553216089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30921067750391558070954785 23190800812793668553216089)
      ·
        refine ⟨17393100609595251414912067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23190800812793668553216089 17393100609595251414912067)
        ·
          refine ⟨26089650914392877122368101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17393100609595251414912067 26089650914392877122368101)
          ·
            refine ⟨4891809546448664460444019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26089650914392877122368101 4891809546448664460444019)
            ·
              refine ⟨7337714319672996690666029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891809546448664460444019 7337714319672996690666029)
              ·
                refine ⟨2751642869877373758999761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7337714319672996690666029 2751642869877373758999761)
                ·
                  refine ⟨2063732152408030319249821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2751642869877373758999761 2063732152408030319249821)
                  ·
                    refine ⟨773899557153011369718683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063732152408030319249821 773899557153011369718683)
                    ·
                      rfl

theorem cell22_2260746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_2260746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260746 prefixEnd_2260746 := by exact prefixLift 2260746
  have htrace : WordTrace (prefixWord ++ tailWord_2260746) baseStart_2260746 baseEnd_2260746 := by
    simpa [prefixWord, tailWord_2260746, baseEnd_2260746] using wordTrace_append hprefix tailTrace_2260746
  have hstable : (prefixWord ++ tailWord_2260746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260746).length < 2 ^ (prefixWord ++ tailWord_2260746).sum := by decide
  have hdescent : baseEnd_2260746 < baseStart_2260746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260782 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_2260782 : Nat := 118140960795 + 2260782 * 2 ^ 59
def prefixEnd_2260782 : Nat := 4983230072969 + 3 ^ 40 * 2260782 * 2
def baseEnd_2260782 : Nat := 257970626896239758606191

theorem tailTrace_2260782 : CollatzResearch.WordTrace tailWord_2260782 prefixEnd_2260782 257970626896239758606191 := by
  unfold tailWord_2260782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307186711947549958857075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54971662463720266447237733 10307186711947549958857075)
  ·
    refine ⟨15460780067921324938285613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10307186711947549958857075 15460780067921324938285613)
    ·
      refine ⟨5797792525470496851857105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15460780067921324938285613 5797792525470496851857105)
      ·
        refine ⟨4348344394102872638892829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5797792525470496851857105 4348344394102872638892829)
        ·
          refine ⟨1630629147788577239584811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4348344394102872638892829 1630629147788577239584811)
          ·
            refine ⟨2445943721682865859377217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630629147788577239584811 2445943721682865859377217)
            ·
              refine ⟨1834457791262149394532913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445943721682865859377217 1834457791262149394532913)
              ·
                refine ⟨1375843343446612045899685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834457791262149394532913 1375843343446612045899685)
                ·
                  refine ⟨257970626896239758606191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375843343446612045899685 257970626896239758606191)
                  ·
                    rfl

theorem cell22_2260782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_2260782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260782 prefixEnd_2260782 := by exact prefixLift 2260782
  have htrace : WordTrace (prefixWord ++ tailWord_2260782) baseStart_2260782 baseEnd_2260782 := by
    simpa [prefixWord, tailWord_2260782, baseEnd_2260782] using wordTrace_append hprefix tailTrace_2260782
  have hstable : (prefixWord ++ tailWord_2260782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260782).length < 2 ^ (prefixWord ++ tailWord_2260782).sum := by decide
  have hdescent : baseEnd_2260782 < baseStart_2260782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260793 : List Nat := [1, 2, 1, 7, 2, 1, 1, 7]
def baseStart_2260793 : Nat := 118140960795 + 2260793 * 2 ^ 59
def prefixEnd_2260793 : Nat := 4983230072969 + 3 ^ 40 * 2260793 * 2
def baseEnd_2260793 : Nat := 85990627357057657088171

theorem tailTrace_2260793 : CollatzResearch.WordTrace tailWord_2260793 prefixEnd_2260793 85990627357057657088171 := by
  unfold tailWord_2260793
  simp only [CollatzResearch.WordTrace]
  refine ⟨82457894898540548549507033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54971929932360365699671355 82457894898540548549507033)
  ·
    refine ⟨61843421173905411412130275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82457894898540548549507033 61843421173905411412130275)
    ·
      refine ⟨92765131760858117118195413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61843421173905411412130275 92765131760858117118195413)
      ·
        refine ⟨2174182775645112119957705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 92765131760858117118195413 2174182775645112119957705)
        ·
          refine ⟨1630637081733834089968279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2174182775645112119957705 1630637081733834089968279)
          ·
            refine ⟨2445955622600751134952419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630637081733834089968279 2445955622600751134952419)
            ·
              refine ⟨3668933433901126702428629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445955622600751134952419 3668933433901126702428629)
              ·
                refine ⟨85990627357057657088171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3668933433901126702428629 85990627357057657088171)
                ·
                  rfl

theorem cell22_2260793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 7].length) (baseStart_2260793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260793 prefixEnd_2260793 := by exact prefixLift 2260793
  have htrace : WordTrace (prefixWord ++ tailWord_2260793) baseStart_2260793 baseEnd_2260793 := by
    simpa [prefixWord, tailWord_2260793, baseEnd_2260793] using wordTrace_append hprefix tailTrace_2260793
  have hstable : (prefixWord ++ tailWord_2260793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260793).length < 2 ^ (prefixWord ++ tailWord_2260793).sum := by decide
  have hdescent : baseEnd_2260793 < baseStart_2260793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260847 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_2260847 : Nat := 118140960795 + 2260847 * 2 ^ 59
def prefixEnd_2260847 : Nat := 4983230072969 + 3 ^ 40 * 2260847 * 2
def baseEnd_2260847 : Nat := 773934131517080772943373

theorem tailTrace_2260847 : CollatzResearch.WordTrace tailWord_2260847 prefixEnd_2260847 773934131517080772943373 := by
  unfold tailWord_2260847
  simp only [CollatzResearch.WordTrace]
  refine ⟨82459864440344915771972795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54973242960229943847981863 82459864440344915771972795)
  ·
    refine ⟨123689796660517373657959193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82459864440344915771972795 123689796660517373657959193)
    ·
      refine ⟨92767347495388030243469395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123689796660517373657959193 92767347495388030243469395)
      ·
        refine ⟨139151021243082045365204093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92767347495388030243469395 139151021243082045365204093)
        ·
          refine ⟨52181632966155767011951535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139151021243082045365204093 52181632966155767011951535)
          ·
            refine ⟨78272449449233650517927303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52181632966155767011951535 78272449449233650517927303)
            ·
              refine ⟨117408674173850475776890955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78272449449233650517927303 117408674173850475776890955)
              ·
                refine ⟨176113011260775713665336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117408674173850475776890955 176113011260775713665336433)
                ·
                  refine ⟨132084758445581785249002325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176113011260775713665336433 132084758445581785249002325)
                  ·
                    refine ⟨773934131517080772943373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 132084758445581785249002325 773934131517080772943373)
                    ·
                      rfl

theorem cell22_2260847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_2260847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260847 prefixEnd_2260847 := by exact prefixLift 2260847
  have htrace : WordTrace (prefixWord ++ tailWord_2260847) baseStart_2260847 baseEnd_2260847 := by
    simpa [prefixWord, tailWord_2260847, baseEnd_2260847] using wordTrace_append hprefix tailTrace_2260847
  have hstable : (prefixWord ++ tailWord_2260847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260847).length < 2 ^ (prefixWord ++ tailWord_2260847).sum := by decide
  have hdescent : baseEnd_2260847 < baseStart_2260847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260849 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 6]
def baseStart_2260849 : Nat := 118140960795 + 2260849 * 2 ^ 59
def prefixEnd_2260849 : Nat := 4983230072969 + 3 ^ 40 * 2260849 * 2
def baseEnd_2260849 : Nat := 257978272052651144797789

theorem tailTrace_2260849 : CollatzResearch.WordTrace tailWord_2260849 prefixEnd_2260849 257978272052651144797789 := by
  unfold tailWord_2260849
  simp only [CollatzResearch.WordTrace]
  refine ⟨82459937386337670113545601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54973291590891780075697067 82459937386337670113545601)
  ·
    refine ⟨61844953039753252585159201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82459937386337670113545601 61844953039753252585159201)
    ·
      refine ⟨46383714779814939438869401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61844953039753252585159201 46383714779814939438869401)
      ·
        refine ⟨34787786084861204579152051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46383714779814939438869401 34787786084861204579152051)
        ·
          refine ⟨52181679127291806868728077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34787786084861204579152051 52181679127291806868728077)
          ·
            refine ⟨19568129672734427575773029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52181679127291806868728077 19568129672734427575773029)
            ·
              refine ⟨3669024313637705170457443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19568129672734427575773029 3669024313637705170457443)
              ·
                refine ⟨5503536470456557755686165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669024313637705170457443 5503536470456557755686165)
                ·
                  refine ⟨257978272052651144797789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5503536470456557755686165 257978272052651144797789)
                  ·
                    rfl

theorem cell22_2260849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_2260849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260849 prefixEnd_2260849 := by exact prefixLift 2260849
  have htrace : WordTrace (prefixWord ++ tailWord_2260849) baseStart_2260849 baseEnd_2260849 := by
    simpa [prefixWord, tailWord_2260849, baseEnd_2260849] using wordTrace_append hprefix tailTrace_2260849
  have hstable : (prefixWord ++ tailWord_2260849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260849).length < 2 ^ (prefixWord ++ tailWord_2260849).sum := by decide
  have hdescent : baseEnd_2260849 < baseStart_2260849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260943 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 1, 3]
def baseStart_2260943 : Nat := 118140960795 + 2260943 * 2 ^ 59
def prefixEnd_2260943 : Nat := 4983230072969 + 3 ^ 40 * 2260943 * 2
def baseEnd_2260943 : Nat := 773966994278968522543079

theorem tailTrace_2260943 : CollatzResearch.WordTrace tailWord_2260943 prefixEnd_2260943 773966994278968522543079 := by
  unfold tailWord_2260943
  simp only [CollatzResearch.WordTrace]
  refine ⟨82463365847997124167467483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54975577231998082778311655 82463365847997124167467483)
  ·
    refine ⟨123695048771995686251201225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82463365847997124167467483 123695048771995686251201225)
    ·
      refine ⟨92771286578996764688400919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123695048771995686251201225 92771286578996764688400919)
      ·
        refine ⟨139156929868495147032601379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92771286578996764688400919 139156929868495147032601379)
        ·
          refine ⟨208735394802742720548902069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139156929868495147032601379 208735394802742720548902069)
          ·
            refine ⟨19568943262757130051459569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 208735394802742720548902069 19568943262757130051459569)
            ·
              refine ⟨14676707447067847538594677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19568943262757130051459569 14676707447067847538594677)
              ·
                refine ⟨1375941323162610706743251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14676707447067847538594677 1375941323162610706743251)
                ·
                  refine ⟨2063911984743916060114877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1375941323162610706743251 2063911984743916060114877)
                  ·
                    refine ⟨773966994278968522543079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2063911984743916060114877 773966994278968522543079)
                    ·
                      rfl

theorem cell22_2260943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 3].length) (baseStart_2260943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260943 prefixEnd_2260943 := by exact prefixLift 2260943
  have htrace : WordTrace (prefixWord ++ tailWord_2260943) baseStart_2260943 baseEnd_2260943 := by
    simpa [prefixWord, tailWord_2260943, baseEnd_2260943] using wordTrace_append hprefix tailTrace_2260943
  have hstable : (prefixWord ++ tailWord_2260943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260943).length < 2 ^ (prefixWord ++ tailWord_2260943).sum := by decide
  have hdescent : baseEnd_2260943 < baseStart_2260943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2260984 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_2260984 : Nat := 118140960795 + 2260984 * 2 ^ 59
def prefixEnd_2260984 : Nat := 4983230072969 + 3 ^ 40 * 2260984 * 2
def baseEnd_2260984 : Nat := 257993676472286027422651

theorem tailTrace_2260984 : CollatzResearch.WordTrace tailWord_2260984 prefixEnd_2260984 257993676472286027422651 := by
  unfold tailWord_2260984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41232430620424294084855003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54976574160565725446473337 41232430620424294084855003)
  ·
    refine ⟨61848645930636441127282505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41232430620424294084855003 61848645930636441127282505)
    ·
      refine ⟨46386484447977330845461879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61848645930636441127282505 46386484447977330845461879)
      ·
        refine ⟨69579726671965996268192819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46386484447977330845461879 69579726671965996268192819)
        ·
          refine ⟨104369590007948994402289229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69579726671965996268192819 104369590007948994402289229)
          ·
            refine ⟨39138596252980872900858461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104369590007948994402289229 39138596252980872900858461)
            ·
              refine ⟨14676973594867827337821923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39138596252980872900858461 14676973594867827337821923)
              ·
                refine ⟨22015460392301741006732885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14676973594867827337821923 22015460392301741006732885)
                ·
                  refine ⟨257993676472286027422651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22015460392301741006732885 257993676472286027422651)
                  ·
                    rfl

theorem cell22_2260984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_2260984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2260984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2260984 prefixEnd_2260984 := by exact prefixLift 2260984
  have htrace : WordTrace (prefixWord ++ tailWord_2260984) baseStart_2260984 baseEnd_2260984 := by
    simpa [prefixWord, tailWord_2260984, baseEnd_2260984] using wordTrace_append hprefix tailTrace_2260984
  have hstable : (prefixWord ++ tailWord_2260984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2260984).length < 2 ^ (prefixWord ++ tailWord_2260984).sum := by decide
  have hdescent : baseEnd_2260984 < baseStart_2260984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2260984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261018 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_2261018 : Nat := 118140960795 + 2261018 * 2 ^ 59
def prefixEnd_2261018 : Nat := 4983230072969 + 3 ^ 40 * 2261018 * 2
def baseEnd_2261018 : Nat := 257997556103897775639283

theorem tailTrace_2261018 : CollatzResearch.WordTrace tailWord_2261018 prefixEnd_2261018 257997556103897775639283 := by
  unfold tailWord_2261018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616525330681352994111927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54977400881816941317631805 20616525330681352994111927)
  ·
    refine ⟨30924787996022029491167891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20616525330681352994111927 30924787996022029491167891)
    ·
      refine ⟨46387181994033044236751837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30924787996022029491167891 46387181994033044236751837)
      ·
        refine ⟨17395193247762391588781939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46387181994033044236751837 17395193247762391588781939)
        ·
          refine ⟨26092789871643587383172909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17395193247762391588781939 26092789871643587383172909)
          ·
            refine ⟨9784796201866345268689841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26092789871643587383172909 9784796201866345268689841)
            ·
              refine ⟨7338597151399758951517381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9784796201866345268689841 7338597151399758951517381)
              ·
                refine ⟨1375986965887454803409509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7338597151399758951517381 1375986965887454803409509)
                ·
                  refine ⟨257997556103897775639283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375986965887454803409509 257997556103897775639283)
                  ·
                    rfl

theorem cell22_2261018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_2261018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261018 prefixEnd_2261018 := by exact prefixLift 2261018
  have htrace : WordTrace (prefixWord ++ tailWord_2261018) baseStart_2261018 baseEnd_2261018 := by
    simpa [prefixWord, tailWord_2261018, baseEnd_2261018] using wordTrace_append hprefix tailTrace_2261018
  have hstable : (prefixWord ++ tailWord_2261018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261018).length < 2 ^ (prefixWord ++ tailWord_2261018).sum := by decide
  have hdescent : baseEnd_2261018 < baseStart_2261018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261076 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2261076 : Nat := 118140960795 + 2261076 * 2 ^ 59
def prefixEnd_2261076 : Nat := 4983230072969 + 3 ^ 40 * 2261076 * 2
def baseEnd_2261076 : Nat := 774012522897000508967671

theorem tailTrace_2261076 : CollatzResearch.WordTrace tailWord_2261076 prefixEnd_2261076 774012522897000508967671 := by
  unfold tailWord_2261076
  simp only [CollatzResearch.WordTrace]
  refine ⟨41234108378257643941029541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54978811171010191921372721 41234108378257643941029541)
  ·
    refine ⟨7731395320923308238943039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41234108378257643941029541 7731395320923308238943039)
    ·
      refine ⟨11597092981384962358414559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731395320923308238943039 11597092981384962358414559)
      ·
        refine ⟨17395639472077443537621839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597092981384962358414559 17395639472077443537621839)
        ·
          refine ⟨26093459208116165306432759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17395639472077443537621839 26093459208116165306432759)
          ·
            refine ⟨39140188812174247959649139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26093459208116165306432759 39140188812174247959649139)
            ·
              refine ⟨58710283218261371939473709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39140188812174247959649139 58710283218261371939473709)
              ·
                refine ⟨22016356206848014477302641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58710283218261371939473709 22016356206848014477302641)
                ·
                  refine ⟨16512267155136010857976981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22016356206848014477302641 16512267155136010857976981)
                  ·
                    refine ⟨774012522897000508967671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16512267155136010857976981 774012522897000508967671)
                    ·
                      rfl

theorem cell22_2261076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2261076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261076 prefixEnd_2261076 := by exact prefixLift 2261076
  have htrace : WordTrace (prefixWord ++ tailWord_2261076) baseStart_2261076 baseEnd_2261076 := by
    simpa [prefixWord, tailWord_2261076, baseEnd_2261076] using wordTrace_append hprefix tailTrace_2261076
  have hstable : (prefixWord ++ tailWord_2261076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261076).length < 2 ^ (prefixWord ++ tailWord_2261076).sum := by decide
  have hdescent : baseEnd_2261076 < baseStart_2261076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261136 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_2261136 : Nat := 118140960795 + 2261136 * 2 ^ 59
def prefixEnd_2261136 : Nat := 4983230072969 + 3 ^ 40 * 2261136 * 2
def baseEnd_2261136 : Nat := 258011020707726784155829

theorem tailTrace_2261136 : CollatzResearch.WordTrace tailWord_2261136 prefixEnd_2261136 258011020707726784155829 := by
  unfold tailWord_2261136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41235202568148959064621631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54980270090865278752828841 41235202568148959064621631)
  ·
    refine ⟨61852803852223438596932447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41235202568148959064621631 61852803852223438596932447)
    ·
      refine ⟨92779205778335157895398671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61852803852223438596932447 92779205778335157895398671)
      ·
        refine ⟨139168808667502736843098007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92779205778335157895398671 139168808667502736843098007)
        ·
          refine ⟨208753213001254105264647011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139168808667502736843098007 208753213001254105264647011)
          ·
            refine ⟨313129819501881157896970517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208753213001254105264647011 313129819501881157896970517)
            ·
              refine ⟨14677960289150679276420493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 313129819501881157896970517 14677960289150679276420493)
              ·
                refine ⟨5504235108431504728657685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14677960289150679276420493 5504235108431504728657685)
                ·
                  refine ⟨258011020707726784155829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5504235108431504728657685 258011020707726784155829)
                  ·
                    rfl

theorem cell22_2261136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_2261136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261136 prefixEnd_2261136 := by exact prefixLift 2261136
  have htrace : WordTrace (prefixWord ++ tailWord_2261136) baseStart_2261136 baseEnd_2261136 := by
    simpa [prefixWord, tailWord_2261136, baseEnd_2261136] using wordTrace_append hprefix tailTrace_2261136
  have hstable : (prefixWord ++ tailWord_2261136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261136).length < 2 ^ (prefixWord ++ tailWord_2261136).sum := by decide
  have hdescent : baseEnd_2261136 < baseStart_2261136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261138 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2261138 : Nat := 118140960795 + 2261138 * 2 ^ 59
def prefixEnd_2261138 : Nat := 4983230072969 + 3 ^ 40 * 2261138 * 2
def baseEnd_2261138 : Nat := 774033746764053013917481

theorem tailTrace_2261138 : CollatzResearch.WordTrace tailWord_2261138 prefixEnd_2261138 774033746764053013917481 := by
  unfold tailWord_2261138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617619520572668117704017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54980318721527114980544045 20617619520572668117704017)
  ·
    refine ⟨15463214640429501088278013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20617619520572668117704017 15463214640429501088278013)
    ·
      refine ⟨5798705490161062908104255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15463214640429501088278013 5798705490161062908104255)
      ·
        refine ⟨8698058235241594362156383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798705490161062908104255 8698058235241594362156383)
        ·
          refine ⟨13047087352862391543234575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698058235241594362156383 13047087352862391543234575)
          ·
            refine ⟨19570631029293587314851863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13047087352862391543234575 19570631029293587314851863)
            ·
              refine ⟨29355946543940380972277795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19570631029293587314851863 29355946543940380972277795)
              ·
                refine ⟨44033919815910571458416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29355946543940380972277795 44033919815910571458416693)
                ·
                  refine ⟨4128179982741616074226565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44033919815910571458416693 4128179982741616074226565)
                  ·
                    refine ⟨774033746764053013917481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128179982741616074226565 774033746764053013917481)
                    ·
                      rfl

theorem cell22_2261138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2261138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261138 prefixEnd_2261138 := by exact prefixLift 2261138
  have htrace : WordTrace (prefixWord ++ tailWord_2261138) baseStart_2261138 baseEnd_2261138 := by
    simpa [prefixWord, tailWord_2261138, baseEnd_2261138] using wordTrace_append hprefix tailTrace_2261138
  have hstable : (prefixWord ++ tailWord_2261138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261138).length < 2 ^ (prefixWord ++ tailWord_2261138).sum := by decide
  have hdescent : baseEnd_2261138 < baseStart_2261138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261153 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 6]
def baseStart_2261153 : Nat := 118140960795 + 2261153 * 2 ^ 59
def prefixEnd_2261153 : Nat := 4983230072969 + 3 ^ 40 * 2261153 * 2
def baseEnd_2261153 : Nat := 258012960523532658264145

theorem tailTrace_2261153 : CollatzResearch.WordTrace tailWord_2261153 prefixEnd_2261153 258012960523532658264145 := by
  unfold tailWord_2261153
  simp only [CollatzResearch.WordTrace]
  refine ⟨82471025177236330032612113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54980683451490886688408075 82471025177236330032612113)
  ·
    refine ⟨61853268882927247524459085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82471025177236330032612113 61853268882927247524459085)
    ·
      refine ⟨23194975831097717821672157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61853268882927247524459085 23194975831097717821672157)
      ·
        refine ⟨8698115936661644183127059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23194975831097717821672157 8698115936661644183127059)
        ·
          refine ⟨13047173904992466274690589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698115936661644183127059 13047173904992466274690589)
          ·
            refine ⟨4892690214372174853008971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13047173904992466274690589 4892690214372174853008971)
            ·
              refine ⟨7339035321558262279513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892690214372174853008971 7339035321558262279513457)
              ·
                refine ⟨5504276491168696709635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7339035321558262279513457 5504276491168696709635093)
                ·
                  refine ⟨258012960523532658264145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5504276491168696709635093 258012960523532658264145)
                  ·
                    rfl

theorem cell22_2261153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_2261153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261153 prefixEnd_2261153 := by exact prefixLift 2261153
  have htrace : WordTrace (prefixWord ++ tailWord_2261153) baseStart_2261153 baseEnd_2261153 := by
    simpa [prefixWord, tailWord_2261153, baseEnd_2261153] using wordTrace_append hprefix tailTrace_2261153
  have hstable : (prefixWord ++ tailWord_2261153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261153).length < 2 ^ (prefixWord ++ tailWord_2261153).sum := by decide
  have hdescent : baseEnd_2261153 < baseStart_2261153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261170 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_2261170 : Nat := 118140960795 + 2261170 * 2 ^ 59
def prefixEnd_2261170 : Nat := 4983230072969 + 3 ^ 40 * 2261170 * 2
def baseEnd_2261170 : Nat := 258014900339338532372461

theorem tailTrace_2261170 : CollatzResearch.WordTrace tailWord_2261170 prefixEnd_2261170 258014900339338532372461 := by
  unfold tailWord_2261170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617911304543685483995241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54981096812116494623987309 20617911304543685483995241)
  ·
    refine ⟨15463433478407764112996431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20617911304543685483995241 15463433478407764112996431)
    ·
      refine ⟨23195150217611646169494647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15463433478407764112996431 23195150217611646169494647)
      ·
        refine ⟨34792725326417469254241971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23195150217611646169494647 34792725326417469254241971)
        ·
          refine ⟨52189087989626203881362957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34792725326417469254241971 52189087989626203881362957)
          ·
            refine ⟨19570907996109826455511109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52189087989626203881362957 19570907996109826455511109)
            ·
              refine ⟨3669545249270592460408333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19570907996109826455511109 3669545249270592460408333)
              ·
                refine ⟨1376079468476472172653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3669545249270592460408333 1376079468476472172653125)
                ·
                  refine ⟨258014900339338532372461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376079468476472172653125 258014900339338532372461)
                  ·
                    rfl

theorem cell22_2261170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_2261170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261170 prefixEnd_2261170 := by exact prefixLift 2261170
  have htrace : WordTrace (prefixWord ++ tailWord_2261170) baseStart_2261170 baseEnd_2261170 := by
    simpa [prefixWord, tailWord_2261170, baseEnd_2261170] using wordTrace_append hprefix tailTrace_2261170
  have hstable : (prefixWord ++ tailWord_2261170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261170).length < 2 ^ (prefixWord ++ tailWord_2261170).sum := by decide
  have hdescent : baseEnd_2261170 < baseStart_2261170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_2261211 : Nat := 118140960795 + 2261211 * 2 ^ 59
def prefixEnd_2261211 : Nat := 4983230072969 + 3 ^ 40 * 2261211 * 2
def baseEnd_2261211 : Nat := 774058736155905156842257

theorem tailTrace_2261211 : CollatzResearch.WordTrace tailWord_2261211 prefixEnd_2261211 774058736155905156842257 := by
  unfold tailWord_2261211
  simp only [CollatzResearch.WordTrace]
  refine ⟨82473140611026205938223487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54982093740684137292148991 82473140611026205938223487)
  ·
    refine ⟨123709710916539308907335231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82473140611026205938223487 123709710916539308907335231)
    ·
      refine ⟨185564566374808963361002847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123709710916539308907335231 185564566374808963361002847)
      ·
        refine ⟨278346849562213445041504271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185564566374808963361002847 278346849562213445041504271)
        ·
          refine ⟨417520274343320167562256407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278346849562213445041504271 417520274343320167562256407)
          ·
            refine ⟨626280411514980251343384611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417520274343320167562256407 626280411514980251343384611)
            ·
              refine ⟨939420617272470377015076917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626280411514980251343384611 939420617272470377015076917)
              ·
                refine ⟨88070682869294097845163461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 939420617272470377015076917 88070682869294097845163461)
                ·
                  refine ⟨16513253037992643345968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88070682869294097845163461 16513253037992643345968149)
                  ·
                    refine ⟨774058736155905156842257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16513253037992643345968149 774058736155905156842257)
                    ·
                      rfl

theorem cell22_2261211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_2261211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261211 prefixEnd_2261211 := by exact prefixLift 2261211
  have htrace : WordTrace (prefixWord ++ tailWord_2261211) baseStart_2261211 baseEnd_2261211 := by
    simpa [prefixWord, tailWord_2261211, baseEnd_2261211] using wordTrace_append hprefix tailTrace_2261211
  have hstable : (prefixWord ++ tailWord_2261211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261211).length < 2 ^ (prefixWord ++ tailWord_2261211).sum := by decide
  have hdescent : baseEnd_2261211 < baseStart_2261211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261258 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_2261258 : Nat := 118140960795 + 2261258 * 2 ^ 59
def prefixEnd_2261258 : Nat := 4983230072969 + 3 ^ 40 * 2261258 * 2
def baseEnd_2261258 : Nat := 774074825216412700917113

theorem tailTrace_2261258 : CollatzResearch.WordTrace tailWord_2261258 prefixEnd_2261258 774074825216412700917113 := by
  unfold tailWord_2261258
  simp only [CollatzResearch.WordTrace]
  refine ⟨20618713710463983241296107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54983236561237288643456285 20618713710463983241296107)
  ·
    refine ⟨30928070565695974861944161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20618713710463983241296107 30928070565695974861944161)
    ·
      refine ⟨23196052924271981146458121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30928070565695974861944161 23196052924271981146458121)
      ·
        refine ⟨17397039693203985859843591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23196052924271981146458121 17397039693203985859843591)
        ·
          refine ⟨26095559539805978789765387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17397039693203985859843591 26095559539805978789765387)
          ·
            refine ⟨39143339309708968184648081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26095559539805978789765387 39143339309708968184648081)
            ·
              refine ⟨29357504482281726138486061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39143339309708968184648081 29357504482281726138486061)
              ·
                refine ⟨11009064180855647301932273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29357504482281726138486061 11009064180855647301932273)
                ·
                  refine ⟨8256798135641735476449205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11009064180855647301932273 8256798135641735476449205)
                  ·
                    refine ⟨774074825216412700917113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8256798135641735476449205 774074825216412700917113)
                    ·
                      rfl

theorem cell22_2261258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_2261258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261258 prefixEnd_2261258 := by exact prefixLift 2261258
  have htrace : WordTrace (prefixWord ++ tailWord_2261258) baseStart_2261258 baseEnd_2261258 := by
    simpa [prefixWord, tailWord_2261258, baseEnd_2261258] using wordTrace_append hprefix tailTrace_2261258
  have hstable : (prefixWord ++ tailWord_2261258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261258).length < 2 ^ (prefixWord ++ tailWord_2261258).sum := by decide
  have hdescent : baseEnd_2261258 < baseStart_2261258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261294 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_2261294 : Nat := 118140960795 + 2261294 * 2 ^ 59
def prefixEnd_2261294 : Nat := 4983230072969 + 3 ^ 40 * 2261294 * 2
def baseEnd_2261294 : Nat := 258029049584040202339001

theorem tailTrace_2261294 : CollatzResearch.WordTrace tailWord_2261294 prefixEnd_2261294 258029049584040202339001 := by
  unfold tailWord_2261294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309520983715688889186867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54984111913150340742329957 10309520983715688889186867)
  ·
    refine ⟨15464281475573533333780301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309520983715688889186867 15464281475573533333780301)
    ·
      refine ⟨5799105553340075000167613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15464281475573533333780301 5799105553340075000167613)
      ·
        refine ⟨2174664582502528125062855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5799105553340075000167613 2174664582502528125062855)
        ·
          refine ⟨3261996873753792187594283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174664582502528125062855 3261996873753792187594283)
          ·
            refine ⟨4892995310630688281391425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261996873753792187594283 4892995310630688281391425)
            ·
              refine ⟨3669746482973016211043569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892995310630688281391425 3669746482973016211043569)
              ·
                refine ⟨2752309862229762158282677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3669746482973016211043569 2752309862229762158282677)
                ·
                  refine ⟨258029049584040202339001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2752309862229762158282677 258029049584040202339001)
                  ·
                    rfl

theorem cell22_2261294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_2261294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261294 prefixEnd_2261294 := by exact prefixLift 2261294
  have htrace : WordTrace (prefixWord ++ tailWord_2261294) baseStart_2261294 baseEnd_2261294 := by
    simpa [prefixWord, tailWord_2261294, baseEnd_2261294] using wordTrace_append hprefix tailTrace_2261294
  have hstable : (prefixWord ++ tailWord_2261294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261294).length < 2 ^ (prefixWord ++ tailWord_2261294).sum := by decide
  have hdescent : baseEnd_2261294 < baseStart_2261294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261298 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_2261298 : Nat := 118140960795 + 2261298 * 2 ^ 59
def prefixEnd_2261298 : Nat := 4983230072969 + 3 ^ 40 * 2261298 * 2
def baseEnd_2261298 : Nat := 774088518033865929916991

theorem tailTrace_2261298 : CollatzResearch.WordTrace tailWord_2261298 prefixEnd_2261298 774088518033865929916991 := by
  unfold tailWord_2261298
  simp only [CollatzResearch.WordTrace]
  refine ⟨20619078440427754949160137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54984209174474013197760365 20619078440427754949160137)
  ·
    refine ⟨15464308830320816211870103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20619078440427754949160137 15464308830320816211870103)
    ·
      refine ⟨23196463245481224317805155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15464308830320816211870103 23196463245481224317805155)
      ·
        refine ⟨34794694868221836476707733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23196463245481224317805155 34794694868221836476707733)
        ·
          refine ⟨1631001321947898584845675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34794694868221836476707733 1631001321947898584845675)
          ·
            refine ⟨2446501982921847877268513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631001321947898584845675 2446501982921847877268513)
            ·
              refine ⟨1834876487191385907951385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2446501982921847877268513 1834876487191385907951385)
              ·
                refine ⟨1376157365393539430963539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834876487191385907951385 1376157365393539430963539)
                ·
                  refine ⟨2064236048090309146445309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376157365393539430963539 2064236048090309146445309)
                  ·
                    refine ⟨774088518033865929916991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064236048090309146445309 774088518033865929916991)
                    ·
                      rfl

theorem cell22_2261298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_2261298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261298 prefixEnd_2261298 := by exact prefixLift 2261298
  have htrace : WordTrace (prefixWord ++ tailWord_2261298) baseStart_2261298 baseEnd_2261298 := by
    simpa [prefixWord, tailWord_2261298, baseEnd_2261298] using wordTrace_append hprefix tailTrace_2261298
  have hstable : (prefixWord ++ tailWord_2261298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261298).length < 2 ^ (prefixWord ++ tailWord_2261298).sum := by decide
  have hdescent : baseEnd_2261298 < baseStart_2261298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261354 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_2261354 : Nat := 118140960795 + 2261354 * 2 ^ 59
def prefixEnd_2261354 : Nat := 4983230072969 + 3 ^ 40 * 2261354 * 2
def baseEnd_2261354 : Nat := 774107687978300450516819

theorem tailTrace_2261354 : CollatzResearch.WordTrace tailWord_2261354 prefixEnd_2261354 774107687978300450516819 := by
  unfold tailWord_2261354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20619589062377035340169779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54985570833005427573786077 20619589062377035340169779)
  ·
    refine ⟨30929383593565553010254669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20619589062377035340169779 30929383593565553010254669)
    ·
      refine ⟨11598518847587082378845501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30929383593565553010254669 11598518847587082378845501)
      ·
        refine ⟨4349444567845155892067063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11598518847587082378845501 4349444567845155892067063)
        ·
          refine ⟨6524166851767733838100595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349444567845155892067063 6524166851767733838100595)
          ·
            refine ⟨9786250277651600757150893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6524166851767733838100595 9786250277651600757150893)
            ·
              refine ⟨3669843854119350283931585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9786250277651600757150893 3669843854119350283931585)
              ·
                refine ⟨2752382890589512712948689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3669843854119350283931585 2752382890589512712948689)
                ·
                  refine ⟨2064287167942134534711517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2752382890589512712948689 2064287167942134534711517)
                  ·
                    refine ⟨774107687978300450516819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064287167942134534711517 774107687978300450516819)
                    ·
                      rfl

theorem cell22_2261354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_2261354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261354 prefixEnd_2261354 := by exact prefixLift 2261354
  have htrace : WordTrace (prefixWord ++ tailWord_2261354) baseStart_2261354 baseEnd_2261354 := by
    simpa [prefixWord, tailWord_2261354, baseEnd_2261354] using wordTrace_append hprefix tailTrace_2261354
  have hstable : (prefixWord ++ tailWord_2261354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261354).length < 2 ^ (prefixWord ++ tailWord_2261354).sum := by decide
  have hdescent : baseEnd_2261354 < baseStart_2261354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261399 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 1, 3]
def baseStart_2261399 : Nat := 118140960795 + 2261399 * 2 ^ 59
def prefixEnd_2261399 : Nat := 4983230072969 + 3 ^ 40 * 2261399 * 2
def baseEnd_2261399 : Nat := 774123092397935333141681

theorem tailTrace_2261399 : CollatzResearch.WordTrace tailWord_2261399 prefixEnd_2261399 774123092397935333141681 := by
  unfold tailWord_2261399
  simp only [CollatzResearch.WordTrace]
  refine ⟨82479997534345114046067251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54986665022896742697378167 82479997534345114046067251)
  ·
    refine ⟨123719996301517671069100877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82479997534345114046067251 123719996301517671069100877)
    ·
      refine ⟨46394998613069126650912829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123719996301517671069100877 46394998613069126650912829)
      ·
        refine ⟨17398124479900922494092311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46394998613069126650912829 17398124479900922494092311)
        ·
          refine ⟨26097186719851383741138467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17398124479900922494092311 26097186719851383741138467)
          ·
            refine ⟨39145780079777075611707701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26097186719851383741138467 39145780079777075611707701)
            ·
              refine ⟨3669916882479100838597597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39145780079777075611707701 3669916882479100838597597)
              ·
                refine ⟨1376218830929662814474099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3669916882479100838597597 1376218830929662814474099)
                ·
                  refine ⟨2064328246394494221711149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376218830929662814474099 2064328246394494221711149)
                  ·
                    refine ⟨774123092397935333141681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064328246394494221711149 774123092397935333141681)
                    ·
                      rfl

theorem cell22_2261399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_2261399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261399 prefixEnd_2261399 := by exact prefixLift 2261399
  have htrace : WordTrace (prefixWord ++ tailWord_2261399) baseStart_2261399 baseEnd_2261399 := by
    simpa [prefixWord, tailWord_2261399, baseEnd_2261399] using wordTrace_append hprefix tailTrace_2261399
  have hstable : (prefixWord ++ tailWord_2261399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261399).length < 2 ^ (prefixWord ++ tailWord_2261399).sum := by decide
  have hdescent : baseEnd_2261399 < baseStart_2261399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261416 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2261416 : Nat := 118140960795 + 2261416 * 2 ^ 59
def prefixEnd_2261416 : Nat := 4983230072969 + 3 ^ 40 * 2261416 * 2
def baseEnd_2261416 : Nat := 774128911845352955466629

theorem tailTrace_2261416 : CollatzResearch.WordTrace tailWord_2261416 prefixEnd_2261416 774128911845352955466629 := by
  unfold tailWord_2261416
  simp only [CollatzResearch.WordTrace]
  refine ⟨41240308787641762974718051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54987078383522350632957401 41240308787641762974718051)
  ·
    refine ⟨61860463181462644462077077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41240308787641762974718051 61860463181462644462077077)
    ·
      refine ⟨2899709211631061459159863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61860463181462644462077077 2899709211631061459159863)
      ·
        refine ⟨4349563817446592188739795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899709211631061459159863 4349563817446592188739795)
        ·
          refine ⟨6524345726169888283109693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349563817446592188739795 6524345726169888283109693)
          ·
            refine ⟨2446629647313708106166135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6524345726169888283109693 2446629647313708106166135)
            ·
              refine ⟨3669944470970562159249203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446629647313708106166135 3669944470970562159249203)
              ·
                refine ⟨5504916706455843238873805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669944470970562159249203 5504916706455843238873805)
                ·
                  refine ⟨2064343764920941214577677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5504916706455843238873805 2064343764920941214577677)
                  ·
                    refine ⟨774128911845352955466629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064343764920941214577677 774128911845352955466629)
                    ·
                      rfl

theorem cell22_2261416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2261416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261416 prefixEnd_2261416 := by exact prefixLift 2261416
  have htrace : WordTrace (prefixWord ++ tailWord_2261416) baseStart_2261416 baseEnd_2261416 := by
    simpa [prefixWord, tailWord_2261416, baseEnd_2261416] using wordTrace_append hprefix tailTrace_2261416
  have hstable : (prefixWord ++ tailWord_2261416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261416).length < 2 ^ (prefixWord ++ tailWord_2261416).sum := by decide
  have hdescent : baseEnd_2261416 < baseStart_2261416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261510 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2261510 : Nat := 118140960795 + 2261510 * 2 ^ 59
def prefixEnd_2261510 : Nat := 4983230072969 + 3 ^ 40 * 2261510 * 2
def baseEnd_2261510 : Nat := 774161089966368043616341

theorem tailTrace_2261510 : CollatzResearch.WordTrace tailWord_2261510 prefixEnd_2261510 774161089966368043616341 := by
  unfold tailWord_2261510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577626438654468125104937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 54989364024628653335571989 2577626438654468125104937)
  ·
    refine ⟨1933219828990851093828703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577626438654468125104937 1933219828990851093828703)
    ·
      refine ⟨2899829743486276640743055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933219828990851093828703 2899829743486276640743055)
      ·
        refine ⟨4349744615229414961114583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899829743486276640743055 4349744615229414961114583)
        ·
          refine ⟨6524616922844122441671875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349744615229414961114583 6524616922844122441671875)
          ·
            refine ⟨9786925384266183662507813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6524616922844122441671875 9786925384266183662507813)
            ·
              refine ⟨1835048509549909436720215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9786925384266183662507813 1835048509549909436720215)
              ·
                refine ⟨2752572764324864155080323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835048509549909436720215 2752572764324864155080323)
                ·
                  refine ⟨4128859146487296232620485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752572764324864155080323 4128859146487296232620485)
                  ·
                    refine ⟨774161089966368043616341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4128859146487296232620485 774161089966368043616341)
                    ·
                      rfl

theorem cell22_2261510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2261510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261510 prefixEnd_2261510 := by exact prefixLift 2261510
  have htrace : WordTrace (prefixWord ++ tailWord_2261510) baseStart_2261510 baseEnd_2261510 := by
    simpa [prefixWord, tailWord_2261510, baseEnd_2261510] using wordTrace_append hprefix tailTrace_2261510
  have hstable : (prefixWord ++ tailWord_2261510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261510).length < 2 ^ (prefixWord ++ tailWord_2261510).sum := by decide
  have hdescent : baseEnd_2261510 < baseStart_2261510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261592 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_2261592 : Nat := 118140960795 + 2261592 * 2 ^ 59
def prefixEnd_2261592 : Nat := 4983230072969 + 3 ^ 40 * 2261592 * 2
def baseEnd_2261592 : Nat := 258063053414049054355363

theorem tailTrace_2261592 : CollatzResearch.WordTrace tailWord_2261592 prefixEnd_2261592 258063053414049054355363 := by
  unfold tailWord_2261592
  simp only [CollatzResearch.WordTrace]
  refine ⟨41243518411322954003921515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54991357881763938671895353 41243518411322954003921515)
  ·
    refine ⟨61865277616984431005882273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41243518411322954003921515 61865277616984431005882273)
    ·
      refine ⟨46398958212738323254411705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61865277616984431005882273 46398958212738323254411705)
      ·
        refine ⟨34799218659553742440808779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46398958212738323254411705 34799218659553742440808779)
        ·
          refine ⟨52198827989330613661213169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34799218659553742440808779 52198827989330613661213169)
          ·
            refine ⟨39149120991997960245909877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52198827989330613661213169 39149120991997960245909877)
            ·
              refine ⟨3670230092999808773054051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39149120991997960245909877 3670230092999808773054051)
              ·
                refine ⟨5505345139499713159581077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670230092999808773054051 5505345139499713159581077)
                ·
                  refine ⟨258063053414049054355363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5505345139499713159581077 258063053414049054355363)
                  ·
                    rfl

theorem cell22_2261592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_2261592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261592 prefixEnd_2261592 := by exact prefixLift 2261592
  have htrace : WordTrace (prefixWord ++ tailWord_2261592) baseStart_2261592 baseEnd_2261592 := by
    simpa [prefixWord, tailWord_2261592, baseEnd_2261592] using wordTrace_append hprefix tailTrace_2261592
  have hstable : (prefixWord ++ tailWord_2261592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261592).length < 2 ^ (prefixWord ++ tailWord_2261592).sum := by decide
  have hdescent : baseEnd_2261592 < baseStart_2261592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261607 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2261607 : Nat := 118140960795 + 2261607 * 2 ^ 59
def prefixEnd_2261607 : Nat := 4983230072969 + 3 ^ 40 * 2261607 * 2
def baseEnd_2261607 : Nat := 774194295048692123941043

theorem tailTrace_2261607 : CollatzResearch.WordTrace tailWord_2261607 prefixEnd_2261607 774194295048692123941043 := by
  unfold tailWord_2261607
  simp only [CollatzResearch.WordTrace]
  refine ⟨82487583917591565569639075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54991722611727710379759383 82487583917591565569639075)
  ·
    refine ⟨123731375876387348354458613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82487583917591565569639075 123731375876387348354458613)
    ·
      refine ⟨11599816488411313908230495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123731375876387348354458613 11599816488411313908230495)
      ·
        refine ⟨17399724732616970862345743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11599816488411313908230495 17399724732616970862345743)
        ·
          refine ⟨26099587098925456293518615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17399724732616970862345743 26099587098925456293518615)
          ·
            refine ⟨39149380648388184440277923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26099587098925456293518615 39149380648388184440277923)
            ·
              refine ⟨58724070972582276660416885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39149380648388184440277923 58724070972582276660416885)
              ·
                refine ⟨5505381653679588436914083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58724070972582276660416885 5505381653679588436914083)
                ·
                  refine ⟨8258072480519382655371125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5505381653679588436914083 8258072480519382655371125)
                  ·
                    refine ⟨774194295048692123941043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8258072480519382655371125 774194295048692123941043)
                    ·
                      rfl

theorem cell22_2261607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2261607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261607 prefixEnd_2261607 := by exact prefixLift 2261607
  have htrace : WordTrace (prefixWord ++ tailWord_2261607) baseStart_2261607 baseEnd_2261607 := by
    simpa [prefixWord, tailWord_2261607, baseEnd_2261607] using wordTrace_append hprefix tailTrace_2261607
  have hstable : (prefixWord ++ tailWord_2261607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261607).length < 2 ^ (prefixWord ++ tailWord_2261607).sum := by decide
  have hdescent : baseEnd_2261607 < baseStart_2261607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261682 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2261682 : Nat := 118140960795 + 2261682 * 2 ^ 59
def prefixEnd_2261682 : Nat := 4983230072969 + 3 ^ 40 * 2261682 * 2
def baseEnd_2261682 : Nat := 258073323027138976105271

theorem tailTrace_2261682 : CollatzResearch.WordTrace tailWord_2261682 prefixEnd_2261682 258073323027138976105271 := by
  unfold tailWord_2261682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20622579848079963344654825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54993546261546568919079533 20622579848079963344654825)
  ·
    refine ⟨15466934886059972508491119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20622579848079963344654825 15466934886059972508491119)
    ·
      refine ⟨23200402329089958762736679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15466934886059972508491119 23200402329089958762736679)
      ·
        refine ⟨34800603493634938144105019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23200402329089958762736679 34800603493634938144105019)
        ·
          refine ⟨52200905240452407216157529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34800603493634938144105019 52200905240452407216157529)
          ·
            refine ⟨39150678930339305412118147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52200905240452407216157529 39150678930339305412118147)
            ·
              refine ⟨58726018395508958118177221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39150678930339305412118147 58726018395508958118177221)
              ·
                refine ⟨11011128449157929647158229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58726018395508958118177221 11011128449157929647158229)
                ·
                  refine ⟨258073323027138976105271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11011128449157929647158229 258073323027138976105271)
                  ·
                    rfl

theorem cell22_2261682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2261682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261682 prefixEnd_2261682 := by exact prefixLift 2261682
  have htrace : WordTrace (prefixWord ++ tailWord_2261682) baseStart_2261682 baseEnd_2261682 := by
    simpa [prefixWord, tailWord_2261682, baseEnd_2261682] using wordTrace_append hprefix tailTrace_2261682
  have hstable : (prefixWord ++ tailWord_2261682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261682).length < 2 ^ (prefixWord ++ tailWord_2261682).sum := by decide
  have hdescent : baseEnd_2261682 < baseStart_2261682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261746 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2261746 : Nat := 118140960795 + 2261746 * 2 ^ 59
def prefixEnd_2261746 : Nat := 4983230072969 + 3 ^ 40 * 2261746 * 2
def baseEnd_2261746 : Nat := 774241877589342094715617

theorem tailTrace_2261746 : CollatzResearch.WordTrace tailWord_2261746 prefixEnd_2261746 774241877589342094715617 := by
  unfold tailWord_2261746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623163416021998077237273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54995102442725328205966061 20623163416021998077237273)
  ·
    refine ⟨15467372562016498557927955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623163416021998077237273 15467372562016498557927955)
    ·
      refine ⟨23201058843024747836891933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467372562016498557927955 23201058843024747836891933)
      ·
        refine ⟨8700397066134280438834475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23201058843024747836891933 8700397066134280438834475)
        ·
          refine ⟨13050595599201420658251713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700397066134280438834475 13050595599201420658251713)
          ·
            refine ⟨9787946699401065493688785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13050595599201420658251713 9787946699401065493688785)
            ·
              refine ⟨7340960024550799120266589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9787946699401065493688785 7340960024550799120266589)
              ·
                refine ⟨2752860009206549670099971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7340960024550799120266589 2752860009206549670099971)
                ·
                  refine ⟨4129290013809824505149957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2752860009206549670099971 4129290013809824505149957)
                  ·
                    refine ⟨774241877589342094715617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4129290013809824505149957 774241877589342094715617)
                    ·
                      rfl

theorem cell22_2261746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2261746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261746 prefixEnd_2261746 := by exact prefixLift 2261746
  have htrace : WordTrace (prefixWord ++ tailWord_2261746) baseStart_2261746 baseEnd_2261746 := by
    simpa [prefixWord, tailWord_2261746, baseEnd_2261746] using wordTrace_append hprefix tailTrace_2261746
  have hstable : (prefixWord ++ tailWord_2261746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261746).length < 2 ^ (prefixWord ++ tailWord_2261746).sum := by decide
  have hdescent : baseEnd_2261746 < baseStart_2261746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261774 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2261774 : Nat := 118140960795 + 2261774 * 2 ^ 59
def prefixEnd_2261774 : Nat := 4983230072969 + 3 ^ 40 * 2261774 * 2
def baseEnd_2261774 : Nat := 774251462561559355015531

theorem tailTrace_2261774 : CollatzResearch.WordTrace tailWord_2261774 prefixEnd_2261774 774251462561559355015531 := by
  unfold tailWord_2261774
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311709363498319136371047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 54995783271991035393978917 10311709363498319136371047)
  ·
    refine ⟨15467564045247478704556571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311709363498319136371047 15467564045247478704556571)
    ·
      refine ⟨23201346067871218056834857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467564045247478704556571 23201346067871218056834857)
      ·
        refine ⟨17401009550903413542626143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23201346067871218056834857 17401009550903413542626143)
        ·
          refine ⟨26101514326355120313939215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17401009550903413542626143 26101514326355120313939215)
          ·
            refine ⟨39152271489532680470908823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26101514326355120313939215 39152271489532680470908823)
            ·
              refine ⟨58728407234299020706363235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39152271489532680470908823 58728407234299020706363235)
              ·
                refine ⟨88092610851448531059544853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58728407234299020706363235 88092610851448531059544853)
                ·
                  refine ⟨4129341133661649893416165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88092610851448531059544853 4129341133661649893416165)
                  ·
                    refine ⟨774251462561559355015531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4129341133661649893416165 774251462561559355015531)
                    ·
                      rfl

theorem cell22_2261774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2261774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261774 prefixEnd_2261774 := by exact prefixLift 2261774
  have htrace : WordTrace (prefixWord ++ tailWord_2261774) baseStart_2261774 baseEnd_2261774 := by
    simpa [prefixWord, tailWord_2261774, baseEnd_2261774] using wordTrace_append hprefix tailTrace_2261774
  have hstable : (prefixWord ++ tailWord_2261774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261774).length < 2 ^ (prefixWord ++ tailWord_2261774).sum := by decide
  have hdescent : baseEnd_2261774 < baseStart_2261774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261791 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_2261791 : Nat := 118140960795 + 2261791 * 2 ^ 59
def prefixEnd_2261791 : Nat := 4983230072969 + 3 ^ 40 * 2261791 * 2
def baseEnd_2261791 : Nat := 774257282008976977340479

theorem tailTrace_2261791 : CollatzResearch.WordTrace tailWord_2261791 prefixEnd_2261791 774257282008976977340479 := by
  unfold tailWord_2261791
  simp only [CollatzResearch.WordTrace]
  refine ⟨82494294948924964994337227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54996196632616643329558151 82494294948924964994337227)
  ·
    refine ⟨123741442423387447491505841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82494294948924964994337227 123741442423387447491505841)
    ·
      refine ⟨92806081817540585618629381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123741442423387447491505841 92806081817540585618629381)
      ·
        refine ⟨17401140340788859803493009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92806081817540585618629381 17401140340788859803493009)
        ·
          refine ⟨13050855255591644852619757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17401140340788859803493009 13050855255591644852619757)
          ·
            refine ⟨4894070720846866819732409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13050855255591644852619757 4894070720846866819732409)
            ·
              refine ⟨3670553040635150114799307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4894070720846866819732409 3670553040635150114799307)
              ·
                refine ⟨5505829560952725172198961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670553040635150114799307 5505829560952725172198961)
                ·
                  refine ⟨4129372170714543879149221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5505829560952725172198961 4129372170714543879149221)
                  ·
                    refine ⟨774257282008976977340479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4129372170714543879149221 774257282008976977340479)
                    ·
                      rfl

theorem cell22_2261791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_2261791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261791 prefixEnd_2261791 := by exact prefixLift 2261791
  have htrace : WordTrace (prefixWord ++ tailWord_2261791) baseStart_2261791 baseEnd_2261791 := by
    simpa [prefixWord, tailWord_2261791, baseEnd_2261791] using wordTrace_append hprefix tailTrace_2261791
  have hstable : (prefixWord ++ tailWord_2261791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261791).length < 2 ^ (prefixWord ++ tailWord_2261791).sum := by decide
  have hdescent : baseEnd_2261791 < baseStart_2261791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261812 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2261812 : Nat := 118140960795 + 2261812 * 2 ^ 59
def prefixEnd_2261812 : Nat := 4983230072969 + 3 ^ 40 * 2261812 * 2
def baseEnd_2261812 : Nat := 258088156912713307521805

theorem tailTrace_2261812 : CollatzResearch.WordTrace tailWord_2261812 prefixEnd_2261812 258088156912713307521805 := by
  unfold tailWord_2261812
  simp only [CollatzResearch.WordTrace]
  refine ⟨41247530440924442790425845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54996707254565923720567793 41247530440924442790425845)
  ·
    refine ⟨3866955978836666511602423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41247530440924442790425845 3866955978836666511602423)
    ·
      refine ⟨5800433968254999767403635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866955978836666511602423 5800433968254999767403635)
      ·
        refine ⟨8700650952382499651105453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800433968254999767403635 8700650952382499651105453)
        ·
          refine ⟨3262744107143437369164545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8700650952382499651105453 3262744107143437369164545)
          ·
            refine ⟨2447058080357578026873409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3262744107143437369164545 2447058080357578026873409)
            ·
              refine ⟨1835293560268183520155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447058080357578026873409 1835293560268183520155057)
              ·
                refine ⟨1376470170201137640116293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835293560268183520155057 1376470170201137640116293)
                ·
                  refine ⟨258088156912713307521805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376470170201137640116293 258088156912713307521805)
                  ·
                    rfl

theorem cell22_2261812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2261812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261812 prefixEnd_2261812 := by exact prefixLift 2261812
  have htrace : WordTrace (prefixWord ++ tailWord_2261812) baseStart_2261812 baseEnd_2261812 := by
    simpa [prefixWord, tailWord_2261812, baseEnd_2261812] using wordTrace_append hprefix tailTrace_2261812
  have hstable : (prefixWord ++ tailWord_2261812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261812).length < 2 ^ (prefixWord ++ tailWord_2261812).sum := by decide
  have hdescent : baseEnd_2261812 < baseStart_2261812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261896 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_2261896 : Nat := 118140960795 + 2261896 * 2 ^ 59
def prefixEnd_2261896 : Nat := 4983230072969 + 3 ^ 40 * 2261896 * 2
def baseEnd_2261896 : Nat := 258097741884930567821719

theorem tailTrace_2261896 : CollatzResearch.WordTrace tailWord_2261896 prefixEnd_2261896 258097741884930567821719 := by
  unfold tailWord_2261896
  simp only [CollatzResearch.WordTrace]
  refine ⟨41249062306772283963454771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 54998749742363045284606361 41249062306772283963454771)
  ·
    refine ⟨61873593460158425945182157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41249062306772283963454771 61873593460158425945182157)
    ·
      refine ⟨23202597547559409729443309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61873593460158425945182157 23202597547559409729443309)
      ·
        refine ⟨8700974080334778648541241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23202597547559409729443309 8700974080334778648541241)
        ·
          refine ⟨6525730560251083986405931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8700974080334778648541241 6525730560251083986405931)
          ·
            refine ⟨9788595840376625979608897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525730560251083986405931 9788595840376625979608897)
            ·
              refine ⟨7341446880282469484706673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9788595840376625979608897 7341446880282469484706673)
              ·
                refine ⟨5506085160211852113530005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7341446880282469484706673 5506085160211852113530005)
                ·
                  refine ⟨258097741884930567821719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5506085160211852113530005 258097741884930567821719)
                  ·
                    rfl

theorem cell22_2261896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_2261896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261896 prefixEnd_2261896 := by exact prefixLift 2261896
  have htrace : WordTrace (prefixWord ++ tailWord_2261896) baseStart_2261896 baseEnd_2261896 := by
    simpa [prefixWord, tailWord_2261896, baseEnd_2261896] using wordTrace_append hprefix tailTrace_2261896
  have hstable : (prefixWord ++ tailWord_2261896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261896).length < 2 ^ (prefixWord ++ tailWord_2261896).sum := by decide
  have hdescent : baseEnd_2261896 < baseStart_2261896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261898 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_2261898 : Nat := 118140960795 + 2261898 * 2 ^ 59
def prefixEnd_2261898 : Nat := 4983230072969 + 3 ^ 40 * 2261898 * 2
def baseEnd_2261898 : Nat := 774293910295664364915151

theorem tailTrace_2261898 : CollatzResearch.WordTrace tailWord_2261898 prefixEnd_2261898 774293910295664364915151 := by
  unfold tailWord_2261898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20624549389884330567120587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 54998798373024881512321565 20624549389884330567120587)
  ·
    refine ⟨30936824084826495850680881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20624549389884330567120587 30936824084826495850680881)
    ·
      refine ⟨23202618063619871888010661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30936824084826495850680881 23202618063619871888010661)
      ·
        refine ⟨4350490886928725979001999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23202618063619871888010661 4350490886928725979001999)
        ·
          refine ⟨6525736330393088968502999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350490886928725979001999 6525736330393088968502999)
          ·
            refine ⟨9788604495589633452754499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525736330393088968502999 9788604495589633452754499)
            ·
              refine ⟨14682906743384450179131749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9788604495589633452754499 14682906743384450179131749)
              ·
                refine ⟨2753045014384584408587203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14682906743384450179131749 2753045014384584408587203)
                ·
                  refine ⟨4129567521576876612880805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753045014384584408587203 4129567521576876612880805)
                  ·
                    refine ⟨774293910295664364915151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4129567521576876612880805 774293910295664364915151)
                    ·
                      rfl

theorem cell22_2261898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_2261898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261898 prefixEnd_2261898 := by exact prefixLift 2261898
  have htrace : WordTrace (prefixWord ++ tailWord_2261898) baseStart_2261898 baseEnd_2261898 := by
    simpa [prefixWord, tailWord_2261898, baseEnd_2261898] using wordTrace_append hprefix tailTrace_2261898
  have hstable : (prefixWord ++ tailWord_2261898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261898).length < 2 ^ (prefixWord ++ tailWord_2261898).sum := by decide
  have hdescent : baseEnd_2261898 < baseStart_2261898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261911 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 6, 3]
def baseStart_2261911 : Nat := 118140960795 + 2261911 * 2 ^ 59
def prefixEnd_2261911 : Nat := 4983230072969 + 3 ^ 40 * 2261911 * 2
def baseEnd_2261911 : Nat := 774298360461336664340111

theorem tailTrace_2261911 : CollatzResearch.WordTrace tailWord_2261911 prefixEnd_2261911 774298360461336664340111 := by
  unfold tailWord_2261911
  simp only [CollatzResearch.WordTrace]
  refine ⟨82498671708490225488705587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54999114472326816992470391 82498671708490225488705587)
  ·
    refine ⟨123748007562735338233058381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82498671708490225488705587 123748007562735338233058381)
    ·
      refine ⟨46405502836025751837396893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123748007562735338233058381 46405502836025751837396893)
      ·
        refine ⟨17402063563509656939023835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46405502836025751837396893 17402063563509656939023835)
        ·
          refine ⟨26103095345264485408535753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17402063563509656939023835 26103095345264485408535753)
          ·
            refine ⟨19577321508948364056401815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26103095345264485408535753 19577321508948364056401815)
            ·
              refine ⟨29365982263422546084602723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19577321508948364056401815 29365982263422546084602723)
              ·
                refine ⟨44048973395133819126904085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29365982263422546084602723 44048973395133819126904085)
                ·
                  refine ⟨2064795627896897771573629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44048973395133819126904085 2064795627896897771573629)
                  ·
                    refine ⟨774298360461336664340111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064795627896897771573629 774298360461336664340111)
                    ·
                      rfl

theorem cell22_2261911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_2261911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261911 prefixEnd_2261911 := by exact prefixLift 2261911
  have htrace : WordTrace (prefixWord ++ tailWord_2261911) baseStart_2261911 baseEnd_2261911 := by
    simpa [prefixWord, tailWord_2261911, baseEnd_2261911] using wordTrace_append hprefix tailTrace_2261911
  have hstable : (prefixWord ++ tailWord_2261911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261911).length < 2 ^ (prefixWord ++ tailWord_2261911).sum := by decide
  have hdescent : baseEnd_2261911 < baseStart_2261911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_2261939 : Nat := 118140960795 + 2261939 * 2 ^ 59
def prefixEnd_2261939 : Nat := 4983230072969 + 3 ^ 40 * 2261939 * 2
def baseEnd_2261939 : Nat := 774307945433553924640025

theorem tailTrace_2261939 : CollatzResearch.WordTrace tailWord_2261939 prefixEnd_2261939 774307945433553924640025 := by
  unfold tailWord_2261939
  simp only [CollatzResearch.WordTrace]
  refine ⟨82499692952388786270724871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54999795301592524180483247 82499692952388786270724871)
  ·
    refine ⟨123749539428583179406087307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82499692952388786270724871 123749539428583179406087307)
    ·
      refine ⟨185624309142874769109130961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123749539428583179406087307 185624309142874769109130961)
      ·
        refine ⟨139218231857156076831848221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185624309142874769109130961 139218231857156076831848221)
        ·
          refine ⟨52206836946433528811943083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139218231857156076831848221 52206836946433528811943083)
          ·
            refine ⟨78310255419650293217914625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52206836946433528811943083 78310255419650293217914625)
            ·
              refine ⟨58732691564737719913435969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78310255419650293217914625 58732691564737719913435969)
              ·
                refine ⟨44049518673553289935076977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58732691564737719913435969 44049518673553289935076977)
                ·
                  refine ⟨33037139005164967451307733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44049518673553289935076977 33037139005164967451307733)
                  ·
                    refine ⟨774307945433553924640025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33037139005164967451307733 774307945433553924640025)
                    ·
                      rfl

theorem cell22_2261939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_2261939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261939 prefixEnd_2261939 := by exact prefixLift 2261939
  have htrace : WordTrace (prefixWord ++ tailWord_2261939) baseStart_2261939 baseEnd_2261939 := by
    simpa [prefixWord, tailWord_2261939, baseEnd_2261939] using wordTrace_append hprefix tailTrace_2261939
  have hstable : (prefixWord ++ tailWord_2261939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261939).length < 2 ^ (prefixWord ++ tailWord_2261939).sum := by decide
  have hdescent : baseEnd_2261939 < baseStart_2261939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261941 : List Nat := [1, 3, 3, 2, 1, 1, 4, 7]
def baseStart_2261941 : Nat := 118140960795 + 2261941 * 2 ^ 59
def prefixEnd_2261941 : Nat := 4983230072969 + 3 ^ 40 * 2261941 * 2
def baseEnd_2261941 : Nat := 86034292230491842898891

theorem tailTrace_2261941 : CollatzResearch.WordTrace tailWord_2261941 prefixEnd_2261941 86034292230491842898891 := by
  unfold tailWord_2261941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82499765898381540612297677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54999843932254360408198451 82499765898381540612297677)
  ·
    refine ⟨30937412211893077729611629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82499765898381540612297677 30937412211893077729611629)
    ·
      refine ⟨11601529579459904148604361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30937412211893077729611629 11601529579459904148604361)
      ·
        refine ⟨8701147184594928111453271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11601529579459904148604361 8701147184594928111453271)
        ·
          refine ⟨13051720776892392167179907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8701147184594928111453271 13051720776892392167179907)
          ·
            refine ⟨19577581165338588250769861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13051720776892392167179907 19577581165338588250769861)
            ·
              refine ⟨3670796468500985297019349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19577581165338588250769861 3670796468500985297019349)
              ·
                refine ⟨86034292230491842898891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3670796468500985297019349 86034292230491842898891)
                ·
                  rfl

theorem cell22_2261941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 7].length) (baseStart_2261941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261941 prefixEnd_2261941 := by exact prefixLift 2261941
  have htrace : WordTrace (prefixWord ++ tailWord_2261941) baseStart_2261941 baseEnd_2261941 := by
    simpa [prefixWord, tailWord_2261941, baseEnd_2261941] using wordTrace_append hprefix tailTrace_2261941
  have hstable : (prefixWord ++ tailWord_2261941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261941).length < 2 ^ (prefixWord ++ tailWord_2261941).sum := by decide
  have hdescent : baseEnd_2261941 < baseStart_2261941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2261945 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 2, 3]
def baseStart_2261945 : Nat := 118140960795 + 2261945 * 2 ^ 59
def prefixEnd_2261945 : Nat := 4983230072969 + 3 ^ 40 * 2261945 * 2
def baseEnd_2261945 : Nat := 774309999356171908990007

theorem tailTrace_2261945 : CollatzResearch.WordTrace tailWord_2261945 prefixEnd_2261945 774309999356171908990007 := by
  unfold tailWord_2261945
  simp only [CollatzResearch.WordTrace]
  refine ⟨82499911790367049295443289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 54999941193578032863628859 82499911790367049295443289)
  ·
    refine ⟨61874933842775286971582467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82499911790367049295443289 61874933842775286971582467)
    ·
      refine ⟨92812400764162930457373701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61874933842775286971582467 92812400764162930457373701)
      ·
        refine ⟨17402325143280549460757569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92812400764162930457373701 17402325143280549460757569)
        ·
          refine ⟨13051743857460412095568177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17402325143280549460757569 13051743857460412095568177)
          ·
            refine ⟨9788807893095309071676133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051743857460412095568177 9788807893095309071676133)
            ·
              refine ⟨1835401479955370450939275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9788807893095309071676133 1835401479955370450939275)
              ·
                refine ⟨2753102219933055676408913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835401479955370450939275 2753102219933055676408913)
                ·
                  refine ⟨2064826664949791757306685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753102219933055676408913 2064826664949791757306685)
                  ·
                    refine ⟨774309999356171908990007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064826664949791757306685 774309999356171908990007)
                    ·
                      rfl

theorem cell22_2261945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 3].length) (baseStart_2261945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2261945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2261945 prefixEnd_2261945 := by exact prefixLift 2261945
  have htrace : WordTrace (prefixWord ++ tailWord_2261945) baseStart_2261945 baseEnd_2261945 := by
    simpa [prefixWord, tailWord_2261945, baseEnd_2261945] using wordTrace_append hprefix tailTrace_2261945
  have hstable : (prefixWord ++ tailWord_2261945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2261945).length < 2 ^ (prefixWord ++ tailWord_2261945).sum := by decide
  have hdescent : baseEnd_2261945 < baseStart_2261945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2261945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262001 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_2262001 : Nat := 118140960795 + 2262001 * 2 ^ 59
def prefixEnd_2262001 : Nat := 4983230072969 + 3 ^ 40 * 2262001 * 2
def baseEnd_2262001 : Nat := 774329169300606429589835

theorem tailTrace_2262001 : CollatzResearch.WordTrace tailWord_2262001 prefixEnd_2262001 774329169300606429589835 := by
  unfold tailWord_2262001
  simp only [CollatzResearch.WordTrace]
  refine ⟨82501954278164170859481857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55001302852109447239654571 82501954278164170859481857)
  ·
    refine ⟨61876465708623128144611393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82501954278164170859481857 61876465708623128144611393)
    ·
      refine ⟨46407349281467346108458545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61876465708623128144611393 46407349281467346108458545)
      ·
        refine ⟨34805511961100509581343909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46407349281467346108458545 34805511961100509581343909)
        ·
          refine ⟨6526033492706345546501983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34805511961100509581343909 6526033492706345546501983)
          ·
            refine ⟨9789050239059518319752975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526033492706345546501983 9789050239059518319752975)
            ·
              refine ⟨14683575358589277479629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9789050239059518319752975 14683575358589277479629463)
              ·
                refine ⟨22025363037883916219444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14683575358589277479629463 22025363037883916219444195)
                ·
                  refine ⟨33038044556825874329166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22025363037883916219444195 33038044556825874329166293)
                  ·
                    refine ⟨774329169300606429589835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33038044556825874329166293 774329169300606429589835)
                    ·
                      rfl

theorem cell22_2262001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_2262001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262001 prefixEnd_2262001 := by exact prefixLift 2262001
  have htrace : WordTrace (prefixWord ++ tailWord_2262001) baseStart_2262001 baseEnd_2262001 := by
    simpa [prefixWord, tailWord_2262001, baseEnd_2262001] using wordTrace_append hprefix tailTrace_2262001
  have hstable : (prefixWord ++ tailWord_2262001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262001).length < 2 ^ (prefixWord ++ tailWord_2262001).sum := by decide
  have hdescent : baseEnd_2262001 < baseStart_2262001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262093 : List Nat := [1, 6, 1, 1, 1, 2, 10]
def baseStart_2262093 : Nat := 118140960795 + 2262093 * 2 ^ 59
def prefixEnd_2262093 : Nat := 4983230072969 + 3 ^ 40 * 2262093 * 2
def baseEnd_2262093 : Nat := 28680024547435142825539

theorem tailTrace_2262093 : CollatzResearch.WordTrace tailWord_2262093 prefixEnd_2262093 28680024547435142825539 := by
  unfold tailWord_2262093
  simp only [CollatzResearch.WordTrace]
  refine ⟨82505309793830870571830933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55003539862553913714553955 82505309793830870571830933)
  ·
    refine ⟨3867436396585822058054575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82505309793830870571830933 3867436396585822058054575)
    ·
      refine ⟨5801154594878733087081863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867436396585822058054575 5801154594878733087081863)
      ·
        refine ⟨8701731892318099630622795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801154594878733087081863 8701731892318099630622795)
        ·
          refine ⟨13052597838477149445934193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8701731892318099630622795 13052597838477149445934193)
          ·
            refine ⟨9789448378857862084450645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13052597838477149445934193 9789448378857862084450645)
            ·
              refine ⟨28680024547435142825539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9789448378857862084450645 28680024547435142825539)
              ·
                rfl

theorem cell22_2262093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 10].length) (baseStart_2262093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262093 prefixEnd_2262093 := by exact prefixLift 2262093
  have htrace : WordTrace (prefixWord ++ tailWord_2262093) baseStart_2262093 baseEnd_2262093 := by
    simpa [prefixWord, tailWord_2262093, baseEnd_2262093] using wordTrace_append hprefix tailTrace_2262093
  have hstable : (prefixWord ++ tailWord_2262093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262093).length < 2 ^ (prefixWord ++ tailWord_2262093).sum := by decide
  have hdescent : baseEnd_2262093 < baseStart_2262093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262114 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2262114 : Nat := 118140960795 + 2262114 * 2 ^ 59
def prefixEnd_2262114 : Nat := 4983230072969 + 3 ^ 40 * 2262114 * 2
def baseEnd_2262114 : Nat := 774367851509911801514489

theorem tailTrace_2262114 : CollatzResearch.WordTrace tailWord_2262114 prefixEnd_2262114 774367851509911801514489 := by
  unfold tailWord_2262114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20626518931688697789586349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55004050484503194105563597 20626518931688697789586349)
  ·
    refine ⟨7734944599383261671094881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20626518931688697789586349 7734944599383261671094881)
    ·
      refine ⟨5801208449537446253321161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7734944599383261671094881 5801208449537446253321161)
      ·
        refine ⟨4350906337153084689990871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5801208449537446253321161 4350906337153084689990871)
        ·
          refine ⟨6526359505729627034986307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350906337153084689990871 6526359505729627034986307)
          ·
            refine ⟨9789539258594440552479461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6526359505729627034986307 9789539258594440552479461)
            ·
              refine ⟨1835538610986457603589899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9789539258594440552479461 1835538610986457603589899)
              ·
                refine ⟨2753307916479686405384849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835538610986457603589899 2753307916479686405384849)
                ·
                  refine ⟨2064980937359764804038637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753307916479686405384849 2064980937359764804038637)
                  ·
                    refine ⟨774367851509911801514489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2064980937359764804038637 774367851509911801514489)
                    ·
                      rfl

theorem cell22_2262114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2262114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262114 prefixEnd_2262114 := by exact prefixLift 2262114
  have htrace : WordTrace (prefixWord ++ tailWord_2262114) baseStart_2262114 baseEnd_2262114 := by
    simpa [prefixWord, tailWord_2262114, baseEnd_2262114] using wordTrace_append hprefix tailTrace_2262114
  have hstable : (prefixWord ++ tailWord_2262114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262114).length < 2 ^ (prefixWord ++ tailWord_2262114).sum := by decide
  have hdescent : baseEnd_2262114 < baseStart_2262114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262170 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_2262170 : Nat := 118140960795 + 2262170 * 2 ^ 59
def prefixEnd_2262170 : Nat := 4983230072969 + 3 ^ 40 * 2262170 * 2
def baseEnd_2262170 : Nat := 774387021454346322114317

theorem tailTrace_2262170 : CollatzResearch.WordTrace tailWord_2262170 prefixEnd_2262170 774387021454346322114317 := by
  unfold tailWord_2262170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20627029553637978180595991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55005412143034608481589309 20627029553637978180595991)
  ·
    refine ⟨30940544330456967270893987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20627029553637978180595991 30940544330456967270893987)
    ·
      refine ⟨46410816495685450906340981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30940544330456967270893987 46410816495685450906340981)
      ·
        refine ⟨4351014046470511022469467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46410816495685450906340981 4351014046470511022469467)
        ·
          refine ⟨6526521069705766533704201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351014046470511022469467 6526521069705766533704201)
          ·
            refine ⟨4894890802279324900278151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526521069705766533704201 4894890802279324900278151)
            ·
              refine ⟨7342336203418987350417227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894890802279324900278151 7342336203418987350417227)
              ·
                refine ⟨11013504305128481025625841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7342336203418987350417227 11013504305128481025625841)
                ·
                  refine ⟨8260128228846360769219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11013504305128481025625841 8260128228846360769219381)
                  ·
                    refine ⟨774387021454346322114317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8260128228846360769219381 774387021454346322114317)
                    ·
                      rfl

theorem cell22_2262170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_2262170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262170 prefixEnd_2262170 := by exact prefixLift 2262170
  have htrace : WordTrace (prefixWord ++ tailWord_2262170) baseStart_2262170 baseEnd_2262170 := by
    simpa [prefixWord, tailWord_2262170, baseEnd_2262170] using wordTrace_append hprefix tailTrace_2262170
  have hstable : (prefixWord ++ tailWord_2262170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262170).length < 2 ^ (prefixWord ++ tailWord_2262170).sum := by decide
  have hdescent : baseEnd_2262170 < baseStart_2262170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262213 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2262213 : Nat := 118140960795 + 2262213 * 2 ^ 59
def prefixEnd_2262213 : Nat := 4983230072969 + 3 ^ 40 * 2262213 * 2
def baseEnd_2262213 : Nat := 774401741233108543289185

theorem tailTrace_2262213 : CollatzResearch.WordTrace tailWord_2262213 prefixEnd_2262213 774401741233108543289185 := by
  unfold tailWord_2262213
  simp only [CollatzResearch.WordTrace]
  refine ⟨82509686553396131066199293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55006457702264087377466195 82509686553396131066199293)
  ·
    refine ⟨30941132457523549149824735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82509686553396131066199293 30941132457523549149824735)
    ·
      refine ⟨46411698686285323724737103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30941132457523549149824735 46411698686285323724737103)
      ·
        refine ⟨69617548029427985587105655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46411698686285323724737103 69617548029427985587105655)
        ·
          refine ⟨104426322044141978380658483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69617548029427985587105655 104426322044141978380658483)
          ·
            refine ⟨156639483066212967570987725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104426322044141978380658483 156639483066212967570987725)
            ·
              refine ⟨58739806149829862839120397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156639483066212967570987725 58739806149829862839120397)
              ·
                refine ⟨22027427306186198564670149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58739806149829862839120397 22027427306186198564670149)
                ·
                  refine ⟨4130142619909912230875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22027427306186198564670149 4130142619909912230875653)
                  ·
                    refine ⟨774401741233108543289185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130142619909912230875653 774401741233108543289185)
                    ·
                      rfl

theorem cell22_2262213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2262213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262213 prefixEnd_2262213 := by exact prefixLift 2262213
  have htrace : WordTrace (prefixWord ++ tailWord_2262213) baseStart_2262213 baseEnd_2262213 := by
    simpa [prefixWord, tailWord_2262213, baseEnd_2262213] using wordTrace_append hprefix tailTrace_2262213
  have hstable : (prefixWord ++ tailWord_2262213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262213).length < 2 ^ (prefixWord ++ tailWord_2262213).sum := by decide
  have hdescent : baseEnd_2262213 < baseStart_2262213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262232 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_2262232 : Nat := 118140960795 + 2262232 * 2 ^ 59
def prefixEnd_2262232 : Nat := 4983230072969 + 3 ^ 40 * 2262232 * 2
def baseEnd_2262232 : Nat := 774408245321398827064127

theorem tailTrace_2262232 : CollatzResearch.WordTrace tailWord_2262232 prefixEnd_2262232 774408245321398827064127 := by
  unfold tailWord_2262232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41255189770163648655570475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55006919693551531540760633 41255189770163648655570475)
  ·
    refine ⟨61882784655245472983355713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41255189770163648655570475 61882784655245472983355713)
    ·
      refine ⟨46412088491434104737516785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61882784655245472983355713 46412088491434104737516785)
      ·
        refine ⟨34809066368575578553137589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46412088491434104737516785 34809066368575578553137589)
        ·
          refine ⟨3263349972053960489356649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34809066368575578553137589 3263349972053960489356649)
          ·
            refine ⟨2447512479040470367017487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3263349972053960489356649 2447512479040470367017487)
            ·
              refine ⟨3671268718560705550526231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447512479040470367017487 3671268718560705550526231)
              ·
                refine ⟨5506903077841058325789347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671268718560705550526231 5506903077841058325789347)
                ·
                  refine ⟨8260354616761587488684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5506903077841058325789347 8260354616761587488684021)
                  ·
                    refine ⟨774408245321398827064127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8260354616761587488684021 774408245321398827064127)
                    ·
                      rfl

theorem cell22_2262232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_2262232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262232 prefixEnd_2262232 := by exact prefixLift 2262232
  have htrace : WordTrace (prefixWord ++ tailWord_2262232) baseStart_2262232 baseEnd_2262232 := by
    simpa [prefixWord, tailWord_2262232, baseEnd_2262232] using wordTrace_append hprefix tailTrace_2262232
  have hstable : (prefixWord ++ tailWord_2262232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262232).length < 2 ^ (prefixWord ++ tailWord_2262232).sum := by decide
  have hdescent : baseEnd_2262232 < baseStart_2262232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262245 : List Nat := [1, 3, 1, 4, 3, 1, 1, 8]
def baseStart_2262245 : Nat := 118140960795 + 2262245 * 2 ^ 59
def prefixEnd_2262245 : Nat := 4983230072969 + 3 ^ 40 * 2262245 * 2
def baseEnd_2262245 : Nat := 86045855054119014054343

theorem tailTrace_2262245 : CollatzResearch.WordTrace tailWord_2262245 prefixEnd_2262245 86045855054119014054343 := by
  unfold tailWord_2262245
  simp only [CollatzResearch.WordTrace]
  refine ⟨82510853689280200531364189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55007235792853467020909459 82510853689280200531364189)
  ·
    refine ⟨30941570133480075199261571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82510853689280200531364189 30941570133480075199261571)
    ·
      refine ⟨46412355200220112798892357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30941570133480075199261571 46412355200220112798892357)
      ·
        refine ⟨8702316600041271149792317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46412355200220112798892357 8702316600041271149792317)
        ·
          refine ⟨3263368725015476681172119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8702316600041271149792317 3263368725015476681172119)
          ·
            refine ⟨4895053087523215021758179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263368725015476681172119 4895053087523215021758179)
            ·
              refine ⟨7342579631284822532637269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4895053087523215021758179 7342579631284822532637269)
              ·
                refine ⟨86045855054119014054343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7342579631284822532637269 86045855054119014054343)
                ·
                  rfl

theorem cell22_2262245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 8].length) (baseStart_2262245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262245 prefixEnd_2262245 := by exact prefixLift 2262245
  have htrace : WordTrace (prefixWord ++ tailWord_2262245) baseStart_2262245 baseEnd_2262245 := by
    simpa [prefixWord, tailWord_2262245, baseEnd_2262245] using wordTrace_append hprefix tailTrace_2262245
  have hstable : (prefixWord ++ tailWord_2262245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262245).length < 2 ^ (prefixWord ++ tailWord_2262245).sum := by decide
  have hdescent : baseEnd_2262245 < baseStart_2262245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262288 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_2262288 : Nat := 118140960795 + 2262288 * 2 ^ 59
def prefixEnd_2262288 : Nat := 4983230072969 + 3 ^ 40 * 2262288 * 2
def baseEnd_2262288 : Nat := 774427415265833347663955

theorem tailTrace_2262288 : CollatzResearch.WordTrace tailWord_2262288 prefixEnd_2262288 774427415265833347663955 := by
  unfold tailWord_2262288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41256211014062209437589759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55008281352082945916786345 41256211014062209437589759)
  ·
    refine ⟨61884316521093314156384639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41256211014062209437589759 61884316521093314156384639)
    ·
      refine ⟨92826474781639971234576959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61884316521093314156384639 92826474781639971234576959)
      ·
        refine ⟨139239712172459956851865439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92826474781639971234576959 139239712172459956851865439)
        ·
          refine ⟨208859568258689935277798159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139239712172459956851865439 208859568258689935277798159)
          ·
            refine ⟨313289352388034902916697239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208859568258689935277798159 313289352388034902916697239)
            ·
              refine ⟨469934028582052354375045859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313289352388034902916697239 469934028582052354375045859)
              ·
                refine ⟨704901042873078531562568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469934028582052354375045859 704901042873078531562568789)
                ·
                  refine ⟨8260559096168889041748853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 704901042873078531562568789 8260559096168889041748853)
                  ·
                    refine ⟨774427415265833347663955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8260559096168889041748853 774427415265833347663955)
                    ·
                      rfl

theorem cell22_2262288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_2262288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262288 prefixEnd_2262288 := by exact prefixLift 2262288
  have htrace : WordTrace (prefixWord ++ tailWord_2262288) baseStart_2262288 baseEnd_2262288 := by
    simpa [prefixWord, tailWord_2262288, baseEnd_2262288] using wordTrace_append hprefix tailTrace_2262288
  have hstable : (prefixWord ++ tailWord_2262288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262288).length < 2 ^ (prefixWord ++ tailWord_2262288).sum := by decide
  have hdescent : baseEnd_2262288 < baseStart_2262288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262337 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2262337 : Nat := 118140960795 + 2262337 * 2 ^ 59
def prefixEnd_2262337 : Nat := 4983230072969 + 3 ^ 40 * 2262337 * 2
def baseEnd_2262337 : Nat := 774444188967213553188805

theorem tailTrace_2262337 : CollatzResearch.WordTrace tailWord_2262337 prefixEnd_2262337 774444188967213553188805 := by
  unfold tailWord_2262337
  simp only [CollatzResearch.WordTrace]
  refine ⟨82514209204946900243713265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55009472803297933495808843 82514209204946900243713265)
  ·
    refine ⟨61885656903710175182784949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82514209204946900243713265 61885656903710175182784949)
    ·
      refine ⟨5801780334722828923386089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61885656903710175182784949 5801780334722828923386089)
      ·
        refine ⟨4351335251042121692539567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5801780334722828923386089 4351335251042121692539567)
        ·
          refine ⟨6527002876563182538809351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351335251042121692539567 6527002876563182538809351)
          ·
            refine ⟨9790504314844773808214027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6527002876563182538809351 9790504314844773808214027)
            ·
              refine ⟨14685756472267160712321041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9790504314844773808214027 14685756472267160712321041)
              ·
                refine ⟨11014317354200370534240781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14685756472267160712321041 11014317354200370534240781)
                ·
                  refine ⟨4130369007825138950340293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11014317354200370534240781 4130369007825138950340293)
                  ·
                    refine ⟨774444188967213553188805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130369007825138950340293 774444188967213553188805)
                    ·
                      rfl

theorem cell22_2262337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2262337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262337 prefixEnd_2262337 := by exact prefixLift 2262337
  have htrace : WordTrace (prefixWord ++ tailWord_2262337) baseStart_2262337 baseEnd_2262337 := by
    simpa [prefixWord, tailWord_2262337, baseEnd_2262337] using wordTrace_append hprefix tailTrace_2262337
  have hstable : (prefixWord ++ tailWord_2262337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262337).length < 2 ^ (prefixWord ++ tailWord_2262337).sum := by decide
  have hdescent : baseEnd_2262337 < baseStart_2262337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262380 : List Nat := [2, 2, 1, 1, 5, 2, 9]
def baseStart_2262380 : Nat := 118140960795 + 2262380 * 2 ^ 59
def prefixEnd_2262380 : Nat := 4983230072969 + 3 ^ 40 * 2262380 * 2
def baseEnd_2262380 : Nat := 28683663286887991643099

theorem tailTrace_2262380 : CollatzResearch.WordTrace tailWord_2262380 prefixEnd_2262380 28683663286887991643099 := by
  unfold tailWord_2262380
  simp only [CollatzResearch.WordTrace]
  refine ⟨41257888771895559293764297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55010518362527412391685729 41257888771895559293764297)
  ·
    refine ⟨30943416578921669470323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41257888771895559293764297 30943416578921669470323223)
    ·
      refine ⟨46415124868382504205484835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30943416578921669470323223 46415124868382504205484835)
      ·
        refine ⟨69622687302573756308227253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46415124868382504205484835 69622687302573756308227253)
        ·
          refine ⟨6527126934616289653896305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69622687302573756308227253 6527126934616289653896305)
          ·
            refine ⟨4895345200962217240422229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6527126934616289653896305 4895345200962217240422229)
            ·
              refine ⟨28683663286887991643099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4895345200962217240422229 28683663286887991643099)
              ·
                rfl

theorem cell22_2262380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 9].length) (baseStart_2262380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262380 prefixEnd_2262380 := by exact prefixLift 2262380
  have htrace : WordTrace (prefixWord ++ tailWord_2262380) baseStart_2262380 baseEnd_2262380 := by
    simpa [prefixWord, tailWord_2262380, baseEnd_2262380] using wordTrace_append hprefix tailTrace_2262380
  have hstable : (prefixWord ++ tailWord_2262380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262380).length < 2 ^ (prefixWord ++ tailWord_2262380).sum := by decide
  have hdescent : baseEnd_2262380 < baseStart_2262380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262401 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2262401 : Nat := 118140960795 + 2262401 * 2 ^ 59
def prefixEnd_2262401 : Nat := 4983230072969 + 3 ^ 40 * 2262401 * 2
def baseEnd_2262401 : Nat := 774466097475138719588609

theorem tailTrace_2262401 : CollatzResearch.WordTrace tailWord_2262401 prefixEnd_2262401 774466097475138719588609 := by
  unfold tailWord_2262401
  simp only [CollatzResearch.WordTrace]
  refine ⟨82516543476715039174043057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55011028984476692782695371 82516543476715039174043057)
  ·
    refine ⟨61887407607536279380532293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82516543476715039174043057 61887407607536279380532293)
    ·
      refine ⟨11603888926413052383849805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61887407607536279380532293 11603888926413052383849805)
      ·
        refine ⟨4351458347404894643943677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11603888926413052383849805 4351458347404894643943677)
        ·
          refine ⟨1631796880276835491478879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4351458347404894643943677 1631796880276835491478879)
          ·
            refine ⟨2447695320415253237218319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631796880276835491478879 2447695320415253237218319)
            ·
              refine ⟨3671542980622879855827479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447695320415253237218319 3671542980622879855827479)
              ·
                refine ⟨5507314470934319783741219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3671542980622879855827479 5507314470934319783741219)
                ·
                  refine ⟨8260971706401479675611829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5507314470934319783741219 8260971706401479675611829)
                  ·
                    refine ⟨774466097475138719588609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8260971706401479675611829 774466097475138719588609)
                    ·
                      rfl

theorem cell22_2262401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2262401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262401 prefixEnd_2262401 := by exact prefixLift 2262401
  have htrace : WordTrace (prefixWord ++ tailWord_2262401) baseStart_2262401 baseEnd_2262401 := by
    simpa [prefixWord, tailWord_2262401, baseEnd_2262401] using wordTrace_append hprefix tailTrace_2262401
  have hstable : (prefixWord ++ tailWord_2262401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262401).length < 2 ^ (prefixWord ++ tailWord_2262401).sum := by decide
  have hdescent : baseEnd_2262401 < baseStart_2262401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262412 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_2262412 : Nat := 118140960795 + 2262412 * 2 ^ 59
def prefixEnd_2262412 : Nat := 4983230072969 + 3 ^ 40 * 2262412 * 2
def baseEnd_2262412 : Nat := 774469862999938357563575

theorem tailTrace_2262412 : CollatzResearch.WordTrace tailWord_2262412 prefixEnd_2262412 774469862999938357563575 := by
  unfold tailWord_2262412
  simp only [CollatzResearch.WordTrace]
  refine ⟨41258472339837594026346745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55011296453116792035128993 41258472339837594026346745)
  ·
    refine ⟨30943854254878195519760059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41258472339837594026346745 30943854254878195519760059)
    ·
      refine ⟨46415781382317293279640089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30943854254878195519760059 46415781382317293279640089)
      ·
        refine ⟨34811836036737969959730067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46415781382317293279640089 34811836036737969959730067)
        ·
          refine ⟨52217754055106954939595101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34811836036737969959730067 52217754055106954939595101)
          ·
            refine ⟨19581657770665108102348163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52217754055106954939595101 19581657770665108102348163)
            ·
              refine ⟨29372486655997662153522245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19581657770665108102348163 29372486655997662153522245)
              ·
                refine ⟨5507341247999561653785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29372486655997662153522245 5507341247999561653785421)
                ·
                  refine ⟨2065252967999835620169533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5507341247999561653785421 2065252967999835620169533)
                  ·
                    refine ⟨774469862999938357563575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065252967999835620169533 774469862999938357563575)
                    ·
                      rfl

theorem cell22_2262412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_2262412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262412 prefixEnd_2262412 := by exact prefixLift 2262412
  have htrace : WordTrace (prefixWord ++ tailWord_2262412) baseStart_2262412 baseEnd_2262412 := by
    simpa [prefixWord, tailWord_2262412, baseEnd_2262412] using wordTrace_append hprefix tailTrace_2262412
  have hstable : (prefixWord ++ tailWord_2262412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262412).length < 2 ^ (prefixWord ++ tailWord_2262412).sum := by decide
  have hdescent : baseEnd_2262412 < baseStart_2262412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262425 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 7]
def baseStart_2262425 : Nat := 118140960795 + 2262425 * 2 ^ 59
def prefixEnd_2262425 : Nat := 4983230072969 + 3 ^ 40 * 2262425 * 2
def baseEnd_2262425 : Nat := 258158104388536885662845

theorem tailTrace_2262425 : CollatzResearch.WordTrace tailWord_2262425 prefixEnd_2262425 258158104388536885662845 := by
  unfold tailWord_2262425
  simp only [CollatzResearch.WordTrace]
  refine ⟨82517418828628091272916729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55011612552418727515277819 82517418828628091272916729)
  ·
    refine ⟨61888064121471068454687547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82517418828628091272916729 61888064121471068454687547)
    ·
      refine ⟨92832096182206602682031321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61888064121471068454687547 92832096182206602682031321)
      ·
        refine ⟨69624072136654952011523491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92832096182206602682031321 69624072136654952011523491)
        ·
          refine ⟨104436108204982428017285237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69624072136654952011523491 104436108204982428017285237)
          ·
            refine ⟨9790885144217102626620491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104436108204982428017285237 9790885144217102626620491)
            ·
              refine ⟨14686327716325653939930737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9790885144217102626620491 14686327716325653939930737)
              ·
                refine ⟨11014745787244240454948053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14686327716325653939930737 11014745787244240454948053)
                ·
                  refine ⟨258158104388536885662845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11014745787244240454948053 258158104388536885662845)
                  ·
                    rfl

theorem cell22_2262425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_2262425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262425 prefixEnd_2262425 := by exact prefixLift 2262425
  have htrace : WordTrace (prefixWord ++ tailWord_2262425) baseStart_2262425 baseEnd_2262425 := by
    simpa [prefixWord, tailWord_2262425, baseEnd_2262425] using wordTrace_append hprefix tailTrace_2262425
  have hstable : (prefixWord ++ tailWord_2262425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262425).length < 2 ^ (prefixWord ++ tailWord_2262425).sum := by decide
  have hdescent : baseEnd_2262425 < baseStart_2262425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262472 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2262472 : Nat := 118140960795 + 2262472 * 2 ^ 59
def prefixEnd_2262472 : Nat := 4983230072969 + 3 ^ 40 * 2262472 * 2
def baseEnd_2262472 : Nat := 774490402226118201063391

theorem tailTrace_2262472 : CollatzResearch.WordTrace tailWord_2262472 prefixEnd_2262472 774490402226118201063391 := by
  unfold tailWord_2262472
  simp only [CollatzResearch.WordTrace]
  refine ⟨41259566529728909149938835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55012755372971878866585113 41259566529728909149938835)
  ·
    refine ⟨61889349794593363724908253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41259566529728909149938835 61889349794593363724908253)
    ·
      refine ⟨23208506172972511396840595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61889349794593363724908253 23208506172972511396840595)
      ·
        refine ⟨34812759259458767095260893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23208506172972511396840595 34812759259458767095260893)
        ·
          refine ⟨13054784722297037660722835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34812759259458767095260893 13054784722297037660722835)
          ·
            refine ⟨19582177083445556491084253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13054784722297037660722835 19582177083445556491084253)
            ·
              refine ⟨7343316406292083684156595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19582177083445556491084253 7343316406292083684156595)
              ·
                refine ⟨11014974609438125526234893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7343316406292083684156595 11014974609438125526234893)
                ·
                  refine ⟨4130615478539297072338085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11014974609438125526234893 4130615478539297072338085)
                  ·
                    refine ⟨774490402226118201063391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130615478539297072338085 774490402226118201063391)
                    ·
                      rfl

theorem cell22_2262472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2262472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262472 prefixEnd_2262472 := by exact prefixLift 2262472
  have htrace : WordTrace (prefixWord ++ tailWord_2262472) baseStart_2262472 baseEnd_2262472 := by
    simpa [prefixWord, tailWord_2262472, baseEnd_2262472] using wordTrace_append hprefix tailTrace_2262472
  have hstable : (prefixWord ++ tailWord_2262472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262472).length < 2 ^ (prefixWord ++ tailWord_2262472).sum := by decide
  have hdescent : baseEnd_2262472 < baseStart_2262472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262504 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_2262504 : Nat := 118140960795 + 2262504 * 2 ^ 59
def prefixEnd_2262504 : Nat := 4983230072969 + 3 ^ 40 * 2262504 * 2
def baseEnd_2262504 : Nat := 258167118826693594754431

theorem tailTrace_2262504 : CollatzResearch.WordTrace tailWord_2262504 prefixEnd_2262504 258167118826693594754431 := by
  unfold tailWord_2262504
  simp only [CollatzResearch.WordTrace]
  refine ⟨41260150097670943882521283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55013533463561258510028377 41260150097670943882521283)
  ·
    refine ⟨61890225146506415823781925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41260150097670943882521283 61890225146506415823781925)
    ·
      refine ⟨11604417214969952966959111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61890225146506415823781925 11604417214969952966959111)
      ·
        refine ⟨17406625822454929450438667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11604417214969952966959111 17406625822454929450438667)
        ·
          refine ⟨26109938733682394175658001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17406625822454929450438667 26109938733682394175658001)
          ·
            refine ⟨19582454050261795631743501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26109938733682394175658001 19582454050261795631743501)
            ·
              refine ⟨7343420268848173361903813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19582454050261795631743501 7343420268848173361903813)
              ·
                refine ⟨1376891300409032505356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7343420268848173361903813 1376891300409032505356965)
                ·
                  refine ⟨258167118826693594754431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376891300409032505356965 258167118826693594754431)
                  ·
                    rfl

theorem cell22_2262504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_2262504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262504 prefixEnd_2262504 := by exact prefixLift 2262504
  have htrace : WordTrace (prefixWord ++ tailWord_2262504) baseStart_2262504 baseEnd_2262504 := by
    simpa [prefixWord, tailWord_2262504, baseEnd_2262504] using wordTrace_append hprefix tailTrace_2262504
  have hstable : (prefixWord ++ tailWord_2262504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262504).length < 2 ^ (prefixWord ++ tailWord_2262504).sum := by decide
  have hdescent : baseEnd_2262504 < baseStart_2262504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262515 : List Nat := [1, 1, 1, 2, 2, 2, 2, 11]
def baseStart_2262515 : Nat := 118140960795 + 2262515 * 2 ^ 59
def prefixEnd_2262515 : Nat := 4983230072969 + 3 ^ 40 * 2262515 * 2
def baseEnd_2262515 : Nat := 86056124667208935804251

theorem tailTrace_2262515 : CollatzResearch.WordTrace tailWord_2262515 prefixEnd_2262515 86056124667208935804251 := by
  unfold tailWord_2262515
  simp only [CollatzResearch.WordTrace]
  refine ⟨82520701398302036643692999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55013800932201357762461999 82520701398302036643692999)
  ·
    refine ⟨123781052097453054965539499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82520701398302036643692999 123781052097453054965539499)
    ·
      refine ⟨185671578146179582448309249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123781052097453054965539499 185671578146179582448309249)
      ·
        refine ⟨139253683609634686836231937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185671578146179582448309249 139253683609634686836231937)
        ·
          refine ⟨104440262707226015127173953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139253683609634686836231937 104440262707226015127173953)
          ·
            refine ⟨78330197030419511345380465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104440262707226015127173953 78330197030419511345380465)
            ·
              refine ⟨58747647772814633509035349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78330197030419511345380465 58747647772814633509035349)
              ·
                refine ⟨86056124667208935804251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58747647772814633509035349 86056124667208935804251)
                ·
                  rfl

theorem cell22_2262515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_2262515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262515 prefixEnd_2262515 := by exact prefixLift 2262515
  have htrace : WordTrace (prefixWord ++ tailWord_2262515) baseStart_2262515 baseEnd_2262515 := by
    simpa [prefixWord, tailWord_2262515, baseEnd_2262515] using wordTrace_append hprefix tailTrace_2262515
  have hstable : (prefixWord ++ tailWord_2262515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262515).length < 2 ^ (prefixWord ++ tailWord_2262515).sum := by decide
  have hdescent : baseEnd_2262515 < baseStart_2262515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262562 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2262562 : Nat := 118140960795 + 2262562 * 2 ^ 59
def prefixEnd_2262562 : Nat := 4983230072969 + 3 ^ 40 * 2262562 * 2
def baseEnd_2262562 : Nat := 774521211065387966313115

theorem tailTrace_2262562 : CollatzResearch.WordTrace tailWord_2262562 prefixEnd_2262562 774521211065387966313115 := by
  unfold tailWord_2262562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20630603907282940917663485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55014943752754509113769293 20630603907282940917663485)
  ·
    refine ⟨7736476465231102844123807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20630603907282940917663485 7736476465231102844123807)
    ·
      refine ⟨11604714697846654266185711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7736476465231102844123807 11604714697846654266185711)
      ·
        refine ⟨17407072046769981399278567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11604714697846654266185711 17407072046769981399278567)
        ·
          refine ⟨26110608070154972098917851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17407072046769981399278567 26110608070154972098917851)
          ·
            refine ⟨39165912105232458148376777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26110608070154972098917851 39165912105232458148376777)
            ·
              refine ⟨29374434078924343611282583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39165912105232458148376777 29374434078924343611282583)
              ·
                refine ⟨44061651118386515416923875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29374434078924343611282583 44061651118386515416923875)
                ·
                  refine ⟨66092476677579773125385813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44061651118386515416923875 66092476677579773125385813)
                  ·
                    refine ⟨774521211065387966313115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66092476677579773125385813 774521211065387966313115)
                    ·
                      rfl

theorem cell22_2262562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2262562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262562 prefixEnd_2262562 := by exact prefixLift 2262562
  have htrace : WordTrace (prefixWord ++ tailWord_2262562) baseStart_2262562 baseEnd_2262562 := by
    simpa [prefixWord, tailWord_2262562, baseEnd_2262562] using wordTrace_append hprefix tailTrace_2262562
  have hstable : (prefixWord ++ tailWord_2262562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262562).length < 2 ^ (prefixWord ++ tailWord_2262562).sum := by decide
  have hdescent : baseEnd_2262562 < baseStart_2262562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262607 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_2262607 : Nat := 118140960795 + 2262607 * 2 ^ 59
def prefixEnd_2262607 : Nat := 4983230072969 + 3 ^ 40 * 2262607 * 2
def baseEnd_2262607 : Nat := 774536615485022848937977

theorem tailTrace_2262607 : CollatzResearch.WordTrace tailWord_2262607 prefixEnd_2262607 774536615485022848937977 := by
  unfold tailWord_2262607
  simp only [CollatzResearch.WordTrace]
  refine ⟨82524056913968736356042075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55016037942645824237361383 82524056913968736356042075)
  ·
    refine ⟨123786085370953104534063113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82524056913968736356042075 123786085370953104534063113)
    ·
      refine ⟨92839564028214828400547335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123786085370953104534063113 92839564028214828400547335)
      ·
        refine ⟨139259346042322242600821003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92839564028214828400547335 139259346042322242600821003)
        ·
          refine ⟨208889019063483363901231505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139259346042322242600821003 208889019063483363901231505)
          ·
            refine ⟨156666764297612522925923629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208889019063483363901231505 156666764297612522925923629)
            ·
              refine ⟨58750036611604696097221361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156666764297612522925923629 58750036611604696097221361)
              ·
                refine ⟨44062527458703522072916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58750036611604696097221361 44062527458703522072916021)
                ·
                  refine ⟨4130861949253455194335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44062527458703522072916021 4130861949253455194335877)
                  ·
                    refine ⟨774536615485022848937977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4130861949253455194335877 774536615485022848937977)
                    ·
                      rfl

theorem cell22_2262607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_2262607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262607 prefixEnd_2262607 := by exact prefixLift 2262607
  have htrace : WordTrace (prefixWord ++ tailWord_2262607) baseStart_2262607 baseEnd_2262607 := by
    simpa [prefixWord, tailWord_2262607, baseEnd_2262607] using wordTrace_append hprefix tailTrace_2262607
  have hstable : (prefixWord ++ tailWord_2262607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262607).length < 2 ^ (prefixWord ++ tailWord_2262607).sum := by decide
  have hdescent : baseEnd_2262607 < baseStart_2262607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_2262697 : Nat := 118140960795 + 2262697 * 2 ^ 59
def prefixEnd_2262697 : Nat := 4983230072969 + 3 ^ 40 * 2262697 * 2
def baseEnd_2262697 : Nat := 774567424324292614187701

theorem tailTrace_2262697 : CollatzResearch.WordTrace tailWord_2262697 prefixEnd_2262697 774567424324292614187701 := by
  unfold tailWord_2262697
  simp only [CollatzResearch.WordTrace]
  refine ⟨82527339483642681726818345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55018226322428454484545563 82527339483642681726818345)
  ·
    refine ⟨61895504612732011295113759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82527339483642681726818345 61895504612732011295113759)
    ·
      refine ⟨92843256919098016942670639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61895504612732011295113759 92843256919098016942670639)
      ·
        refine ⟨139264885378647025414005959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92843256919098016942670639 139264885378647025414005959)
        ·
          refine ⟨208897328067970538121008939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139264885378647025414005959 208897328067970538121008939)
          ·
            refine ⟨313345992101955807181513409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208897328067970538121008939 313345992101955807181513409)
            ·
              refine ⟨235009494076466855386135057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313345992101955807181513409 235009494076466855386135057)
              ·
                refine ⟨176257120557350141539601293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235009494076466855386135057 176257120557350141539601293)
                ·
                  refine ⟨66096420209006303077350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176257120557350141539601293 66096420209006303077350485)
                  ·
                    refine ⟨774567424324292614187701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66096420209006303077350485 774567424324292614187701)
                    ·
                      rfl

theorem cell22_2262697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_2262697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262697 prefixEnd_2262697 := by exact prefixLift 2262697
  have htrace : WordTrace (prefixWord ++ tailWord_2262697) baseStart_2262697 baseEnd_2262697 := by
    simpa [prefixWord, tailWord_2262697, baseEnd_2262697] using wordTrace_append hprefix tailTrace_2262697
  have hstable : (prefixWord ++ tailWord_2262697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262697).length < 2 ^ (prefixWord ++ tailWord_2262697).sum := by decide
  have hdescent : baseEnd_2262697 < baseStart_2262697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262701 : List Nat := [1, 5, 2, 1, 1, 1, 5, 6]
def baseStart_2262701 : Nat := 118140960795 + 2262701 * 2 ^ 59
def prefixEnd_2262701 : Nat := 4983230072969 + 3 ^ 40 * 2262701 * 2
def baseEnd_2262701 : Nat := 86063199289559770787521

theorem tailTrace_2262701 : CollatzResearch.WordTrace tailWord_2262701 prefixEnd_2262701 86063199289559770787521 := by
  unfold tailWord_2262701
  simp only [CollatzResearch.WordTrace]
  refine ⟨82527485375628190409963957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55018323583752126939975971 82527485375628190409963957)
  ·
    refine ⟨7736951753965142850934121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82527485375628190409963957 7736951753965142850934121)
    ·
      refine ⟨5802713815473857138200591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7736951753965142850934121 5802713815473857138200591)
      ·
        refine ⟨8704070723210785707300887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802713815473857138200591 8704070723210785707300887)
        ·
          refine ⟨13056106084816178560951331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8704070723210785707300887 13056106084816178560951331)
          ·
            refine ⟨19584159127224267841426997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056106084816178560951331 19584159127224267841426997)
            ·
              refine ⟨1836014918177275110133781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19584159127224267841426997 1836014918177275110133781)
              ·
                refine ⟨86063199289559770787521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1836014918177275110133781 86063199289559770787521)
                ·
                  rfl

theorem cell22_2262701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 6].length) (baseStart_2262701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262701 prefixEnd_2262701 := by exact prefixLift 2262701
  have htrace : WordTrace (prefixWord ++ tailWord_2262701) baseStart_2262701 baseEnd_2262701 := by
    simpa [prefixWord, tailWord_2262701, baseEnd_2262701] using wordTrace_append hprefix tailTrace_2262701
  have hstable : (prefixWord ++ tailWord_2262701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262701).length < 2 ^ (prefixWord ++ tailWord_2262701).sum := by decide
  have hdescent : baseEnd_2262701 < baseStart_2262701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262722 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2262722 : Nat := 118140960795 + 2262722 * 2 ^ 59
def prefixEnd_2262722 : Nat := 4983230072969 + 3 ^ 40 * 2262722 * 2
def baseEnd_2262722 : Nat := 774575982335200882312625

theorem tailTrace_2262722 : CollatzResearch.WordTrace tailWord_2262722 prefixEnd_2262722 774575982335200882312625 := by
  unfold tailWord_2262722
  simp only [CollatzResearch.WordTrace]
  refine ⟨20632062827138027749119605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55018834205701407330985613 20632062827138027749119605)
  ·
    refine ⟨1934255890044190101479963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20632062827138027749119605 1934255890044190101479963)
    ·
      refine ⟨2901383835066285152219945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934255890044190101479963 2901383835066285152219945)
      ·
        refine ⟨2176037876299713864164959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2901383835066285152219945 2176037876299713864164959)
        ·
          refine ⟨3264056814449570796247439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176037876299713864164959 3264056814449570796247439)
          ·
            refine ⟨4896085221674356194371159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264056814449570796247439 4896085221674356194371159)
            ·
              refine ⟨7344127832511534291556739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896085221674356194371159 7344127832511534291556739)
              ·
                refine ⟨11016191748767301437335109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7344127832511534291556739 11016191748767301437335109)
                ·
                  refine ⟨2065535952893869019500333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11016191748767301437335109 2065535952893869019500333)
                  ·
                    refine ⟨774575982335200882312625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065535952893869019500333 774575982335200882312625)
                    ·
                      rfl

theorem cell22_2262722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2262722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262722 prefixEnd_2262722 := by exact prefixLift 2262722
  have htrace : WordTrace (prefixWord ++ tailWord_2262722) baseStart_2262722 baseEnd_2262722 := by
    simpa [prefixWord, tailWord_2262722, baseEnd_2262722] using wordTrace_append hprefix tailTrace_2262722
  have hstable : (prefixWord ++ tailWord_2262722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262722).length < 2 ^ (prefixWord ++ tailWord_2262722).sum := by decide
  have hdescent : baseEnd_2262722 < baseStart_2262722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262744 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2262744 : Nat := 118140960795 + 2262744 * 2 ^ 59
def prefixEnd_2262744 : Nat := 4983230072969 + 3 ^ 40 * 2262744 * 2
def baseEnd_2262744 : Nat := 774583513384800158262557

theorem tailTrace_2262744 : CollatzResearch.WordTrace tailWord_2262744 prefixEnd_2262744 774583513384800158262557 := by
  unfold tailWord_2262744
  simp only [CollatzResearch.WordTrace]
  refine ⟨41264526857236204376889643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55019369142981605835852857 41264526857236204376889643)
  ·
    refine ⟨61896790285854306565334465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41264526857236204376889643 61896790285854306565334465)
    ·
      refine ⟨46422592714390729924000849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61896790285854306565334465 46422592714390729924000849)
      ·
        refine ⟨34816944535793047443000637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46422592714390729924000849 34816944535793047443000637)
        ·
          refine ⟨13056354200922392791125239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34816944535793047443000637 13056354200922392791125239)
          ·
            refine ⟨19584531301383589186687859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056354200922392791125239 19584531301383589186687859)
            ·
              refine ⟨29376796952075383780031789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19584531301383589186687859 29376796952075383780031789)
              ·
                refine ⟨11016298857028268917511921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29376796952075383780031789 11016298857028268917511921)
                ·
                  refine ⟨8262224142771201688133941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11016298857028268917511921 8262224142771201688133941)
                  ·
                    refine ⟨774583513384800158262557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8262224142771201688133941 774583513384800158262557)
                    ·
                      rfl

theorem cell22_2262744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2262744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262744 prefixEnd_2262744 := by exact prefixLift 2262744
  have htrace : WordTrace (prefixWord ++ tailWord_2262744) baseStart_2262744 baseEnd_2262744 := by
    simpa [prefixWord, tailWord_2262744, baseEnd_2262744] using wordTrace_append hprefix tailTrace_2262744
  have hstable : (prefixWord ++ tailWord_2262744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262744).length < 2 ^ (prefixWord ++ tailWord_2262744).sum := by decide
  have hdescent : baseEnd_2262744 < baseStart_2262744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262790 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2262790 : Nat := 118140960795 + 2262790 * 2 ^ 59
def prefixEnd_2262790 : Nat := 4983230072969 + 3 ^ 40 * 2262790 * 2
def baseEnd_2262790 : Nat := 774599260124871371612417

theorem tailTrace_2262790 : CollatzResearch.WordTrace tailWord_2262790 prefixEnd_2262790 774599260124871371612417 := by
  unfold tailWord_2262790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579085358509554956561057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55020487648203839073302549 2579085358509554956561057)
  ·
    refine ⟨1934314018882166217420793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2579085358509554956561057 1934314018882166217420793)
    ·
      refine ⟨1450735514161624663065595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934314018882166217420793 1450735514161624663065595)
      ·
        refine ⟨2176103271242436994598393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450735514161624663065595 2176103271242436994598393)
        ·
          refine ⟨1632077453431827745948795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176103271242436994598393 1632077453431827745948795)
          ·
            refine ⟨2448116180147741618923193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632077453431827745948795 2448116180147741618923193)
            ·
              refine ⟨1836087135110806214192395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2448116180147741618923193 1836087135110806214192395)
              ·
                refine ⟨2754130702666209321288593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836087135110806214192395 2754130702666209321288593)
                ·
                  refine ⟨2065598026999656990966445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754130702666209321288593 2065598026999656990966445)
                  ·
                    refine ⟨774599260124871371612417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065598026999656990966445 774599260124871371612417)
                    ·
                      rfl

theorem cell22_2262790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2262790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262790 prefixEnd_2262790 := by exact prefixLift 2262790
  have htrace : WordTrace (prefixWord ++ tailWord_2262790) baseStart_2262790 baseEnd_2262790 := by
    simpa [prefixWord, tailWord_2262790, baseEnd_2262790] using wordTrace_append hprefix tailTrace_2262790
  have hstable : (prefixWord ++ tailWord_2262790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262790).length < 2 ^ (prefixWord ++ tailWord_2262790).sum := by decide
  have hdescent : baseEnd_2262790 < baseStart_2262790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262819 : List Nat := [1, 1, 1, 4, 2, 1, 4, 8]
def baseStart_2262819 : Nat := 118140960795 + 2262819 * 2 ^ 59
def prefixEnd_2262819 : Nat := 4983230072969 + 3 ^ 40 * 2262819 * 2
def baseEnd_2262819 : Nat := 86067687490836106959703

theorem tailTrace_2262819 : CollatzResearch.WordTrace tailWord_2262819 prefixEnd_2262819 86067687490836106959703 := by
  unfold tailWord_2262819
  simp only [CollatzResearch.WordTrace]
  refine ⟨82531789189200696562759511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55021192792800464375173007 82531789189200696562759511)
  ·
    refine ⟨123797683783801044844139267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82531789189200696562759511 123797683783801044844139267)
    ·
      refine ⟨185696525675701567266208901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123797683783801044844139267 185696525675701567266208901)
      ·
        refine ⟨34818098564194043862414169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185696525675701567266208901 34818098564194043862414169)
        ·
          refine ⟨26113573923145532896810627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34818098564194043862414169 26113573923145532896810627)
          ·
            refine ⟨39170360884718299345215941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26113573923145532896810627 39170360884718299345215941)
            ·
              refine ⟨7344442665884681127227989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39170360884718299345215941 7344442665884681127227989)
              ·
                refine ⟨86067687490836106959703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7344442665884681127227989 86067687490836106959703)
                ·
                  rfl

theorem cell22_2262819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_2262819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262819 prefixEnd_2262819 := by exact prefixLift 2262819
  have htrace : WordTrace (prefixWord ++ tailWord_2262819) baseStart_2262819 baseEnd_2262819 := by
    simpa [prefixWord, tailWord_2262819, baseEnd_2262819] using wordTrace_append hprefix tailTrace_2262819
  have hstable : (prefixWord ++ tailWord_2262819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262819).length < 2 ^ (prefixWord ++ tailWord_2262819).sum := by decide
  have hdescent : baseEnd_2262819 < baseStart_2262819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262821 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_2262821 : Nat := 118140960795 + 2262821 * 2 ^ 59
def prefixEnd_2262821 : Nat := 4983230072969 + 3 ^ 40 * 2262821 * 2
def baseEnd_2262821 : Nat := 774609872058397624087321

theorem tailTrace_2262821 : CollatzResearch.WordTrace tailWord_2262821 prefixEnd_2262821 774609872058397624087321 := by
  unfold tailWord_2262821
  simp only [CollatzResearch.WordTrace]
  refine ⟨82531862135193450904332317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55021241423462300602888211 82531862135193450904332317)
  ·
    refine ⟨30949448300697544089124619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82531862135193450904332317 30949448300697544089124619)
    ·
      refine ⟨46424172451046316133686929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30949448300697544089124619 46424172451046316133686929)
      ·
        refine ⟨34818129338284737100265197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46424172451046316133686929 34818129338284737100265197)
        ·
          refine ⟨13056798501856776412599449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34818129338284737100265197 13056798501856776412599449)
          ·
            refine ⟨9792598876392582309449587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13056798501856776412599449 9792598876392582309449587)
            ·
              refine ⟨14688898314588873464174381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9792598876392582309449587 14688898314588873464174381)
              ·
                refine ⟨5508336867970827549065393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14688898314588873464174381 5508336867970827549065393)
                ·
                  refine ⟨4131252650978120661799045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5508336867970827549065393 4131252650978120661799045)
                  ·
                    refine ⟨774609872058397624087321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131252650978120661799045 774609872058397624087321)
                    ·
                      rfl

theorem cell22_2262821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_2262821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262821 prefixEnd_2262821 := by exact prefixLift 2262821
  have htrace : WordTrace (prefixWord ++ tailWord_2262821) baseStart_2262821 baseEnd_2262821 := by
    simpa [prefixWord, tailWord_2262821, baseEnd_2262821] using wordTrace_append hprefix tailTrace_2262821
  have hstable : (prefixWord ++ tailWord_2262821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262821).length < 2 ^ (prefixWord ++ tailWord_2262821).sum := by decide
  have hdescent : baseEnd_2262821 < baseStart_2262821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262836 : List Nat := [2, 5, 1, 1, 2, 11]
def baseStart_2262836 : Nat := 118140960795 + 2262836 * 2 ^ 59
def prefixEnd_2262836 : Nat := 4983230072969 + 3 ^ 40 * 2262836 * 2
def baseEnd_2262836 : Nat := 9563148232900525740275

theorem tailTrace_2262836 : CollatzResearch.WordTrace tailWord_2262836 prefixEnd_2262836 9563148232900525740275 := by
  unfold tailWord_2262836
  simp only [CollatzResearch.WordTrace]
  refine ⟨41266204615069554233064181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55021606153426072310752241 41266204615069554233064181)
  ·
    refine ⟨3868706682662770709349767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41266204615069554233064181 3868706682662770709349767)
    ·
      refine ⟨5803060023994156064024651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868706682662770709349767 5803060023994156064024651)
      ·
        refine ⟨8704590035991234096036977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5803060023994156064024651 8704590035991234096036977)
        ·
          refine ⟨6528442526993425572027733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8704590035991234096036977 6528442526993425572027733)
          ·
            refine ⟨9563148232900525740275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6528442526993425572027733 9563148232900525740275)
            ·
              rfl

theorem cell22_2262836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 11].length) (baseStart_2262836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262836 prefixEnd_2262836 := by exact prefixLift 2262836
  have htrace : WordTrace (prefixWord ++ tailWord_2262836) baseStart_2262836 baseEnd_2262836 := by
    simpa [prefixWord, tailWord_2262836, baseEnd_2262836] using wordTrace_append hprefix tailTrace_2262836
  have hstable : (prefixWord ++ tailWord_2262836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262836).length < 2 ^ (prefixWord ++ tailWord_2262836).sum := by decide
  have hdescent : baseEnd_2262836 < baseStart_2262836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262864 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_2262864 : Nat := 118140960795 + 2262864 * 2 ^ 59
def prefixEnd_2262864 : Nat := 4983230072969 + 3 ^ 40 * 2262864 * 2
def baseEnd_2262864 : Nat := 258208197279053281754063

theorem tailTrace_2262864 : CollatzResearch.WordTrace tailWord_2262864 prefixEnd_2262864 258208197279053281754063 := by
  unfold tailWord_2262864
  simp only [CollatzResearch.WordTrace]
  refine ⟨41266715237018834624073823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55022286982691779498765097 41266715237018834624073823)
  ·
    refine ⟨61900072855528251936110735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41266715237018834624073823 61900072855528251936110735)
    ·
      refine ⟨92850109283292377904166103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61900072855528251936110735 92850109283292377904166103)
      ·
        refine ⟨139275163924938566856249155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92850109283292377904166103 139275163924938566856249155)
        ·
          refine ⟨208912745887407850284373733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139275163924938566856249155 208912745887407850284373733)
          ·
            refine ⟨39171139853888971928320075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208912745887407850284373733 39171139853888971928320075)
            ·
              refine ⟨58756709780833457892480113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39171139853888971928320075 58756709780833457892480113)
              ·
                refine ⟨44067532335625093419360085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58756709780833457892480113 44067532335625093419360085)
                ·
                  refine ⟨258208197279053281754063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44067532335625093419360085 258208197279053281754063)
                  ·
                    rfl

theorem cell22_2262864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_2262864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262864 prefixEnd_2262864 := by exact prefixLift 2262864
  have htrace : WordTrace (prefixWord ++ tailWord_2262864) baseStart_2262864 baseEnd_2262864 := by
    simpa [prefixWord, tailWord_2262864, baseEnd_2262864] using wordTrace_append hprefix tailTrace_2262864
  have hstable : (prefixWord ++ tailWord_2262864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262864).length < 2 ^ (prefixWord ++ tailWord_2262864).sum := by decide
  have hdescent : baseEnd_2262864 < baseStart_2262864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262868 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2262868 : Nat := 118140960795 + 2262868 * 2 ^ 59
def prefixEnd_2262868 : Nat := 4983230072969 + 3 ^ 40 * 2262868 * 2
def baseEnd_2262868 : Nat := 774625961118905168162177

theorem tailTrace_2262868 : CollatzResearch.WordTrace tailWord_2262868 prefixEnd_2262868 774625961118905168162177 := by
  unfold tailWord_2262868
  simp only [CollatzResearch.WordTrace]
  refine ⟨41266788183011588965646629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55022384244015451954195505 41266788183011588965646629)
  ·
    refine ⟨7737522784314672931058743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41266788183011588965646629 7737522784314672931058743)
    ·
      refine ⟨11606284176472009396588115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737522784314672931058743 11606284176472009396588115)
      ·
        refine ⟨17409426264708014094882173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11606284176472009396588115 17409426264708014094882173)
        ·
          refine ⟨6528534849265505285580815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17409426264708014094882173 6528534849265505285580815)
          ·
            refine ⟨9792802273898257928371223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528534849265505285580815 9792802273898257928371223)
            ·
              refine ⟨14689203410847386892556835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9792802273898257928371223 14689203410847386892556835)
              ·
                refine ⟨22033805116271080338835253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14689203410847386892556835 22033805116271080338835253)
                ·
                  refine ⟨2065669229650413781765805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22033805116271080338835253 2065669229650413781765805)
                  ·
                    refine ⟨774625961118905168162177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065669229650413781765805 774625961118905168162177)
                    ·
                      rfl

theorem cell22_2262868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2262868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262868 prefixEnd_2262868 := by exact prefixLift 2262868
  have htrace : WordTrace (prefixWord ++ tailWord_2262868) baseStart_2262868 baseEnd_2262868 := by
    simpa [prefixWord, tailWord_2262868, baseEnd_2262868] using wordTrace_append hprefix tailTrace_2262868
  have hstable : (prefixWord ++ tailWord_2262868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262868).length < 2 ^ (prefixWord ++ tailWord_2262868).sum := by decide
  have hdescent : baseEnd_2262868 < baseStart_2262868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262902 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2262902 : Nat := 118140960795 + 2262902 * 2 ^ 59
def prefixEnd_2262902 : Nat := 4983230072969 + 3 ^ 40 * 2262902 * 2
def baseEnd_2262902 : Nat := 774637600013740412812073

theorem tailTrace_2262902 : CollatzResearch.WordTrace tailWord_2262902 prefixEnd_2262902 774637600013740412812073 := by
  unfold tailWord_2262902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158426027993750108626935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55023210965266667825353973 5158426027993750108626935)
  ·
    refine ⟨7737639041990625162940403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5158426027993750108626935 7737639041990625162940403)
    ·
      refine ⟨11606458562985937744410605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7737639041990625162940403 11606458562985937744410605)
      ·
        refine ⟨4352421961119726654153977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11606458562985937744410605 4352421961119726654153977)
        ·
          refine ⟨3264316470839794990615483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352421961119726654153977 3264316470839794990615483)
          ·
            refine ⟨4896474706259692485923225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264316470839794990615483 4896474706259692485923225)
            ·
              refine ⟨3672356029694769364442419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896474706259692485923225 3672356029694769364442419)
              ·
                refine ⟨5508534044542154046663629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672356029694769364442419 5508534044542154046663629)
                ·
                  refine ⟨2065700266703307767498861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5508534044542154046663629 2065700266703307767498861)
                  ·
                    refine ⟨774637600013740412812073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065700266703307767498861 774637600013740412812073)
                    ·
                      rfl

theorem cell22_2262902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2262902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262902 prefixEnd_2262902 := by exact prefixLift 2262902
  have htrace : WordTrace (prefixWord ++ tailWord_2262902) baseStart_2262902 baseEnd_2262902 := by
    simpa [prefixWord, tailWord_2262902, baseEnd_2262902] using wordTrace_append hprefix tailTrace_2262902
  have hstable : (prefixWord ++ tailWord_2262902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262902).length < 2 ^ (prefixWord ++ tailWord_2262902).sum := by decide
  have hdescent : baseEnd_2262902 < baseStart_2262902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262936 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_2262936 : Nat := 118140960795 + 2262936 * 2 ^ 59
def prefixEnd_2262936 : Nat := 4983230072969 + 3 ^ 40 * 2262936 * 2
def baseEnd_2262936 : Nat := 774649238908575657461969

theorem tailTrace_2262936 : CollatzResearch.WordTrace tailWord_2262936 prefixEnd_2262936 774649238908575657461969 := by
  unfold tailWord_2262936
  simp only [CollatzResearch.WordTrace]
  refine ⟨41268028264888412772384331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55024037686517883696512441 41268028264888412772384331)
  ·
    refine ⟨61902042397332619158576497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41268028264888412772384331 61902042397332619158576497)
    ·
      refine ⟨46426531797999464368932373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61902042397332619158576497 46426531797999464368932373)
      ·
        refine ⟨2176243678031224892293705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46426531797999464368932373 2176243678031224892293705)
        ·
          refine ⟨1632182758523418669220279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176243678031224892293705 1632182758523418669220279)
          ·
            refine ⟨2448274137785128003830419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632182758523418669220279 2448274137785128003830419)
            ·
              refine ⟨3672411206677692005745629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448274137785128003830419 3672411206677692005745629)
              ·
                refine ⟨1377154202504134502154611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3672411206677692005745629 1377154202504134502154611)
                ·
                  refine ⟨2065731303756201753231917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377154202504134502154611 2065731303756201753231917)
                  ·
                    refine ⟨774649238908575657461969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2065731303756201753231917 774649238908575657461969)
                    ·
                      rfl

theorem cell22_2262936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_2262936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262936 prefixEnd_2262936 := by exact prefixLift 2262936
  have htrace : WordTrace (prefixWord ++ tailWord_2262936) baseStart_2262936 baseEnd_2262936 := by
    simpa [prefixWord, tailWord_2262936, baseEnd_2262936] using wordTrace_append hprefix tailTrace_2262936
  have hstable : (prefixWord ++ tailWord_2262936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262936).length < 2 ^ (prefixWord ++ tailWord_2262936).sum := by decide
  have hdescent : baseEnd_2262936 < baseStart_2262936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2262986 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_2262986 : Nat := 118140960795 + 2262986 * 2 ^ 59
def prefixEnd_2262986 : Nat := 4983230072969 + 3 ^ 40 * 2262986 * 2
def baseEnd_2262986 : Nat := 774666354930392193711815

theorem tailTrace_2262986 : CollatzResearch.WordTrace tailWord_2262986 prefixEnd_2262986 774666354930392193711815 := by
  unfold tailWord_2262986
  simp only [CollatzResearch.WordTrace]
  refine ⟨20634470044898921021022203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55025253453063789389392541 20634470044898921021022203)
  ·
    refine ⟨30951705067348381531533305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20634470044898921021022203 30951705067348381531533305)
    ·
      refine ⟨23213778800511286148649979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30951705067348381531533305 23213778800511286148649979)
      ·
        refine ⟨34820668200766929222974969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23213778800511286148649979 34820668200766929222974969)
        ·
          refine ⟨26115501150575196917231227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34820668200766929222974969 26115501150575196917231227)
          ·
            refine ⟨39173251725862795375846841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26115501150575196917231227 39173251725862795375846841)
            ·
              refine ⟨29379938794397096531885131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39173251725862795375846841 29379938794397096531885131)
              ·
                refine ⟨44069908191595644797827697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29379938794397096531885131 44069908191595644797827697)
                ·
                  refine ⟨33052431143696733598370773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44069908191595644797827697 33052431143696733598370773)
                  ·
                    refine ⟨774666354930392193711815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33052431143696733598370773 774666354930392193711815)
                    ·
                      rfl

theorem cell22_2262986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_2262986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2262986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2262986 prefixEnd_2262986 := by exact prefixLift 2262986
  have htrace : WordTrace (prefixWord ++ tailWord_2262986) baseStart_2262986 baseEnd_2262986 := by
    simpa [prefixWord, tailWord_2262986, baseEnd_2262986] using wordTrace_append hprefix tailTrace_2262986
  have hstable : (prefixWord ++ tailWord_2262986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2262986).length < 2 ^ (prefixWord ++ tailWord_2262986).sum := by decide
  have hdescent : baseEnd_2262986 < baseStart_2262986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2262986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263033 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 5]
def baseStart_2263033 : Nat := 118140960795 + 2263033 * 2 ^ 59
def prefixEnd_2263033 : Nat := 4983230072969 + 3 ^ 40 * 2263033 * 2
def baseEnd_2263033 : Nat := 258227481330299912595557

theorem tailTrace_2263033 : CollatzResearch.WordTrace tailWord_2263033 prefixEnd_2263033 258227481330299912595557 := by
  unfold tailWord_2263033
  simp only [CollatzResearch.WordTrace]
  refine ⟨82539594410425411111049753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55026396273616940740699835 82539594410425411111049753)
  ·
    refine ⟨61904695807819058333287315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82539594410425411111049753 61904695807819058333287315)
    ·
      refine ⟨92857043711728587499930973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61904695807819058333287315 92857043711728587499930973)
      ·
        refine ⟨34821391391898220312474115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92857043711728587499930973 34821391391898220312474115)
        ·
          refine ⟨52232087087847330468711173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34821391391898220312474115 52232087087847330468711173)
          ·
            refine ⟨9793516328971374462883345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52232087087847330468711173 9793516328971374462883345)
            ·
              refine ⟨7345137246728530847162509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9793516328971374462883345 7345137246728530847162509)
              ·
                refine ⟨2754426467523199067685941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345137246728530847162509 2754426467523199067685941)
                ·
                  refine ⟨258227481330299912595557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2754426467523199067685941 258227481330299912595557)
                  ·
                    rfl

theorem cell22_2263033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_2263033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263033 prefixEnd_2263033 := by exact prefixLift 2263033
  have htrace : WordTrace (prefixWord ++ tailWord_2263033) baseStart_2263033 baseEnd_2263033 := by
    simpa [prefixWord, tailWord_2263033, baseEnd_2263033] using wordTrace_append hprefix tailTrace_2263033
  have hstable : (prefixWord ++ tailWord_2263033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263033).length < 2 ^ (prefixWord ++ tailWord_2263033).sum := by decide
  have hdescent : baseEnd_2263033 < baseStart_2263033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263097 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_2263097 : Nat := 118140960795 + 2263097 * 2 ^ 59
def prefixEnd_2263097 : Nat := 4983230072969 + 3 ^ 40 * 2263097 * 2
def baseEnd_2263097 : Nat := 774704352498824904186475

theorem tailTrace_2263097 : CollatzResearch.WordTrace tailWord_2263097 prefixEnd_2263097 774704352498824904186475 := by
  unfold tailWord_2263097
  simp only [CollatzResearch.WordTrace]
  refine ⟨82541928682193550041379545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55027952454795700027586363 82541928682193550041379545)
  ·
    refine ⟨61906446511645162531034659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82541928682193550041379545 61906446511645162531034659)
    ·
      refine ⟨92859669767467743796551989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61906446511645162531034659 92859669767467743796551989)
      ·
        refine ⟨8705594040700100980926749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92859669767467743796551989 8705594040700100980926749)
        ·
          refine ⟨3264597765262537867847531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8705594040700100980926749 3264597765262537867847531)
          ·
            refine ⟨4896896647893806801771297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264597765262537867847531 4896896647893806801771297)
            ·
              refine ⟨3672672485920355101328473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896896647893806801771297 3672672485920355101328473)
              ·
                refine ⟨2754504364440266325996355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672672485920355101328473 2754504364440266325996355)
                ·
                  refine ⟨4131756546660399488994533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754504364440266325996355 4131756546660399488994533)
                  ·
                    refine ⟨774704352498824904186475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131756546660399488994533 774704352498824904186475)
                    ·
                      rfl

theorem cell22_2263097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_2263097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263097 prefixEnd_2263097 := by exact prefixLift 2263097
  have htrace : WordTrace (prefixWord ++ tailWord_2263097) baseStart_2263097 baseEnd_2263097 := by
    simpa [prefixWord, tailWord_2263097, baseEnd_2263097] using wordTrace_append hprefix tailTrace_2263097
  have hstable : (prefixWord ++ tailWord_2263097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263097).length < 2 ^ (prefixWord ++ tailWord_2263097).sum := by decide
  have hdescent : baseEnd_2263097 < baseStart_2263097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263125 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2263125 : Nat := 118140960795 + 2263125 * 2 ^ 59
def prefixEnd_2263125 : Nat := 4983230072969 + 3 ^ 40 * 2263125 * 2
def baseEnd_2263125 : Nat := 774713937471042164486389

theorem tailTrace_2263125 : CollatzResearch.WordTrace tailWord_2263125 prefixEnd_2263125 774713937471042164486389 := by
  unfold tailWord_2263125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82542949926092110823398829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55028633284061407215599219 82542949926092110823398829)
  ·
    refine ⟨30953606222284541558774561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82542949926092110823398829 30953606222284541558774561)
    ·
      refine ⟨23215204666713406169080921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30953606222284541558774561 23215204666713406169080921)
      ·
        refine ⟨17411403500035054626810691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23215204666713406169080921 17411403500035054626810691)
        ·
          refine ⟨26117105250052581940216037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17411403500035054626810691 26117105250052581940216037)
          ·
            refine ⟨4896957234384859113790507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26117105250052581940216037 4896957234384859113790507)
            ·
              refine ⟨7345435851577288670685761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896957234384859113790507 7345435851577288670685761)
              ·
                refine ⟨5509076888682966503014321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7345435851577288670685761 5509076888682966503014321)
                ·
                  refine ⟨4131807666512224877260741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5509076888682966503014321 4131807666512224877260741)
                  ·
                    refine ⟨774713937471042164486389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131807666512224877260741 774713937471042164486389)
                    ·
                      rfl

theorem cell22_2263125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2263125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263125 prefixEnd_2263125 := by exact prefixLift 2263125
  have htrace : WordTrace (prefixWord ++ tailWord_2263125) baseStart_2263125 baseEnd_2263125 := by
    simpa [prefixWord, tailWord_2263125, baseEnd_2263125] using wordTrace_append hprefix tailTrace_2263125
  have hstable : (prefixWord ++ tailWord_2263125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263125).length < 2 ^ (prefixWord ++ tailWord_2263125).sum := by decide
  have hdescent : baseEnd_2263125 < baseStart_2263125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263200 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_2263200 : Nat := 118140960795 + 2263200 * 2 ^ 59
def prefixEnd_2263200 : Nat := 4983230072969 + 3 ^ 40 * 2263200 * 2
def baseEnd_2263200 : Nat := 774739611503766968861159

theorem tailTrace_2263200 : CollatzResearch.WordTrace tailWord_2263200 prefixEnd_2263200 774739611503766968861159 := by
  unfold tailWord_2263200
  simp only [CollatzResearch.WordTrace]
  refine ⟨41272842700410199316189527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55030456933880265754919369 41272842700410199316189527)
  ·
    refine ⟨61909264050615298974284291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41272842700410199316189527 61909264050615298974284291)
    ·
      refine ⟨92863896075922948461426437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61909264050615298974284291 92863896075922948461426437)
      ·
        refine ⟨17411980514235552836517457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92863896075922948461426437 17411980514235552836517457)
        ·
          refine ⟨13058985385676664627388093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17411980514235552836517457 13058985385676664627388093)
          ·
            refine ⟨4897119519628749235270535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13058985385676664627388093 4897119519628749235270535)
            ·
              refine ⟨7345679279443123852905803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897119519628749235270535 7345679279443123852905803)
              ·
                refine ⟨11018518919164685779358705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345679279443123852905803 11018518919164685779358705)
                ·
                  refine ⟨8263889189373514334519029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11018518919164685779358705 8263889189373514334519029)
                  ·
                    refine ⟨774739611503766968861159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8263889189373514334519029 774739611503766968861159)
                    ·
                      rfl

theorem cell22_2263200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_2263200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263200 prefixEnd_2263200 := by exact prefixLift 2263200
  have htrace : WordTrace (prefixWord ++ tailWord_2263200) baseStart_2263200 baseEnd_2263200 := by
    simpa [prefixWord, tailWord_2263200, baseEnd_2263200] using wordTrace_append hprefix tailTrace_2263200
  have hstable : (prefixWord ++ tailWord_2263200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263200).length < 2 ^ (prefixWord ++ tailWord_2263200).sum := by decide
  have hdescent : baseEnd_2263200 < baseStart_2263200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263202 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2263202 : Nat := 118140960795 + 2263202 * 2 ^ 59
def prefixEnd_2263202 : Nat := 4983230072969 + 3 ^ 40 * 2263202 * 2
def baseEnd_2263202 : Nat := 258246765381546543437051

theorem tailTrace_2263202 : CollatzResearch.WordTrace tailWord_2263202 prefixEnd_2263202 258246765381546543437051 := by
  unfold tailWord_2263202
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636439586703288243487965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55030505564542101982634573 20636439586703288243487965)
  ·
    refine ⟨7738664845013733091307987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20636439586703288243487965 7738664845013733091307987)
    ·
      refine ⟨11607997267520599636961981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738664845013733091307987 11607997267520599636961981)
      ·
        refine ⟨4352998975320224863860743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11607997267520599636961981 4352998975320224863860743)
        ·
          refine ⟨6529498462980337295791115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4352998975320224863860743 6529498462980337295791115)
          ·
            refine ⟨9794247694470505943686673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529498462980337295791115 9794247694470505943686673)
            ·
              refine ⟨7345685770852879457765005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9794247694470505943686673 7345685770852879457765005)
              ·
                refine ⟨2754632164069829796661877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345685770852879457765005 2754632164069829796661877)
                ·
                  refine ⟨258246765381546543437051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2754632164069829796661877 258246765381546543437051)
                  ·
                    rfl

theorem cell22_2263202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2263202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263202 prefixEnd_2263202 := by exact prefixLift 2263202
  have htrace : WordTrace (prefixWord ++ tailWord_2263202) baseStart_2263202 baseEnd_2263202 := by
    simpa [prefixWord, tailWord_2263202, baseEnd_2263202] using wordTrace_append hprefix tailTrace_2263202
  have hstable : (prefixWord ++ tailWord_2263202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263202).length < 2 ^ (prefixWord ++ tailWord_2263202).sum := by decide
  have hdescent : baseEnd_2263202 < baseStart_2263202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263215 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 1, 4]
def baseStart_2263215 : Nat := 118140960795 + 2263215 * 2 ^ 59
def prefixEnd_2263215 : Nat := 4983230072969 + 3 ^ 40 * 2263215 * 2
def baseEnd_2263215 : Nat := 774744746310311929736113

theorem tailTrace_2263215 : CollatzResearch.WordTrace tailWord_2263215 prefixEnd_2263215 774744746310311929736113 := by
  unfold tailWord_2263215
  simp only [CollatzResearch.WordTrace]
  refine ⟨82546232495766056194175099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55030821663844037462783399 82546232495766056194175099)
  ·
    refine ⟨123819348743649084291262649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82546232495766056194175099 123819348743649084291262649)
    ·
      refine ⟨92864511557736813218446987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123819348743649084291262649 92864511557736813218446987)
      ·
        refine ⟨139296767336605219827670481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92864511557736813218446987 139296767336605219827670481)
        ·
          refine ⟨104472575502453914870752861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139296767336605219827670481 104472575502453914870752861)
          ·
            refine ⟨39177215813420218076532323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104472575502453914870752861 39177215813420218076532323)
            ·
              refine ⟨58765823720130327114798485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39177215813420218076532323 58765823720130327114798485)
              ·
                refine ⟨2754647986881109083506179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58765823720130327114798485 2754647986881109083506179)
                ·
                  refine ⟨4131971980321663625259269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754647986881109083506179 4131971980321663625259269)
                  ·
                    refine ⟨774744746310311929736113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4131971980321663625259269 774744746310311929736113)
                    ·
                      rfl

theorem cell22_2263215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_2263215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263215 prefixEnd_2263215 := by exact prefixLift 2263215
  have htrace : WordTrace (prefixWord ++ tailWord_2263215) baseStart_2263215 baseEnd_2263215 := by
    simpa [prefixWord, tailWord_2263215, baseEnd_2263215] using wordTrace_append hprefix tailTrace_2263215
  have hstable : (prefixWord ++ tailWord_2263215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263215).length < 2 ^ (prefixWord ++ tailWord_2263215).sum := by decide
  have hdescent : baseEnd_2263215 < baseStart_2263215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263232 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_2263232 : Nat := 118140960795 + 2263232 * 2 ^ 59
def prefixEnd_2263232 : Nat := 4983230072969 + 3 ^ 40 * 2263232 * 2
def baseEnd_2263232 : Nat := 774750565757729552061061

theorem tailTrace_2263232 : CollatzResearch.WordTrace tailWord_2263232 prefixEnd_2263232 774750565757729552061061 := by
  unfold tailWord_2263232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273426268352234048771975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55031235024469645398362633 41273426268352234048771975)
  ·
    refine ⟨61910139402528351073157963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41273426268352234048771975 61910139402528351073157963)
    ·
      refine ⟨92865209103792526609736945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61910139402528351073157963 92865209103792526609736945)
      ·
        refine ⟨69648906827844394957302709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92865209103792526609736945 69648906827844394957302709)
        ·
          refine ⟨6529585015110412027247129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69648906827844394957302709 6529585015110412027247129)
          ·
            refine ⟨4897188761332809020435347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6529585015110412027247129 4897188761332809020435347)
            ·
              refine ⟨7345783141999213530653021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897188761332809020435347 7345783141999213530653021)
              ·
                refine ⟨2754668678249705073994883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345783141999213530653021 2754668678249705073994883)
                ·
                  refine ⟨4132003017374557610992325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754668678249705073994883 4132003017374557610992325)
                  ·
                    refine ⟨774750565757729552061061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132003017374557610992325 774750565757729552061061)
                    ·
                      rfl

theorem cell22_2263232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_2263232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263232 prefixEnd_2263232 := by exact prefixLift 2263232
  have htrace : WordTrace (prefixWord ++ tailWord_2263232) baseStart_2263232 baseEnd_2263232 := by
    simpa [prefixWord, tailWord_2263232, baseEnd_2263232] using wordTrace_append hprefix tailTrace_2263232
  have hstable : (prefixWord ++ tailWord_2263232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263232).length < 2 ^ (prefixWord ++ tailWord_2263232).sum := by decide
  have hdescent : baseEnd_2263232 < baseStart_2263232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263234 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2263234 : Nat := 118140960795 + 2263234 * 2 ^ 59
def prefixEnd_2263234 : Nat := 4983230072969 + 3 ^ 40 * 2263234 * 2
def baseEnd_2263234 : Nat := 774751250398602213511055

theorem tailTrace_2263234 : CollatzResearch.WordTrace tailWord_2263234 prefixEnd_2263234 774751250398602213511055 := by
  unfold tailWord_2263234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20636731370674305609779189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55031283655131481626077837 20636731370674305609779189)
  ·
    refine ⟨1934693566000716150916799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20636731370674305609779189 1934693566000716150916799)
    ·
      refine ⟨2902040349001074226375199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934693566000716150916799 2902040349001074226375199)
      ·
        refine ⟨4353060523501611339562799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2902040349001074226375199 4353060523501611339562799)
        ·
          refine ⟨6529590785252417009344199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4353060523501611339562799 6529590785252417009344199)
          ·
            refine ⟨9794386177878625514016299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6529590785252417009344199 9794386177878625514016299)
            ·
              refine ⟨14691579266817938271024449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9794386177878625514016299 14691579266817938271024449)
              ·
                refine ⟨11018684450113453703268337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14691579266817938271024449 11018684450113453703268337)
                ·
                  refine ⟨8264013337585090277451253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11018684450113453703268337 8264013337585090277451253)
                  ·
                    refine ⟨774751250398602213511055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8264013337585090277451253 774751250398602213511055)
                    ·
                      rfl

theorem cell22_2263234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2263234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263234 prefixEnd_2263234 := by exact prefixLift 2263234
  have htrace : WordTrace (prefixWord ++ tailWord_2263234) baseStart_2263234 baseEnd_2263234 := by
    simpa [prefixWord, tailWord_2263234, baseEnd_2263234] using wordTrace_append hprefix tailTrace_2263234
  have hstable : (prefixWord ++ tailWord_2263234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263234).length < 2 ^ (prefixWord ++ tailWord_2263234).sum := by decide
  have hdescent : baseEnd_2263234 < baseStart_2263234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263358 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2263358 : Nat := 118140960795 + 2263358 * 2 ^ 59
def prefixEnd_2263358 : Nat := 4983230072969 + 3 ^ 40 * 2263358 * 2
def baseEnd_2263358 : Nat := 774793698132707223410675

theorem tailTrace_2263358 : CollatzResearch.WordTrace tailWord_2263358 prefixEnd_2263358 774793698132707223410675 := by
  unfold tailWord_2263358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318931016780998952078841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55034298756165327744420485 10318931016780998952078841)
  ·
    refine ⟨7739198262585749214059131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10318931016780998952078841 7739198262585749214059131)
    ·
      refine ⟨11608797393878623821088697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7739198262585749214059131 11608797393878623821088697)
      ·
        refine ⟨8706598045408967865816523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11608797393878623821088697 8706598045408967865816523)
        ·
          refine ⟨13059897068113451798724785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706598045408967865816523 13059897068113451798724785)
          ·
            refine ⟨9794922801085088849043589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13059897068113451798724785 9794922801085088849043589)
            ·
              refine ⟨1836548025203454159195673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9794922801085088849043589 1836548025203454159195673)
              ·
                refine ⟨1377411018902590619396755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836548025203454159195673 1377411018902590619396755)
                ·
                  refine ⟨2066116528353885929095133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377411018902590619396755 2066116528353885929095133)
                  ·
                    refine ⟨774793698132707223410675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066116528353885929095133 774793698132707223410675)
                    ·
                      rfl

theorem cell22_2263358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2263358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263358 prefixEnd_2263358 := by exact prefixLift 2263358
  have htrace : WordTrace (prefixWord ++ tailWord_2263358) baseStart_2263358 baseEnd_2263358 := by
    simpa [prefixWord, tailWord_2263358, baseEnd_2263358] using wordTrace_append hprefix tailTrace_2263358
  have hstable : (prefixWord ++ tailWord_2263358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263358).length < 2 ^ (prefixWord ++ tailWord_2263358).sum := by decide
  have hdescent : baseEnd_2263358 < baseStart_2263358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263397 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_2263397 : Nat := 118140960795 + 2263397 * 2 ^ 59
def prefixEnd_2263397 : Nat := 4983230072969 + 3 ^ 40 * 2263397 * 2
def baseEnd_2263397 : Nat := 774807048629724121685555

theorem tailTrace_2263397 : CollatzResearch.WordTrace tailWord_2263397 prefixEnd_2263397 774807048629724121685555 := by
  unfold tailWord_2263397
  simp only [CollatzResearch.WordTrace]
  refine ⟨82552870581106701277300445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55035247054071134184866963 82552870581106701277300445)
  ·
    refine ⟨30957326467915012978987667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82552870581106701277300445 30957326467915012978987667)
    ·
      refine ⟨46435989701872519468481501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30957326467915012978987667 46435989701872519468481501)
      ·
        refine ⟨17413496138202194800680563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46435989701872519468481501 17413496138202194800680563)
        ·
          refine ⟨26120244207303292201020845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17413496138202194800680563 26120244207303292201020845)
          ·
            refine ⟨9795091577738734575382817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26120244207303292201020845 9795091577738734575382817)
            ·
              refine ⟨7346318683304050931537113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9795091577738734575382817 7346318683304050931537113)
              ·
                refine ⟨5509739012478038198652835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7346318683304050931537113 5509739012478038198652835)
                ·
                  refine ⟨8264608518717057297979253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5509739012478038198652835 8264608518717057297979253)
                  ·
                    refine ⟨774807048629724121685555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8264608518717057297979253 774807048629724121685555)
                    ·
                      rfl

theorem cell22_2263397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_2263397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263397 prefixEnd_2263397 := by exact prefixLift 2263397
  have htrace : WordTrace (prefixWord ++ tailWord_2263397) baseStart_2263397 baseEnd_2263397 := by
    simpa [prefixWord, tailWord_2263397, baseEnd_2263397] using wordTrace_append hprefix tailTrace_2263397
  have hstable : (prefixWord ++ tailWord_2263397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263397).length < 2 ^ (prefixWord ++ tailWord_2263397).sum := by decide
  have hdescent : baseEnd_2263397 < baseStart_2263397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263399 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 4]
def baseStart_2263399 : Nat := 118140960795 + 2263399 * 2 ^ 59
def prefixEnd_2263399 : Nat := 4983230072969 + 3 ^ 40 * 2263399 * 2
def baseEnd_2263399 : Nat := 258269244423532261045183

theorem tailTrace_2263399 : CollatzResearch.WordTrace tailWord_2263399 prefixEnd_2263399 258269244423532261045183 := by
  unfold tailWord_2263399
  simp only [CollatzResearch.WordTrace]
  refine ⟨82552943527099455618873251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55035295684732970412582167 82552943527099455618873251)
  ·
    refine ⟨123829415290649183428309877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82552943527099455618873251 123829415290649183428309877)
    ·
      refine ⟨11609007683498360946404051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123829415290649183428309877 11609007683498360946404051)
      ·
        refine ⟨17413511525247541419606077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11609007683498360946404051 17413511525247541419606077)
        ·
          refine ⟨6530066821967828032352279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17413511525247541419606077 6530066821967828032352279)
          ·
            refine ⟨9795100232951742048528419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6530066821967828032352279 9795100232951742048528419)
            ·
              refine ⟨14692650349427613072792629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9795100232951742048528419 14692650349427613072792629)
              ·
                refine ⟨1377435970258838725574309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14692650349427613072792629 1377435970258838725574309)
                ·
                  refine ⟨258269244423532261045183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1377435970258838725574309 258269244423532261045183)
                  ·
                    rfl

theorem cell22_2263399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 4].length) (baseStart_2263399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263399 prefixEnd_2263399 := by exact prefixLift 2263399
  have htrace : WordTrace (prefixWord ++ tailWord_2263399) baseStart_2263399 baseEnd_2263399 := by
    simpa [prefixWord, tailWord_2263399, baseEnd_2263399] using wordTrace_append hprefix tailTrace_2263399
  have hstable : (prefixWord ++ tailWord_2263399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263399).length < 2 ^ (prefixWord ++ tailWord_2263399).sum := by decide
  have hdescent : baseEnd_2263399 < baseStart_2263399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263431 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 2, 3]
def baseStart_2263431 : Nat := 118140960795 + 2263431 * 2 ^ 59
def prefixEnd_2263431 : Nat := 4983230072969 + 3 ^ 40 * 2263431 * 2
def baseEnd_2263431 : Nat := 774818687524559366335451

theorem tailTrace_2263431 : CollatzResearch.WordTrace tailWord_2263431 prefixEnd_2263431 774818687524559366335451 := by
  unfold tailWord_2263431
  simp only [CollatzResearch.WordTrace]
  refine ⟨82554110662983525084038147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55036073775322350056025431 82554110662983525084038147)
  ·
    refine ⟨123831165994475287626057221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82554110662983525084038147 123831165994475287626057221)
    ·
      refine ⟨23218343623964116429885729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123831165994475287626057221 23218343623964116429885729)
      ·
        refine ⟨17413757717973087322414297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23218343623964116429885729 17413757717973087322414297)
        ·
          refine ⟨13060318288479815491810723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17413757717973087322414297 13060318288479815491810723)
          ·
            refine ⟨19590477432719723237716085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060318288479815491810723 19590477432719723237716085)
            ·
              refine ⟨1836607259317474053535883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19590477432719723237716085 1836607259317474053535883)
              ·
                refine ⟨2754910888976211080303825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836607259317474053535883 2754910888976211080303825)
                ·
                  refine ⟨2066183166732158310227869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754910888976211080303825 2066183166732158310227869)
                  ·
                    refine ⟨774818687524559366335451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066183166732158310227869 774818687524559366335451)
                    ·
                      rfl

theorem cell22_2263431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_2263431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263431 prefixEnd_2263431 := by exact prefixLift 2263431
  have htrace : WordTrace (prefixWord ++ tailWord_2263431) baseStart_2263431 baseEnd_2263431 := by
    simpa [prefixWord, tailWord_2263431, baseEnd_2263431] using wordTrace_append hprefix tailTrace_2263431
  have hstable : (prefixWord ++ tailWord_2263431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263431).length < 2 ^ (prefixWord ++ tailWord_2263431).sum := by decide
  have hdescent : baseEnd_2263431 < baseStart_2263431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263444 : List Nat := [2, 4, 2, 1, 3, 1, 1, 8]
def baseStart_2263444 : Nat := 118140960795 + 2263444 * 2 ^ 59
def prefixEnd_2263444 : Nat := 4983230072969 + 3 ^ 40 * 2263444 * 2
def baseEnd_2263444 : Nat := 86091459743359073973379

theorem tailTrace_2263444 : CollatzResearch.WordTrace tailWord_2263444 prefixEnd_2263444 86091459743359073973379 := by
  unfold tailWord_2263444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41277292405968214152130693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55036389874624285536174257 41277292405968214152130693)
  ·
    refine ⟨7739492326119040153524505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41277292405968214152130693 7739492326119040153524505)
    ·
      refine ⟨5804619244589280115143379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7739492326119040153524505 5804619244589280115143379)
      ·
        refine ⟨8706928866883920172715069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5804619244589280115143379 8706928866883920172715069)
        ·
          refine ⟨3265098325081470064768151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8706928866883920172715069 3265098325081470064768151)
          ·
            refine ⟨4897647487622205097152227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265098325081470064768151 4897647487622205097152227)
            ·
              refine ⟨7346471231433307645728341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897647487622205097152227 7346471231433307645728341)
              ·
                refine ⟨86091459743359073973379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7346471231433307645728341 86091459743359073973379)
                ·
                  rfl

theorem cell22_2263444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_2263444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263444 prefixEnd_2263444 := by exact prefixLift 2263444
  have htrace : WordTrace (prefixWord ++ tailWord_2263444) baseStart_2263444 baseEnd_2263444 := by
    simpa [prefixWord, tailWord_2263444, baseEnd_2263444] using wordTrace_append hprefix tailTrace_2263444
  have hstable : (prefixWord ++ tailWord_2263444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263444).length < 2 ^ (prefixWord ++ tailWord_2263444).sum := by decide
  have hdescent : baseEnd_2263444 < baseStart_2263444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263532 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_2263532 : Nat := 118140960795 + 2263532 * 2 ^ 59
def prefixEnd_2263532 : Nat := 4983230072969 + 3 ^ 40 * 2263532 * 2
def baseEnd_2263532 : Nat := 774853261888628769560141

theorem tailTrace_2263532 : CollatzResearch.WordTrace tailWord_2263532 prefixEnd_2263532 774853261888628769560141 := by
  unfold tailWord_2263532
  simp only [CollatzResearch.WordTrace]
  refine ⟨41278897217808809666732425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55038529623745079555643233 41278897217808809666732425)
  ·
    refine ⟨30959172913356607250049319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41278897217808809666732425 30959172913356607250049319)
    ·
      refine ⟨46438759370034910875073979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30959172913356607250049319 46438759370034910875073979)
      ·
        refine ⟨69658139055052366312610969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46438759370034910875073979 69658139055052366312610969)
        ·
          refine ⟨52243604291289274734458227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69658139055052366312610969 52243604291289274734458227)
          ·
            refine ⟨78365406436933912101687341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52243604291289274734458227 78365406436933912101687341)
            ·
              refine ⟨29387027413850217038132753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78365406436933912101687341 29387027413850217038132753)
              ·
                refine ⟨22040270560387662778599565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29387027413850217038132753 22040270560387662778599565)
                ·
                  refine ⟨8265101460145373541974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22040270560387662778599565 8265101460145373541974837)
                  ·
                    refine ⟨774853261888628769560141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8265101460145373541974837 774853261888628769560141)
                    ·
                      rfl

theorem cell22_2263532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_2263532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263532 prefixEnd_2263532 := by exact prefixLift 2263532
  have htrace : WordTrace (prefixWord ++ tailWord_2263532) baseStart_2263532 baseEnd_2263532 := by
    simpa [prefixWord, tailWord_2263532, baseEnd_2263532] using wordTrace_append hprefix tailTrace_2263532
  have hstable : (prefixWord ++ tailWord_2263532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263532).length < 2 ^ (prefixWord ++ tailWord_2263532).sum := by decide
  have hdescent : baseEnd_2263532 < baseStart_2263532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263549 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2263549 : Nat := 118140960795 + 2263549 * 2 ^ 59
def prefixEnd_2263549 : Nat := 4983230072969 + 3 ^ 40 * 2263549 * 2
def baseEnd_2263549 : Nat := 774859081336046391885089

theorem tailTrace_2263549 : CollatzResearch.WordTrace tailWord_2263549 prefixEnd_2263549 774859081336046391885089 := by
  unfold tailWord_2263549
  simp only [CollatzResearch.WordTrace]
  refine ⟨82558414476556031236833701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55038942984370687491222467 82558414476556031236833701)
  ·
    refine ⟨15479702714354255856906319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82558414476556031236833701 15479702714354255856906319)
    ·
      refine ⟨23219554071531383785359479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15479702714354255856906319 23219554071531383785359479)
      ·
        refine ⟨34829331107297075678039219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219554071531383785359479 34829331107297075678039219)
        ·
          refine ⟨52243996660945613517058829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34829331107297075678039219 52243996660945613517058829)
          ·
            refine ⟨19591498747854605068897061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52243996660945613517058829 19591498747854605068897061)
            ·
              refine ⟨3673406015222738450418199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19591498747854605068897061 3673406015222738450418199)
              ·
                refine ⟨5510109022834107675627299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673406015222738450418199 5510109022834107675627299)
                ·
                  refine ⟨8265163534251161513440949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5510109022834107675627299 8265163534251161513440949)
                  ·
                    refine ⟨774859081336046391885089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8265163534251161513440949 774859081336046391885089)
                    ·
                      rfl

theorem cell22_2263549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2263549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263549 prefixEnd_2263549 := by exact prefixLift 2263549
  have htrace : WordTrace (prefixWord ++ tailWord_2263549) baseStart_2263549 baseEnd_2263549 := by
    simpa [prefixWord, tailWord_2263549, baseEnd_2263549] using wordTrace_append hprefix tailTrace_2263549
  have hstable : (prefixWord ++ tailWord_2263549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263549).length < 2 ^ (prefixWord ++ tailWord_2263549).sum := by decide
  have hdescent : baseEnd_2263549 < baseStart_2263549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263564 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_2263564 : Nat := 118140960795 + 2263564 * 2 ^ 59
def prefixEnd_2263564 : Nat := 4983230072969 + 3 ^ 40 * 2263564 * 2
def baseEnd_2263564 : Nat := 774864216142591352760043

theorem tailTrace_2263564 : CollatzResearch.WordTrace tailWord_2263564 prefixEnd_2263564 774864216142591352760043 := by
  unfold tailWord_2263564
  simp only [CollatzResearch.WordTrace]
  refine ⟨41279480785750844399314873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55039307714334459199086497 41279480785750844399314873)
  ·
    refine ⟨30959610589313133299486155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41279480785750844399314873 30959610589313133299486155)
    ·
      refine ⟨46439415883969699949229233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30959610589313133299486155 46439415883969699949229233)
      ·
        refine ⟨34829561912977274961921925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46439415883969699949229233 34829561912977274961921925)
        ·
          refine ⟨6530542858683239055360361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34829561912977274961921925 6530542858683239055360361)
          ·
            refine ⟨4897907144012429291520271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530542858683239055360361 4897907144012429291520271)
            ·
              refine ⟨7346860716018643937280407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4897907144012429291520271 7346860716018643937280407)
              ·
                refine ⟨11020291074027965905920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7346860716018643937280407 11020291074027965905920611)
                ·
                  refine ⟨16530436611041948858880917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11020291074027965905920611 16530436611041948858880917)
                  ·
                    refine ⟨774864216142591352760043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16530436611041948858880917 774864216142591352760043)
                    ·
                      rfl

theorem cell22_2263564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_2263564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263564 prefixEnd_2263564 := by exact prefixLift 2263564
  have htrace : WordTrace (prefixWord ++ tailWord_2263564) baseStart_2263564 baseEnd_2263564 := by
    simpa [prefixWord, tailWord_2263564, baseEnd_2263564] using wordTrace_append hprefix tailTrace_2263564
  have hstable : (prefixWord ++ tailWord_2263564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263564).length < 2 ^ (prefixWord ++ tailWord_2263564).sum := by decide
  have hdescent : baseEnd_2263564 < baseStart_2263564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263671 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2263671 : Nat := 118140960795 + 2263671 * 2 ^ 59
def prefixEnd_2263671 : Nat := 4983230072969 + 3 ^ 40 * 2263671 * 2
def baseEnd_2263671 : Nat := 774900844429278740334715

theorem tailTrace_2263671 : CollatzResearch.WordTrace tailWord_2263671 prefixEnd_2263671 774900844429278740334715 := by
  unfold tailWord_2263671
  simp only [CollatzResearch.WordTrace]
  refine ⟨82562864182114046072774867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55041909454742697381849911 82562864182114046072774867)
  ·
    refine ⟨123844296273171069109162301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82562864182114046072774867 123844296273171069109162301)
    ·
      refine ⟨46441611102439150915935863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123844296273171069109162301 46441611102439150915935863)
      ·
        refine ⟨69662416653658726373903795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46441611102439150915935863 69662416653658726373903795)
        ·
          refine ⟨104493624980488089560855693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69662416653658726373903795 104493624980488089560855693)
          ·
            refine ⟨39185109367683033585320885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104493624980488089560855693 39185109367683033585320885)
            ·
              refine ⟨3673604003220284398623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39185109367683033585320885 3673604003220284398623833)
              ·
                refine ⟨2755203002415213298967875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673604003220284398623833 2755203002415213298967875)
                ·
                  refine ⟨4132804503622819948451813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755203002415213298967875 4132804503622819948451813)
                  ·
                    refine ⟨774900844429278740334715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132804503622819948451813 774900844429278740334715)
                    ·
                      rfl

theorem cell22_2263671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2263671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263671 prefixEnd_2263671 := by exact prefixLift 2263671
  have htrace : WordTrace (prefixWord ++ tailWord_2263671) baseStart_2263671 baseEnd_2263671 := by
    simpa [prefixWord, tailWord_2263671, baseEnd_2263671] using wordTrace_append hprefix tailTrace_2263671
  have hstable : (prefixWord ++ tailWord_2263671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263671).length < 2 ^ (prefixWord ++ tailWord_2263671).sum := by decide
  have hdescent : baseEnd_2263671 < baseStart_2263671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263731 : List Nat := [1, 1, 1, 2, 3, 5, 3, 6]
def baseStart_2263731 : Nat := 118140960795 + 2263731 * 2 ^ 59
def prefixEnd_2263731 : Nat := 4983230072969 + 3 ^ 40 * 2263731 * 2
def baseEnd_2263731 : Nat := 86102375961717620426059

theorem tailTrace_2263731 : CollatzResearch.WordTrace tailWord_2263731 prefixEnd_2263731 86102375961717620426059 := by
  unfold tailWord_2263731
  simp only [CollatzResearch.WordTrace]
  refine ⟨82565052561896676319959047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55043368374597784213306031 82565052561896676319959047)
  ·
    refine ⟨123847578842845014479938571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82565052561896676319959047 123847578842845014479938571)
    ·
      refine ⟨185771368264267521719907857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123847578842845014479938571 185771368264267521719907857)
      ·
        refine ⟨139328526198200641289930893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185771368264267521719907857 139328526198200641289930893)
        ·
          refine ⟨52248197324325240483724085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139328526198200641289930893 52248197324325240483724085)
          ·
            refine ⟨4898268499155491295349133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52248197324325240483724085 4898268499155491295349133)
            ·
              refine ⟨1836850687183309235755925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4898268499155491295349133 1836850687183309235755925)
              ·
                refine ⟨86102375961717620426059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1836850687183309235755925 86102375961717620426059)
                ·
                  rfl

theorem cell22_2263731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 6].length) (baseStart_2263731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263731 prefixEnd_2263731 := by exact prefixLift 2263731
  have htrace : WordTrace (prefixWord ++ tailWord_2263731) baseStart_2263731 baseEnd_2263731 := by
    simpa [prefixWord, tailWord_2263731, baseEnd_2263731] using wordTrace_append hprefix tailTrace_2263731
  have hstable : (prefixWord ++ tailWord_2263731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263731).length < 2 ^ (prefixWord ++ tailWord_2263731).sum := by decide
  have hdescent : baseEnd_2263731 < baseStart_2263731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263733 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2263733 : Nat := 118140960795 + 2263733 * 2 ^ 59
def prefixEnd_2263733 : Nat := 4983230072969 + 3 ^ 40 * 2263733 * 2
def baseEnd_2263733 : Nat := 774922068296331245284525

theorem tailTrace_2263733 : CollatzResearch.WordTrace tailWord_2263733 prefixEnd_2263733 774922068296331245284525 := by
  unfold tailWord_2263733
  simp only [CollatzResearch.WordTrace]
  refine ⟨82565125507889430661531853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55043417005259620441021235 82565125507889430661531853)
  ·
    refine ⟨30961922065458536498074445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82565125507889430661531853 30961922065458536498074445)
    ·
      refine ⟨11610720774546951186777917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30961922065458536498074445 11610720774546951186777917)
      ·
        refine ⟨4354020290455106695041719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11610720774546951186777917 4354020290455106695041719)
        ·
          refine ⟨6531030435682660042562579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354020290455106695041719 6531030435682660042562579)
          ·
            refine ⟨9796545653523990063843869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531030435682660042562579 9796545653523990063843869)
            ·
              refine ⟨3673704620071496273941451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9796545653523990063843869 3673704620071496273941451)
              ·
                refine ⟨5510556930107244410912177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3673704620071496273941451 5510556930107244410912177)
                ·
                  refine ⟨4132917697580433308184133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510556930107244410912177 4132917697580433308184133)
                  ·
                    refine ⟨774922068296331245284525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132917697580433308184133 774922068296331245284525)
                    ·
                      rfl

theorem cell22_2263733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2263733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263733 prefixEnd_2263733 := by exact prefixLift 2263733
  have htrace : WordTrace (prefixWord ++ tailWord_2263733) baseStart_2263733 baseEnd_2263733 := by
    simpa [prefixWord, tailWord_2263733, baseEnd_2263733] using wordTrace_append hprefix tailTrace_2263733
  have hstable : (prefixWord ++ tailWord_2263733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263733).length < 2 ^ (prefixWord ++ tailWord_2263733).sum := by decide
  have hdescent : baseEnd_2263733 < baseStart_2263733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263840 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_2263840 : Nat := 118140960795 + 2263840 * 2 ^ 59
def prefixEnd_2263840 : Nat := 4983230072969 + 3 ^ 40 * 2263840 * 2
def baseEnd_2263840 : Nat := 774958696583018632859197

theorem tailTrace_2263840 : CollatzResearch.WordTrace tailWord_2263840 prefixEnd_2263840 774958696583018632859197 := by
  unfold tailWord_2263840
  simp only [CollatzResearch.WordTrace]
  refine ⟨41284514059250893967838487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55046018745667858623784649 41284514059250893967838487)
  ·
    refine ⟨61926771088876340951757731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41284514059250893967838487 61926771088876340951757731)
    ·
      refine ⟨92890156633314511427636597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61926771088876340951757731 92890156633314511427636597)
      ·
        refine ⟨8708452184373235446340931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92890156633314511427636597 8708452184373235446340931)
        ·
          refine ⟨13062678276559853169511397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8708452184373235446340931 13062678276559853169511397)
          ·
            refine ⟨2449252176854972469283387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13062678276559853169511397 2449252176854972469283387)
            ·
              refine ⟨3673878265282458703925081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449252176854972469283387 3673878265282458703925081)
              ·
                refine ⟨2755408698961844027943811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673878265282458703925081 2755408698961844027943811)
                ·
                  refine ⟨4133113048442766041915717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2755408698961844027943811 4133113048442766041915717)
                  ·
                    refine ⟨774958696583018632859197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133113048442766041915717 774958696583018632859197)
                    ·
                      rfl

theorem cell22_2263840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_2263840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263840 prefixEnd_2263840 := by exact prefixLift 2263840
  have htrace : WordTrace (prefixWord ++ tailWord_2263840) baseStart_2263840 baseEnd_2263840 := by
    simpa [prefixWord, tailWord_2263840, baseEnd_2263840] using wordTrace_append hprefix tailTrace_2263840
  have hstable : (prefixWord ++ tailWord_2263840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263840).length < 2 ^ (prefixWord ++ tailWord_2263840).sum := by decide
  have hdescent : baseEnd_2263840 < baseStart_2263840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263851 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_2263851 : Nat := 118140960795 + 2263851 * 2 ^ 59
def prefixEnd_2263851 : Nat := 4983230072969 + 3 ^ 40 * 2263851 * 2
def baseEnd_2263851 : Nat := 774962462107818270834163

theorem tailTrace_2263851 : CollatzResearch.WordTrace tailWord_2263851 prefixEnd_2263851 774962462107818270834163 := by
  unfold tailWord_2263851
  simp only [CollatzResearch.WordTrace]
  refine ⟨82569429321461936814327407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55046286214307957876218271 82569429321461936814327407)
  ·
    refine ⟨123854143982192905221491111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82569429321461936814327407 123854143982192905221491111)
    ·
      refine ⟨185781215973289357832236667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123854143982192905221491111 185781215973289357832236667)
      ·
        refine ⟨278671823959934036748355001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185781215973289357832236667 278671823959934036748355001)
        ·
          refine ⟨209003867969950527561266251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278671823959934036748355001 209003867969950527561266251)
          ·
            refine ⟨313505801954925791341899377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209003867969950527561266251 313505801954925791341899377)
            ·
              refine ⟨235129351466194343506424533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313505801954925791341899377 235129351466194343506424533)
              ·
                refine ⟨5510844174988929925931825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235129351466194343506424533 5510844174988929925931825)
                ·
                  refine ⟨4133133131241697444448869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5510844174988929925931825 4133133131241697444448869)
                  ·
                    refine ⟨774962462107818270834163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133133131241697444448869 774962462107818270834163)
                    ·
                      rfl

theorem cell22_2263851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_2263851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263851 prefixEnd_2263851 := by exact prefixLift 2263851
  have htrace : WordTrace (prefixWord ++ tailWord_2263851) baseStart_2263851 baseEnd_2263851 := by
    simpa [prefixWord, tailWord_2263851, baseEnd_2263851] using wordTrace_append hprefix tailTrace_2263851
  have hstable : (prefixWord ++ tailWord_2263851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263851).length < 2 ^ (prefixWord ++ tailWord_2263851).sum := by decide
  have hdescent : baseEnd_2263851 < baseStart_2263851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263866 : List Nat := [3, 1, 1, 1, 6, 10]
def baseStart_2263866 : Nat := 118140960795 + 2263866 * 2 ^ 59
def prefixEnd_2263866 : Nat := 4983230072969 + 3 ^ 40 * 2263866 * 2
def baseEnd_2263866 : Nat := 9567501196473620144557

theorem tailTrace_2263866 : CollatzResearch.WordTrace tailWord_2263866 prefixEnd_2263866 9567501196473620144557 := by
  unfold tailWord_2263866
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642494104101898594030863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55046650944271729584082301 20642494104101898594030863)
  ·
    refine ⟨30963741156152847891046295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20642494104101898594030863 30963741156152847891046295)
    ·
      refine ⟨46445611734229271836569443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30963741156152847891046295 46445611734229271836569443)
      ·
        refine ⟨69668417601343907754854165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46445611734229271836569443 69668417601343907754854165)
        ·
          refine ⟨3265707075062995676008789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69668417601343907754854165 3265707075062995676008789)
          ·
            refine ⟨9567501196473620144557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3265707075062995676008789 9567501196473620144557)
            ·
              rfl

theorem cell22_2263866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 10].length) (baseStart_2263866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263866 prefixEnd_2263866 := by exact prefixLift 2263866
  have htrace : WordTrace (prefixWord ++ tailWord_2263866) baseStart_2263866 baseEnd_2263866 := by
    simpa [prefixWord, tailWord_2263866, baseEnd_2263866] using wordTrace_append hprefix tailTrace_2263866
  have hstable : (prefixWord ++ tailWord_2263866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263866).length < 2 ^ (prefixWord ++ tailWord_2263866).sum := by decide
  have hdescent : baseEnd_2263866 < baseStart_2263866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263898 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_2263898 : Nat := 118140960795 + 2263898 * 2 ^ 59
def prefixEnd_2263898 : Nat := 4983230072969 + 3 ^ 40 * 2263898 * 2
def baseEnd_2263898 : Nat := 774978551168325814909019

theorem tailTrace_2263898 : CollatzResearch.WordTrace tailWord_2263898 prefixEnd_2263898 774978551168325814909019 := by
  unfold tailWord_2263898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642785888072915960322087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55047429034861109227525565 20642785888072915960322087)
  ·
    refine ⟨30964178832109373940483131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20642785888072915960322087 30964178832109373940483131)
    ·
      refine ⟨46446268248164060910724697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30964178832109373940483131 46446268248164060910724697)
      ·
        refine ⟨34834701186123045683043523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46446268248164060910724697 34834701186123045683043523)
        ·
          refine ⟨52252051779184568524565285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34834701186123045683043523 52252051779184568524565285)
          ·
            refine ⟨9797259708597106598355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52252051779184568524565285 9797259708597106598355991)
            ·
              refine ⟨14695889562895659897533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9797259708597106598355991 14695889562895659897533987)
              ·
                refine ⟨22043834344343489846300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14695889562895659897533987 22043834344343489846300981)
                ·
                  refine ⟨2066609469782202173090717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22043834344343489846300981 2066609469782202173090717)
                  ·
                    refine ⟨774978551168325814909019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066609469782202173090717 774978551168325814909019)
                    ·
                      rfl

theorem cell22_2263898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_2263898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263898 prefixEnd_2263898 := by exact prefixLift 2263898
  have htrace : WordTrace (prefixWord ++ tailWord_2263898) baseStart_2263898 baseEnd_2263898 := by
    simpa [prefixWord, tailWord_2263898, baseEnd_2263898] using wordTrace_append hprefix tailTrace_2263898
  have hstable : (prefixWord ++ tailWord_2263898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263898).length < 2 ^ (prefixWord ++ tailWord_2263898).sum := by decide
  have hdescent : baseEnd_2263898 < baseStart_2263898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263900 : List Nat := [2, 2, 4, 2, 1, 2, 3, 6]
def baseStart_2263900 : Nat := 118140960795 + 2263900 * 2 ^ 59
def prefixEnd_2263900 : Nat := 4983230072969 + 3 ^ 40 * 2263900 * 2
def baseEnd_2263900 : Nat := 86108803978799830706557

theorem tailTrace_2263900 : CollatzResearch.WordTrace tailWord_2263900 prefixEnd_2263900 86108803978799830706557 := by
  unfold tailWord_2263900
  simp only [CollatzResearch.WordTrace]
  refine ⟨41285608249142209091430577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55047477665522945455240769 41285608249142209091430577)
  ·
    refine ⟨30964206186856656818572933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41285608249142209091430577 30964206186856656818572933)
    ·
      refine ⟨5805788660035623153482425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30964206186856656818572933 5805788660035623153482425)
      ·
        refine ⟨4354341495026717365111819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5805788660035623153482425 4354341495026717365111819)
        ·
          refine ⟨6531512242540076047667729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354341495026717365111819 6531512242540076047667729)
          ·
            refine ⟨4898634181905057035750797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531512242540076047667729 4898634181905057035750797)
            ·
              refine ⟨1836987818214396388406549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4898634181905057035750797 1836987818214396388406549)
              ·
                refine ⟨86108803978799830706557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1836987818214396388406549 86108803978799830706557)
                ·
                  rfl

theorem cell22_2263900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_2263900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263900 prefixEnd_2263900 := by exact prefixLift 2263900
  have htrace : WordTrace (prefixWord ++ tailWord_2263900) baseStart_2263900 baseEnd_2263900 := by
    simpa [prefixWord, tailWord_2263900, baseEnd_2263900] using wordTrace_append hprefix tailTrace_2263900
  have hstable : (prefixWord ++ tailWord_2263900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263900).length < 2 ^ (prefixWord ++ tailWord_2263900).sum := by decide
  have hdescent : baseEnd_2263900 < baseStart_2263900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263915 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 1, 3]
def baseStart_2263915 : Nat := 118140960795 + 2263915 * 2 ^ 59
def prefixEnd_2263915 : Nat := 4983230072969 + 3 ^ 40 * 2263915 * 2
def baseEnd_2263915 : Nat := 774984370615743437233967

theorem tailTrace_2263915 : CollatzResearch.WordTrace tailWord_2263915 prefixEnd_2263915 774984370615743437233967 := by
  unfold tailWord_2263915
  simp only [CollatzResearch.WordTrace]
  refine ⟨82571763593230075744657199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55047842395486717163104799 82571763593230075744657199)
  ·
    refine ⟨123857645389845113616985799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82571763593230075744657199 123857645389845113616985799)
    ·
      refine ⟨185786468084767670425478699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123857645389845113616985799 185786468084767670425478699)
      ·
        refine ⟨278679702127151505638218049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185786468084767670425478699 278679702127151505638218049)
        ·
          refine ⟨209009776595363629228663537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278679702127151505638218049 209009776595363629228663537)
          ·
            refine ⟨156757332446522721921497653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209009776595363629228663537 156757332446522721921497653)
            ·
              refine ⟨14695999916861505180140405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156757332446522721921497653 14695999916861505180140405)
              ·
                refine ⟨1377749992205766110638163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14695999916861505180140405 1377749992205766110638163)
                ·
                  refine ⟨2066624988308649165957245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1377749992205766110638163 2066624988308649165957245)
                  ·
                    refine ⟨774984370615743437233967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066624988308649165957245 774984370615743437233967)
                    ·
                      rfl

theorem cell22_2263915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 3].length) (baseStart_2263915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263915 prefixEnd_2263915 := by exact prefixLift 2263915
  have htrace : WordTrace (prefixWord ++ tailWord_2263915) baseStart_2263915 baseEnd_2263915 := by
    simpa [prefixWord, tailWord_2263915, baseEnd_2263915] using wordTrace_append hprefix tailTrace_2263915
  have hstable : (prefixWord ++ tailWord_2263915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263915).length < 2 ^ (prefixWord ++ tailWord_2263915).sum := by decide
  have hdescent : baseEnd_2263915 < baseStart_2263915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263943 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2263943 : Nat := 118140960795 + 2263943 * 2 ^ 59
def prefixEnd_2263943 : Nat := 4983230072969 + 3 ^ 40 * 2263943 * 2
def baseEnd_2263943 : Nat := 774993955587960697533881

theorem tailTrace_2263943 : CollatzResearch.WordTrace tailWord_2263943 prefixEnd_2263943 774993955587960697533881 := by
  unfold tailWord_2263943
  simp only [CollatzResearch.WordTrace]
  refine ⟨82572784837128636526676483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55048523224752424351117655 82572784837128636526676483)
  ·
    refine ⟨123859177255692954790014725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82572784837128636526676483 123859177255692954790014725)
    ·
      refine ⟨23223595735442429023127761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123859177255692954790014725 23223595735442429023127761)
      ·
        refine ⟨17417696801581821767345821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23223595735442429023127761 17417696801581821767345821)
        ·
          refine ⟨6531636300593183162754683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17417696801581821767345821 6531636300593183162754683)
          ·
            refine ⟨9797454450889774744132025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6531636300593183162754683 9797454450889774744132025)
            ·
              refine ⟨7348090838167331058099019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9797454450889774744132025 7348090838167331058099019)
              ·
                refine ⟨11022136257250996587148529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7348090838167331058099019 11022136257250996587148529)
                ·
                  refine ⟨8266602192938247440361397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11022136257250996587148529 8266602192938247440361397)
                  ·
                    refine ⟨774993955587960697533881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8266602192938247440361397 774993955587960697533881)
                    ·
                      rfl

theorem cell22_2263943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2263943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263943 prefixEnd_2263943 := by exact prefixLift 2263943
  have htrace : WordTrace (prefixWord ++ tailWord_2263943) baseStart_2263943 baseEnd_2263943 := by
    simpa [prefixWord, tailWord_2263943, baseEnd_2263943] using wordTrace_append hprefix tailTrace_2263943
  have hstable : (prefixWord ++ tailWord_2263943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263943).length < 2 ^ (prefixWord ++ tailWord_2263943).sum := by decide
  have hdescent : baseEnd_2263943 < baseStart_2263943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2263945 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 5]
def baseStart_2263945 : Nat := 118140960795 + 2263945 * 2 ^ 59
def prefixEnd_2263945 : Nat := 4983230072969 + 3 ^ 40 * 2263945 * 2
def baseEnd_2263945 : Nat := 258331546742944452994625

theorem tailTrace_2263945 : CollatzResearch.WordTrace tailWord_2263945 prefixEnd_2263945 258331546742944452994625 := by
  unfold tailWord_2263945
  simp only [CollatzResearch.WordTrace]
  refine ⟨82572857783121390868249289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55048571855414260578832859 82572857783121390868249289)
  ·
    refine ⟨61929643337341043151186967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82572857783121390868249289 61929643337341043151186967)
    ·
      refine ⟨92894465006011564726780451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61929643337341043151186967 92894465006011564726780451)
      ·
        refine ⟨139341697509017347090170677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92894465006011564726780451 139341697509017347090170677)
        ·
          refine ⟨13063284141470376289703501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139341697509017347090170677 13063284141470376289703501)
          ·
            refine ⟨4898731553051391108638813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13063284141470376289703501 4898731553051391108638813)
            ·
              refine ⟨1837024332394271665739555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4898731553051391108638813 1837024332394271665739555)
              ·
                refine ⟨2755536498591407498609333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837024332394271665739555 2755536498591407498609333)
                ·
                  refine ⟨258331546742944452994625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755536498591407498609333 258331546742944452994625)
                  ·
                    rfl

theorem cell22_2263945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_2263945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2263945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2263945 prefixEnd_2263945 := by exact prefixLift 2263945
  have htrace : WordTrace (prefixWord ++ tailWord_2263945) baseStart_2263945 baseEnd_2263945 := by
    simpa [prefixWord, tailWord_2263945, baseEnd_2263945] using wordTrace_append hprefix tailTrace_2263945
  have hstable : (prefixWord ++ tailWord_2263945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2263945).length < 2 ^ (prefixWord ++ tailWord_2263945).sum := by decide
  have hdescent : baseEnd_2263945 < baseStart_2263945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2263945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264020 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2264020 : Nat := 118140960795 + 2264020 * 2 ^ 59
def prefixEnd_2264020 : Nat := 4983230072969 + 3 ^ 40 * 2264020 * 2
def baseEnd_2264020 : Nat := 775020314261558163358645

theorem tailTrace_2264020 : CollatzResearch.WordTrace tailWord_2264020 prefixEnd_2264020 775020314261558163358645 := by
  unfold tailWord_2264020
  simp only [CollatzResearch.WordTrace]
  refine ⟨41287796628924839338614757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55050395505233119118153009 41287796628924839338614757)
  ·
    refine ⟨7741461867923407375990267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41287796628924839338614757 7741461867923407375990267)
    ·
      refine ⟨11612192801885111063985401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7741461867923407375990267 11612192801885111063985401)
      ·
        refine ⟨8709144601413833297989051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11612192801885111063985401 8709144601413833297989051)
        ·
          refine ⟨13063716902120749946983577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709144601413833297989051 13063716902120749946983577)
          ·
            refine ⟨9797787676590562460237683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13063716902120749946983577 9797787676590562460237683)
            ·
              refine ⟨14696681514885843690356525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9797787676590562460237683 14696681514885843690356525)
              ·
                refine ⟨5511255568082191383883697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14696681514885843690356525 5511255568082191383883697)
                ·
                  refine ⟨4133441676061643537912773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511255568082191383883697 4133441676061643537912773)
                  ·
                    refine ⟨775020314261558163358645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133441676061643537912773 775020314261558163358645)
                    ·
                      rfl

theorem cell22_2264020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2264020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264020 prefixEnd_2264020 := by exact prefixLift 2264020
  have htrace : WordTrace (prefixWord ++ tailWord_2264020) baseStart_2264020 baseEnd_2264020 := by
    simpa [prefixWord, tailWord_2264020, baseEnd_2264020] using wordTrace_append hprefix tailTrace_2264020
  have hstable : (prefixWord ++ tailWord_2264020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264020).length < 2 ^ (prefixWord ++ tailWord_2264020).sum := by decide
  have hdescent : baseEnd_2264020 < baseStart_2264020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264022 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2264022 : Nat := 118140960795 + 2264022 * 2 ^ 59
def prefixEnd_2264022 : Nat := 4983230072969 + 3 ^ 40 * 2264022 * 2
def baseEnd_2264022 : Nat := 775020998902430824808639

theorem tailTrace_2264022 : CollatzResearch.WordTrace tailWord_2264022 prefixEnd_2264022 775020998902430824808639 := by
  unfold tailWord_2264022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160979137740152063675145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55050444135894955345868213 5160979137740152063675145)
  ·
    refine ⟨3870734353305114047756359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5160979137740152063675145 3870734353305114047756359)
    ·
      refine ⟨5806101529957671071634539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3870734353305114047756359 5806101529957671071634539)
      ·
        refine ⟨8709152294936506607451809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806101529957671071634539 8709152294936506607451809)
        ·
          refine ⟨6531864221202379955588857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8709152294936506607451809 6531864221202379955588857)
          ·
            refine ⟨4898898165901784966691643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531864221202379955588857 4898898165901784966691643)
            ·
              refine ⟨7348347248852677450037465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898898165901784966691643 7348347248852677450037465)
              ·
                refine ⟨5511260436639508087528099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7348347248852677450037465 5511260436639508087528099)
                ·
                  refine ⟨8266890654959262131292149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511260436639508087528099 8266890654959262131292149)
                  ·
                    refine ⟨775020998902430824808639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8266890654959262131292149 775020998902430824808639)
                    ·
                      rfl

theorem cell22_2264022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2264022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264022 prefixEnd_2264022 := by exact prefixLift 2264022
  have htrace : WordTrace (prefixWord ++ tailWord_2264022) baseStart_2264022 baseEnd_2264022 := by
    simpa [prefixWord, tailWord_2264022, baseEnd_2264022] using wordTrace_append hprefix tailTrace_2264022
  have hstable : (prefixWord ++ tailWord_2264022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264022).length < 2 ^ (prefixWord ++ tailWord_2264022).sum := by decide
  have hdescent : baseEnd_2264022 < baseStart_2264022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264097 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 5]
def baseStart_2264097 : Nat := 118140960795 + 2264097 * 2 ^ 59
def prefixEnd_2264097 : Nat := 4983230072969 + 3 ^ 40 * 2264097 * 2
def baseEnd_2264097 : Nat := 258348890978385209727803

theorem tailTrace_2264097 : CollatzResearch.WordTrace tailWord_2264097 prefixEnd_2264097 258348890978385209727803 := by
  unfold tailWord_2264097
  simp only [CollatzResearch.WordTrace]
  refine ⟨82578401678570720827782545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55052267785713813885188363 82578401678570720827782545)
  ·
    refine ⟨61933801258928040620836909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82578401678570720827782545 61933801258928040620836909)
    ·
      refine ⟨23225175472098015232813841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61933801258928040620836909 23225175472098015232813841)
      ·
        refine ⟨17418881604073511424610381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23225175472098015232813841 17418881604073511424610381)
        ·
          refine ⟨6532080601527566784228893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17418881604073511424610381 6532080601527566784228893)
          ·
            refine ⟨2449530225572837544085835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6532080601527566784228893 2449530225572837544085835)
            ·
              refine ⟨3674295338359256316128753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449530225572837544085835 3674295338359256316128753)
              ·
                refine ⟨2755721503769442237096565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3674295338359256316128753 2755721503769442237096565)
                ·
                  refine ⟨258348890978385209727803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2755721503769442237096565 258348890978385209727803)
                  ·
                    rfl

theorem cell22_2264097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_2264097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264097 prefixEnd_2264097 := by exact prefixLift 2264097
  have htrace : WordTrace (prefixWord ++ tailWord_2264097) baseStart_2264097 baseEnd_2264097 := by
    simpa [prefixWord, tailWord_2264097, baseEnd_2264097] using wordTrace_append hprefix tailTrace_2264097
  have hstable : (prefixWord ++ tailWord_2264097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264097).length < 2 ^ (prefixWord ++ tailWord_2264097).sum := by decide
  have hdescent : baseEnd_2264097 < baseStart_2264097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264125 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2264125 : Nat := 118140960795 + 2264125 * 2 ^ 59
def prefixEnd_2264125 : Nat := 4983230072969 + 3 ^ 40 * 2264125 * 2
def baseEnd_2264125 : Nat := 258352085969124296494441

theorem tailTrace_2264125 : CollatzResearch.WordTrace tailWord_2264125 prefixEnd_2264125 258352085969124296494441 := by
  unfold tailWord_2264125
  simp only [CollatzResearch.WordTrace]
  refine ⟨82579422922469281609801829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55052948614979521073201219 82579422922469281609801829)
  ·
    refine ⟨15483641797962990301837843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82579422922469281609801829 15483641797962990301837843)
    ·
      refine ⟨23225462696944485452756765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15483641797962990301837843 23225462696944485452756765)
      ·
        refine ⟨8709548511354182044783787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23225462696944485452756765 8709548511354182044783787)
        ·
          refine ⟨13064322767031273067175681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709548511354182044783787 13064322767031273067175681)
          ·
            refine ⟨9798242075273454800381761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064322767031273067175681 9798242075273454800381761)
            ·
              refine ⟨7348681556455091100286321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9798242075273454800381761 7348681556455091100286321)
              ·
                refine ⟨5511511167341318325214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7348681556455091100286321 5511511167341318325214741)
                ·
                  refine ⟨258352085969124296494441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5511511167341318325214741 258352085969124296494441)
                  ·
                    rfl

theorem cell22_2264125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2264125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264125 prefixEnd_2264125 := by exact prefixLift 2264125
  have htrace : WordTrace (prefixWord ++ tailWord_2264125) baseStart_2264125 baseEnd_2264125 := by
    simpa [prefixWord, tailWord_2264125, baseEnd_2264125] using wordTrace_append hprefix tailTrace_2264125
  have hstable : (prefixWord ++ tailWord_2264125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264125).length < 2 ^ (prefixWord ++ tailWord_2264125).sum := by decide
  have hdescent : baseEnd_2264125 < baseStart_2264125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264170 : List Nat := [3, 1, 3, 2, 2, 1, 1, 9]
def baseStart_2264170 : Nat := 118140960795 + 2264170 * 2 ^ 59
def prefixEnd_2264170 : Nat := 4983230072969 + 3 ^ 40 * 2264170 * 2
def baseEnd_2264170 : Nat := 86119073591889752456465

theorem tailTrace_2264170 : CollatzResearch.WordTrace tailWord_2264170 prefixEnd_2264170 86119073591889752456465 := by
  unfold tailWord_2264170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645266051826563573797491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55054042804870836196793309 20645266051826563573797491)
  ·
    refine ⟨30967899077739845360696237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20645266051826563573797491 30967899077739845360696237)
    ·
      refine ⟨11612962154152442010261089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30967899077739845360696237 11612962154152442010261089)
      ·
        refine ⟨8709721615614331507695817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11612962154152442010261089 8709721615614331507695817)
        ·
          refine ⟨6532291211710748630771863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8709721615614331507695817 6532291211710748630771863)
          ·
            refine ⟨9798436817566122946157795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6532291211710748630771863 9798436817566122946157795)
            ·
              refine ⟨14697655226349184419236693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9798436817566122946157795 14697655226349184419236693)
              ·
                refine ⟨86119073591889752456465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14697655226349184419236693 86119073591889752456465)
                ·
                  rfl

theorem cell22_2264170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_2264170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264170 prefixEnd_2264170 := by exact prefixLift 2264170
  have htrace : WordTrace (prefixWord ++ tailWord_2264170) baseStart_2264170 baseEnd_2264170 := by
    simpa [prefixWord, tailWord_2264170, baseEnd_2264170] using wordTrace_append hprefix tailTrace_2264170
  have hstable : (prefixWord ++ tailWord_2264170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264170).length < 2 ^ (prefixWord ++ tailWord_2264170).sum := by decide
  have hdescent : baseEnd_2264170 < baseStart_2264170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264174 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2264174 : Nat := 118140960795 + 2264174 * 2 ^ 59
def prefixEnd_2264174 : Nat := 4983230072969 + 3 ^ 40 * 2264174 * 2
def baseEnd_2264174 : Nat := 775073031608753095008173

theorem tailTrace_2264174 : CollatzResearch.WordTrace tailWord_2264174 prefixEnd_2264174 775073031608753095008173 := by
  unfold tailWord_2264174
  simp only [CollatzResearch.WordTrace]
  refine ⟨10322651262411470372291947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55054140066194508652223717 10322651262411470372291947)
  ·
    refine ⟨15483976893617205558437921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10322651262411470372291947 15483976893617205558437921)
    ·
      refine ⟨11612982670212904168828441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15483976893617205558437921 11612982670212904168828441)
      ·
        refine ⟨8709737002659678126621331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11612982670212904168828441 8709737002659678126621331)
        ·
          refine ⟨13064605503989517189931997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8709737002659678126621331 13064605503989517189931997)
          ·
            refine ⟨4899227063996068946224499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13064605503989517189931997 4899227063996068946224499)
            ·
              refine ⟨7348840595994103419336749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899227063996068946224499 7348840595994103419336749)
              ·
                refine ⟨2755815223497788782251281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7348840595994103419336749 2755815223497788782251281)
                ·
                  refine ⟨2066861417623341586688461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755815223497788782251281 2066861417623341586688461)
                  ·
                    refine ⟨775073031608753095008173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2066861417623341586688461 775073031608753095008173)
                    ·
                      rfl

theorem cell22_2264174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2264174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264174 prefixEnd_2264174 := by exact prefixLift 2264174
  have htrace : WordTrace (prefixWord ++ tailWord_2264174) baseStart_2264174 baseEnd_2264174 := by
    simpa [prefixWord, tailWord_2264174, baseEnd_2264174] using wordTrace_append hprefix tailTrace_2264174
  have hstable : (prefixWord ++ tailWord_2264174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264174).length < 2 ^ (prefixWord ++ tailWord_2264174).sum := by decide
  have hdescent : baseEnd_2264174 < baseStart_2264174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264277 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2264277 : Nat := 118140960795 + 2264277 * 2 ^ 59
def prefixEnd_2264277 : Nat := 4983230072969 + 3 ^ 40 * 2264277 * 2
def baseEnd_2264277 : Nat := 258369430204565053227619

theorem tailTrace_2264277 : CollatzResearch.WordTrace tailWord_2264277 prefixEnd_2264277 258369430204565053227619 := by
  unfold tailWord_2264277
  simp only [CollatzResearch.WordTrace]
  refine ⟨82584966817918611569335085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55056644545279074379556723 82584966817918611569335085)
  ·
    refine ⟨30969362556719479338500657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82584966817918611569335085 30969362556719479338500657)
    ·
      refine ⟨23227021917539609503875493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30969362556719479338500657 23227021917539609503875493)
      ·
        refine ⟨4355066609538676781976655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23227021917539609503875493 4355066609538676781976655)
        ·
          refine ⟨6532599914308015172964983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355066609538676781976655 6532599914308015172964983)
          ·
            refine ⟨9798899871462022759447475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6532599914308015172964983 9798899871462022759447475)
            ·
              refine ⟨14698349807193034139171213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9798899871462022759447475 14698349807193034139171213)
              ·
                refine ⟨5511881177697387802189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14698349807193034139171213 5511881177697387802189205)
                ·
                  refine ⟨258369430204565053227619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5511881177697387802189205 258369430204565053227619)
                  ·
                    rfl

theorem cell22_2264277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2264277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264277 prefixEnd_2264277 := by exact prefixLift 2264277
  have htrace : WordTrace (prefixWord ++ tailWord_2264277) baseStart_2264277 baseEnd_2264277 := by
    simpa [prefixWord, tailWord_2264277, baseEnd_2264277] using wordTrace_append hprefix tailTrace_2264277
  have hstable : (prefixWord ++ tailWord_2264277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264277).length < 2 ^ (prefixWord ++ tailWord_2264277).sum := by decide
  have hdescent : baseEnd_2264277 < baseStart_2264277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264292 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2264292 : Nat := 118140960795 + 2264292 * 2 ^ 59
def prefixEnd_2264292 : Nat := 4983230072969 + 3 ^ 40 * 2264292 * 2
def baseEnd_2264292 : Nat := 775113425420240120557811

theorem tailTrace_2264292 : CollatzResearch.WordTrace tailWord_2264292 prefixEnd_2264292 775113425420240120557811 := by
  unfold tailWord_2264292
  simp only [CollatzResearch.WordTrace]
  refine ⟨41292756956432134565565565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55057009275242846087420753 41292756956432134565565565)
  ·
    refine ⟨15484783858662050462087087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41292756956432134565565565 15484783858662050462087087)
    ·
      refine ⟨23227175787993075693130631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15484783858662050462087087 23227175787993075693130631)
      ·
        refine ⟨34840763681989613539695947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23227175787993075693130631 34840763681989613539695947)
        ·
          refine ⟨52261145522984420309543921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34840763681989613539695947 52261145522984420309543921)
          ·
            refine ⟨39195859142238315232157941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52261145522984420309543921 39195859142238315232157941)
            ·
              refine ⟨3674611794584842053014807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39195859142238315232157941 3674611794584842053014807)
              ·
                refine ⟨5511917691877263079522211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674611794584842053014807 5511917691877263079522211)
                ·
                  refine ⟨8267876537815894619283317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5511917691877263079522211 8267876537815894619283317)
                  ·
                    refine ⟨775113425420240120557811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8267876537815894619283317 775113425420240120557811)
                    ·
                      rfl

theorem cell22_2264292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2264292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264292 prefixEnd_2264292 := by exact prefixLift 2264292
  have htrace : WordTrace (prefixWord ++ tailWord_2264292) baseStart_2264292 baseEnd_2264292 := by
    simpa [prefixWord, tailWord_2264292, baseEnd_2264292] using wordTrace_append hprefix tailTrace_2264292
  have hstable : (prefixWord ++ tailWord_2264292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264292).length < 2 ^ (prefixWord ++ tailWord_2264292).sum := by decide
  have hdescent : baseEnd_2264292 < baseStart_2264292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264324 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2264324 : Nat := 118140960795 + 2264324 * 2 ^ 59
def prefixEnd_2264324 : Nat := 4983230072969 + 3 ^ 40 * 2264324 * 2
def baseEnd_2264324 : Nat := 775124379674202703757713

theorem tailTrace_2264324 : CollatzResearch.WordTrace tailWord_2264324 prefixEnd_2264324 775124379674202703757713 := by
  unfold tailWord_2264324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41293340524374169298148013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55057787365832225730864017 41293340524374169298148013)
  ·
    refine ⟨15485002696640313486805505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41293340524374169298148013 15485002696640313486805505)
    ·
      refine ⟨11613752022480235115104129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15485002696640313486805505 11613752022480235115104129)
      ·
        refine ⟨8710314016860176336328097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11613752022480235115104129 8710314016860176336328097)
        ·
          refine ⟨6532735512645132252246073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8710314016860176336328097 6532735512645132252246073)
          ·
            refine ⟨4899551634483849189184555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532735512645132252246073 4899551634483849189184555)
            ·
              refine ⟨7349327451725773783776833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899551634483849189184555 7349327451725773783776833)
              ·
                refine ⟨5511995588794330337832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7349327451725773783776833 5511995588794330337832625)
                ·
                  refine ⟨4133996691595747753374469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5511995588794330337832625 4133996691595747753374469)
                  ·
                    refine ⟨775124379674202703757713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133996691595747753374469 775124379674202703757713)
                    ·
                      rfl

theorem cell22_2264324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2264324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264324 prefixEnd_2264324 := by exact prefixLift 2264324
  have htrace : WordTrace (prefixWord ++ tailWord_2264324) baseStart_2264324 baseEnd_2264324 := by
    simpa [prefixWord, tailWord_2264324, baseEnd_2264324] using wordTrace_append hprefix tailTrace_2264324
  have hstable : (prefixWord ++ tailWord_2264324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264324).length < 2 ^ (prefixWord ++ tailWord_2264324).sum := by decide
  have hdescent : baseEnd_2264324 < baseStart_2264324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264390 : List Nat := [6, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2264390 : Nat := 118140960795 + 2264390 * 2 ^ 59
def prefixEnd_2264390 : Nat := 4983230072969 + 3 ^ 40 * 2264390 * 2
def baseEnd_2264390 : Nat := 86127441424777836845279

theorem tailTrace_2264390 : CollatzResearch.WordTrace tailWord_2264390 prefixEnd_2264390 86127441424777836845279 := by
  unfold tailWord_2264390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580909008328413495881207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55059392177672821245465749 2580909008328413495881207)
  ·
    refine ⟨3871363512492620243821811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2580909008328413495881207 3871363512492620243821811)
    ·
      refine ⟨5807045268738930365732717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871363512492620243821811 5807045268738930365732717)
      ·
        refine ⟨2177641975777098887149769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5807045268738930365732717 2177641975777098887149769)
        ·
          refine ⟨1633231481832824165362327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2177641975777098887149769 1633231481832824165362327)
          ·
            refine ⟨2449847222749236248043491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633231481832824165362327 2449847222749236248043491)
            ·
              refine ⟨3674770834123854372065237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449847222749236248043491 3674770834123854372065237)
              ·
                refine ⟨86127441424777836845279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3674770834123854372065237 86127441424777836845279)
                ·
                  rfl

theorem cell22_2264390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2264390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264390 prefixEnd_2264390 := by exact prefixLift 2264390
  have htrace : WordTrace (prefixWord ++ tailWord_2264390) baseStart_2264390 baseEnd_2264390 := by
    simpa [prefixWord, tailWord_2264390, baseEnd_2264390] using wordTrace_append hprefix tailTrace_2264390
  have hstable : (prefixWord ++ tailWord_2264390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264390).length < 2 ^ (prefixWord ++ tailWord_2264390).sum := by decide
  have hdescent : baseEnd_2264390 < baseStart_2264390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264444 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_2264444 : Nat := 118140960795 + 2264444 * 2 ^ 59
def prefixEnd_2264444 : Nat := 4983230072969 + 3 ^ 40 * 2264444 * 2
def baseEnd_2264444 : Nat := 775165458126562390757345

theorem tailTrace_2264444 : CollatzResearch.WordTrace tailWord_2264444 prefixEnd_2264444 775165458126562390757345 := by
  unfold tailWord_2264444
  simp only [CollatzResearch.WordTrace]
  refine ⟨41295528904156799545332193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55060705205542399393776257 41295528904156799545332193)
  ·
    refine ⟨30971646678117599658999145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41295528904156799545332193 30971646678117599658999145)
    ·
      refine ⟨23228735008588199744249359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30971646678117599658999145 23228735008588199744249359)
      ·
        refine ⟨34843102512882299616374039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23228735008588199744249359 34843102512882299616374039)
        ·
          refine ⟨52264653769323449424561059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34843102512882299616374039 52264653769323449424561059)
          ·
            refine ⟨78396980653985174136841589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52264653769323449424561059 78396980653985174136841589)
            ·
              refine ⟨7349716936311110075328899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78396980653985174136841589 7349716936311110075328899)
              ·
                refine ⟨11024575404466665112993349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349716936311110075328899 11024575404466665112993349)
                ·
                  refine ⟨2067107888337499708686253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11024575404466665112993349 2067107888337499708686253)
                  ·
                    refine ⟨775165458126562390757345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067107888337499708686253 775165458126562390757345)
                    ·
                      rfl

theorem cell22_2264444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_2264444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264444 prefixEnd_2264444 := by exact prefixLift 2264444
  have htrace : WordTrace (prefixWord ++ tailWord_2264444) baseStart_2264444 baseEnd_2264444 := by
    simpa [prefixWord, tailWord_2264444, baseEnd_2264444] using wordTrace_append hprefix tailTrace_2264444
  have hstable : (prefixWord ++ tailWord_2264444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264444).length < 2 ^ (prefixWord ++ tailWord_2264444).sum := by decide
  have hdescent : baseEnd_2264444 < baseStart_2264444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264519 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 5]
def baseStart_2264519 : Nat := 118140960795 + 2264519 * 2 ^ 59
def prefixEnd_2264519 : Nat := 4983230072969 + 3 ^ 40 * 2264519 * 2
def baseEnd_2264519 : Nat := 258397044053095731710705

theorem tailTrace_2264519 : CollatzResearch.WordTrace tailWord_2264519 prefixEnd_2264519 258397044053095731710705 := by
  unfold tailWord_2264519
  simp only [CollatzResearch.WordTrace]
  refine ⟨82593793283041886899644611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55062528855361257933096407 82593793283041886899644611)
  ·
    refine ⟨123890689924562830349466917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82593793283041886899644611 123890689924562830349466917)
    ·
      refine ⟨23229504360855530690525047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123890689924562830349466917 23229504360855530690525047)
      ·
        refine ⟨34844256541283296035787571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23229504360855530690525047 34844256541283296035787571)
        ·
          refine ⟨52266384811924944053681357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34844256541283296035787571 52266384811924944053681357)
          ·
            refine ⟨19599894304471854020130509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52266384811924944053681357 19599894304471854020130509)
            ·
              refine ⟨7349960364176945257548941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19599894304471854020130509 7349960364176945257548941)
              ·
                refine ⟨2756235136566354471580853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7349960364176945257548941 2756235136566354471580853)
                ·
                  refine ⟨258397044053095731710705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756235136566354471580853 258397044053095731710705)
                  ·
                    rfl

theorem cell22_2264519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 5].length) (baseStart_2264519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264519 prefixEnd_2264519 := by exact prefixLift 2264519
  have htrace : WordTrace (prefixWord ++ tailWord_2264519) baseStart_2264519 baseEnd_2264519 := by
    simpa [prefixWord, tailWord_2264519, baseEnd_2264519] using wordTrace_append hprefix tailTrace_2264519
  have hstable : (prefixWord ++ tailWord_2264519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264519).length < 2 ^ (prefixWord ++ tailWord_2264519).sum := by decide
  have hdescent : baseEnd_2264519 < baseStart_2264519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264566 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2264566 : Nat := 118140960795 + 2264566 * 2 ^ 59
def prefixEnd_2264566 : Nat := 4983230072969 + 3 ^ 40 * 2264566 * 2
def baseEnd_2264566 : Nat := 775207221219794739206971

theorem tailTrace_2264566 : CollatzResearch.WordTrace tailWord_2264566 prefixEnd_2264566 775207221219794739206971 := by
  unfold tailWord_2264566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162219219616975870412847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55063671675914409284403701 5162219219616975870412847)
  ·
    refine ⟨7743328829425463805619271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162219219616975870412847 7743328829425463805619271)
    ·
      refine ⟨11614993244138195708428907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7743328829425463805619271 11614993244138195708428907)
      ·
        refine ⟨17422489866207293562643361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11614993244138195708428907 17422489866207293562643361)
        ·
          refine ⟨13066867399655470171982521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17422489866207293562643361 13066867399655470171982521)
          ·
            refine ⟨9800150549741602628986891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13066867399655470171982521 9800150549741602628986891)
            ·
              refine ⟨14700225824612403943480337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800150549741602628986891 14700225824612403943480337)
              ·
                refine ⟨11025169368459302957610253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14700225824612403943480337 11025169368459302957610253)
                ·
                  refine ⟨4134438513172238609103845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11025169368459302957610253 4134438513172238609103845)
                  ·
                    refine ⟨775207221219794739206971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134438513172238609103845 775207221219794739206971)
                    ·
                      rfl

theorem cell22_2264566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2264566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264566 prefixEnd_2264566 := by exact prefixLift 2264566
  have htrace : WordTrace (prefixWord ++ tailWord_2264566) baseStart_2264566 baseEnd_2264566 := by
    simpa [prefixWord, tailWord_2264566, baseEnd_2264566] using wordTrace_append hprefix tailTrace_2264566
  have hstable : (prefixWord ++ tailWord_2264566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264566).length < 2 ^ (prefixWord ++ tailWord_2264566).sum := by decide
  have hdescent : baseEnd_2264566 < baseStart_2264566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264600 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_2264600 : Nat := 118140960795 + 2264600 * 2 ^ 59
def prefixEnd_2264600 : Nat := 4983230072969 + 3 ^ 40 * 2264600 * 2
def baseEnd_2264600 : Nat := 775218860114629983856867

theorem tailTrace_2264600 : CollatzResearch.WordTrace tailWord_2264600 prefixEnd_2264600 775218860114629983856867 := by
  unfold tailWord_2264600
  simp only [CollatzResearch.WordTrace]
  refine ⟨41298373797874218866671627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55064498397165625155562169 41298373797874218866671627)
  ·
    refine ⟨61947560696811328300007441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41298373797874218866671627 61947560696811328300007441)
    ·
      refine ⟨46460670522608496225005581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61947560696811328300007441 46460670522608496225005581)
      ·
        refine ⟨17422751445978186084377093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46460670522608496225005581 17422751445978186084377093)
        ·
          refine ⟨3266765896120909890820705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17422751445978186084377093 3266765896120909890820705)
          ·
            refine ⟨2450074422090682418115529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266765896120909890820705 2450074422090682418115529)
            ·
              refine ⟨1837555816568011813586647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2450074422090682418115529 1837555816568011813586647)
              ·
                refine ⟨2756333724852017720379971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837555816568011813586647 2756333724852017720379971)
                ·
                  refine ⟨4134500587278026580569957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756333724852017720379971 4134500587278026580569957)
                  ·
                    refine ⟨775218860114629983856867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134500587278026580569957 775218860114629983856867)
                    ·
                      rfl

theorem cell22_2264600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_2264600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264600 prefixEnd_2264600 := by exact prefixLift 2264600
  have htrace : WordTrace (prefixWord ++ tailWord_2264600) baseStart_2264600 baseEnd_2264600 := by
    simpa [prefixWord, tailWord_2264600, baseEnd_2264600] using wordTrace_append hprefix tailTrace_2264600
  have hstable : (prefixWord ++ tailWord_2264600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264600).length < 2 ^ (prefixWord ++ tailWord_2264600).sum := by decide
  have hdescent : baseEnd_2264600 < baseStart_2264600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264609 : List Nat := [1, 2, 3, 2, 2, 3, 9]
def baseStart_2264609 : Nat := 118140960795 + 2264609 * 2 ^ 59
def prefixEnd_2264609 : Nat := 4983230072969 + 3 ^ 40 * 2264609 * 2
def baseEnd_2264609 : Nat := 28711923740687294828957

theorem tailTrace_2264609 : CollatzResearch.WordTrace tailWord_2264609 prefixEnd_2264609 28711923740687294828957 := by
  unfold tailWord_2264609
  simp only [CollatzResearch.WordTrace]
  refine ⟨82597075852715832270420881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55064717235143888180280587 82597075852715832270420881)
  ·
    refine ⟨61947806889536874202815661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82597075852715832270420881 61947806889536874202815661)
    ·
      refine ⟨23230427583576327826055873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61947806889536874202815661 23230427583576327826055873)
      ·
        refine ⟨17422820687682245869541905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23230427583576327826055873 17422820687682245869541905)
        ·
          refine ⟨13067115515761684402156429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17422820687682245869541905 13067115515761684402156429)
          ·
            refine ⟨4900168318410631650808661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13067115515761684402156429 4900168318410631650808661)
            ·
              refine ⟨28711923740687294828957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4900168318410631650808661 28711923740687294828957)
              ·
                rfl

theorem cell22_2264609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 9].length) (baseStart_2264609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264609 prefixEnd_2264609 := by exact prefixLift 2264609
  have htrace : WordTrace (prefixWord ++ tailWord_2264609) baseStart_2264609 baseEnd_2264609 := by
    simpa [prefixWord, tailWord_2264609, baseEnd_2264609] using wordTrace_append hprefix tailTrace_2264609
  have hstable : (prefixWord ++ tailWord_2264609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264609).length < 2 ^ (prefixWord ++ tailWord_2264609).sum := by decide
  have hdescent : baseEnd_2264609 < baseStart_2264609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264630 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2264630 : Nat := 118140960795 + 2264630 * 2 ^ 59
def prefixEnd_2264630 : Nat := 4983230072969 + 3 ^ 40 * 2264630 * 2
def baseEnd_2264630 : Nat := 775229129727719905606775

theorem tailTrace_2264630 : CollatzResearch.WordTrace tailWord_2264630 prefixEnd_2264630 775229129727719905606775 := by
  unfold tailWord_2264630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162365111602484553558459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55065227857093168571290229 5162365111602484553558459)
  ·
    refine ⟨7743547667403726830337689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162365111602484553558459 7743547667403726830337689)
    ·
      refine ⟨5807660750552795122753267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7743547667403726830337689 5807660750552795122753267)
      ·
        refine ⟨8711491125829192684129901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5807660750552795122753267 8711491125829192684129901)
        ·
          refine ⟨3266809172185947256548713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8711491125829192684129901 3266809172185947256548713)
          ·
            refine ⟨2450106879139460442411535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3266809172185947256548713 2450106879139460442411535)
            ·
              refine ⟨3675160318709190663617303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450106879139460442411535 3675160318709190663617303)
              ·
                refine ⟨5512740478063785995425955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675160318709190663617303 5512740478063785995425955)
                ·
                  refine ⟨8269110717095678993138933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5512740478063785995425955 8269110717095678993138933)
                  ·
                    refine ⟨775229129727719905606775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8269110717095678993138933 775229129727719905606775)
                    ·
                      rfl

theorem cell22_2264630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2264630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264630 prefixEnd_2264630 := by exact prefixLift 2264630
  have htrace : WordTrace (prefixWord ++ tailWord_2264630) baseStart_2264630 baseEnd_2264630 := by
    simpa [prefixWord, tailWord_2264630, baseEnd_2264630] using wordTrace_append hprefix tailTrace_2264630
  have hstable : (prefixWord ++ tailWord_2264630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264630).length < 2 ^ (prefixWord ++ tailWord_2264630).sum := by decide
  have hdescent : baseEnd_2264630 < baseStart_2264630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264662 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2264662 : Nat := 118140960795 + 2264662 * 2 ^ 59
def prefixEnd_2264662 : Nat := 4983230072969 + 3 ^ 40 * 2264662 * 2
def baseEnd_2264662 : Nat := 775240083981682488806677

theorem tailTrace_2264662 : CollatzResearch.WordTrace tailWord_2264662 prefixEnd_2264662 775240083981682488806677 := by
  unfold tailWord_2264662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162438057595238895131265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55066005947682548214733493 5162438057595238895131265)
  ·
    refine ⟨3871828543196429171348449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5162438057595238895131265 3871828543196429171348449)
    ·
      refine ⟨2903871407397321878511337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3871828543196429171348449 2903871407397321878511337)
      ·
        refine ⟨2177903555547991408883503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903871407397321878511337 2177903555547991408883503)
        ·
          refine ⟨3266855333321987113325255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177903555547991408883503 3266855333321987113325255)
          ·
            refine ⟨4900282999982980669987883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266855333321987113325255 4900282999982980669987883)
            ·
              refine ⟨7350424499974471004981825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900282999982980669987883 7350424499974471004981825)
              ·
                refine ⟨5512818374980853253736369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7350424499974471004981825 5512818374980853253736369)
                ·
                  refine ⟨4134613781235639940302277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512818374980853253736369 4134613781235639940302277)
                  ·
                    refine ⟨775240083981682488806677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4134613781235639940302277 775240083981682488806677)
                    ·
                      rfl

theorem cell22_2264662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2264662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264662 prefixEnd_2264662 := by exact prefixLift 2264662
  have htrace : WordTrace (prefixWord ++ tailWord_2264662) baseStart_2264662 baseEnd_2264662 := by
    simpa [prefixWord, tailWord_2264662, baseEnd_2264662] using wordTrace_append hprefix tailTrace_2264662
  have hstable : (prefixWord ++ tailWord_2264662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264662).length < 2 ^ (prefixWord ++ tailWord_2264662).sum := by decide
  have hdescent : baseEnd_2264662 < baseStart_2264662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264684 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_2264684 : Nat := 118140960795 + 2264684 * 2 ^ 59
def prefixEnd_2264684 : Nat := 4983230072969 + 3 ^ 40 * 2264684 * 2
def baseEnd_2264684 : Nat := 775247615031281764756609

theorem tailTrace_2264684 : CollatzResearch.WordTrace tailWord_2264684 prefixEnd_2264684 775247615031281764756609 := by
  unfold tailWord_2264684
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299905663722060039700553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55066540884962746719600737 41299905663722060039700553)
  ·
    refine ⟨30974929247791545029775415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41299905663722060039700553 30974929247791545029775415)
    ·
      refine ⟨46462393871687317544663123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30974929247791545029775415 46462393871687317544663123)
      ·
        refine ⟨69693590807530976316994685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46462393871687317544663123 69693590807530976316994685)
        ·
          refine ⟨26135096552824116118873007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69693590807530976316994685 26135096552824116118873007)
          ·
            refine ⟨39202644829236174178309511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26135096552824116118873007 39202644829236174178309511)
            ·
              refine ⟨58803967243854261267464267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39202644829236174178309511 58803967243854261267464267)
              ·
                refine ⟨88205950865781391901196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58803967243854261267464267 88205950865781391901196401)
                ·
                  refine ⟨66154463149336043925897301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88205950865781391901196401 66154463149336043925897301)
                  ·
                    refine ⟨775247615031281764756609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66154463149336043925897301 775247615031281764756609)
                    ·
                      rfl

theorem cell22_2264684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_2264684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264684 prefixEnd_2264684 := by exact prefixLift 2264684
  have htrace : WordTrace (prefixWord ++ tailWord_2264684) baseStart_2264684 baseEnd_2264684 := by
    simpa [prefixWord, tailWord_2264684, baseEnd_2264684] using wordTrace_append hprefix tailTrace_2264684
  have hstable : (prefixWord ++ tailWord_2264684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264684).length < 2 ^ (prefixWord ++ tailWord_2264684).sum := by decide
  have hdescent : baseEnd_2264684 < baseStart_2264684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264688 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 5]
def baseStart_2264688 : Nat := 118140960795 + 2264688 * 2 ^ 59
def prefixEnd_2264688 : Nat := 4983230072969 + 3 ^ 40 * 2264688 * 2
def baseEnd_2264688 : Nat := 258416328104342362552199

theorem tailTrace_2264688 : CollatzResearch.WordTrace tailWord_2264688 prefixEnd_2264688 258416328104342362552199 := by
  unfold tailWord_2264688
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299978609714814381273359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55066638146286419175031145 41299978609714814381273359)
  ·
    refine ⟨61949967914572221571910039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41299978609714814381273359 61949967914572221571910039)
    ·
      refine ⟨92924951871858332357865059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61949967914572221571910039 92924951871858332357865059)
      ·
        refine ⟨139387427807787498536797589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92924951871858332357865059 139387427807787498536797589)
        ·
          refine ⟨6533785678490038993912387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139387427807787498536797589 6533785678490038993912387)
          ·
            refine ⟨9800678517735058490868581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533785678490038993912387 9800678517735058490868581)
            ·
              refine ⟨1837627222075323467037859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9800678517735058490868581 1837627222075323467037859)
              ·
                refine ⟨2756440833112985200556789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837627222075323467037859 2756440833112985200556789)
                ·
                  refine ⟨258416328104342362552199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2756440833112985200556789 258416328104342362552199)
                  ·
                    rfl

theorem cell22_2264688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_2264688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264688 prefixEnd_2264688 := by exact prefixLift 2264688
  have htrace : WordTrace (prefixWord ++ tailWord_2264688) baseStart_2264688 baseEnd_2264688 := by
    simpa [prefixWord, tailWord_2264688, baseEnd_2264688] using wordTrace_append hprefix tailTrace_2264688
  have hstable : (prefixWord ++ tailWord_2264688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264688).length < 2 ^ (prefixWord ++ tailWord_2264688).sum := by decide
  have hdescent : baseEnd_2264688 < baseStart_2264688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264699 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 8]
def baseStart_2264699 : Nat := 118140960795 + 2264699 * 2 ^ 59
def prefixEnd_2264699 : Nat := 4983230072969 + 3 ^ 40 * 2264699 * 2
def baseEnd_2264699 : Nat := 258417583279275575210521

theorem tailTrace_2264699 : CollatzResearch.WordTrace tailWord_2264699 prefixEnd_2264699 258417583279275575210521 := by
  unfold tailWord_2264699
  simp only [CollatzResearch.WordTrace]
  refine ⟨82600358422389777641197151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55066905614926518427464767 82600358422389777641197151)
  ·
    refine ⟨123900537633584666461795727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82600358422389777641197151 123900537633584666461795727)
    ·
      refine ⟨185850806450376999692693591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123900537633584666461795727 185850806450376999692693591)
      ·
        refine ⟨278776209675565499539040387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185850806450376999692693591 278776209675565499539040387)
        ·
          refine ⟨418164314513348249308560581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278776209675565499539040387 418164314513348249308560581)
          ·
            refine ⟨78405808971252796745355109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 418164314513348249308560581 78405808971252796745355109)
            ·
              refine ⟨14701089182109899389754083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78405808971252796745355109 14701089182109899389754083)
              ·
                refine ⟨22051633773164849084631125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14701089182109899389754083 22051633773164849084631125)
                ·
                  refine ⟨258417583279275575210521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22051633773164849084631125 258417583279275575210521)
                  ·
                    rfl

theorem cell22_2264699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_2264699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264699 prefixEnd_2264699 := by exact prefixLift 2264699
  have htrace : WordTrace (prefixWord ++ tailWord_2264699) baseStart_2264699 baseEnd_2264699 := by
    simpa [prefixWord, tailWord_2264699, baseEnd_2264699] using wordTrace_append hprefix tailTrace_2264699
  have hstable : (prefixWord ++ tailWord_2264699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264699).length < 2 ^ (prefixWord ++ tailWord_2264699).sum := by decide
  have hdescent : baseEnd_2264699 < baseStart_2264699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264750 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2264750 : Nat := 118140960795 + 2264750 * 2 ^ 59
def prefixEnd_2264750 : Nat := 4983230072969 + 3 ^ 40 * 2264750 * 2
def baseEnd_2264750 : Nat := 258423402726693197535469

theorem tailTrace_2264750 : CollatzResearch.WordTrace tailWord_2264750 prefixEnd_2264750 258423402726693197535469 := by
  unfold tailWord_2264750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10325277318150626668912963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55068145696803342234202469 10325277318150626668912963)
  ·
    refine ⟨15487915977225940003369445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10325277318150626668912963 15487915977225940003369445)
    ·
      refine ⟨2903984245729863750631771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15487915977225940003369445 2903984245729863750631771)
      ·
        refine ⟨4355976368594795625947657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903984245729863750631771 4355976368594795625947657)
        ·
          refine ⟨3266982276446096719460743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4355976368594795625947657 3266982276446096719460743)
          ·
            refine ⟨4900473414669145079191115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266982276446096719460743 4900473414669145079191115)
            ·
              refine ⟨7350710122003717618786673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900473414669145079191115 7350710122003717618786673)
              ·
                refine ⟨5513032591502788214090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7350710122003717618786673 5513032591502788214090005)
                ·
                  refine ⟨258423402726693197535469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5513032591502788214090005 258423402726693197535469)
                  ·
                    rfl

theorem cell22_2264750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2264750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264750 prefixEnd_2264750 := by exact prefixLift 2264750
  have htrace : WordTrace (prefixWord ++ tailWord_2264750) baseStart_2264750 baseEnd_2264750 := by
    simpa [prefixWord, tailWord_2264750, baseEnd_2264750] using wordTrace_append hprefix tailTrace_2264750
  have hstable : (prefixWord ++ tailWord_2264750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264750).length < 2 ^ (prefixWord ++ tailWord_2264750).sum := by decide
  have hdescent : baseEnd_2264750 < baseStart_2264750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264793 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_2264793 : Nat := 118140960795 + 2264793 * 2 ^ 59
def prefixEnd_2264793 : Nat := 4983230072969 + 3 ^ 40 * 2264793 * 2
def baseEnd_2264793 : Nat := 775284927958841813781275

theorem tailTrace_2264793 : CollatzResearch.WordTrace tailWord_2264793 prefixEnd_2264793 775284927958841813781275 := by
  unfold tailWord_2264793
  simp only [CollatzResearch.WordTrace]
  refine ⟨82603786884049231695119033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55069191256032821130079355 82603786884049231695119033)
  ·
    refine ⟨61952840163036923771339275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82603786884049231695119033 61952840163036923771339275)
    ·
      refine ⟨92929260244555385657008913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61952840163036923771339275 92929260244555385657008913)
      ·
        refine ⟨69696945183416539242756685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92929260244555385657008913 69696945183416539242756685)
        ·
          refine ⟨26136354443781202216033757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69696945183416539242756685 26136354443781202216033757)
          ·
            refine ⟨9801132916417950831012659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26136354443781202216033757 9801132916417950831012659)
            ·
              refine ⟨14701699374626926246518989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9801132916417950831012659 14701699374626926246518989)
              ·
                refine ⟨5513137265485097342444621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14701699374626926246518989 5513137265485097342444621)
                ·
                  refine ⟨2067426474556911503416733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5513137265485097342444621 2067426474556911503416733)
                  ·
                    refine ⟨775284927958841813781275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2067426474556911503416733 775284927958841813781275)
                    ·
                      rfl

theorem cell22_2264793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_2264793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264793 prefixEnd_2264793 := by exact prefixLift 2264793
  have htrace : WordTrace (prefixWord ++ tailWord_2264793) baseStart_2264793 baseEnd_2264793 := by
    simpa [prefixWord, tailWord_2264793, baseEnd_2264793] using wordTrace_append hprefix tailTrace_2264793
  have hstable : (prefixWord ++ tailWord_2264793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264793).length < 2 ^ (prefixWord ++ tailWord_2264793).sum := by decide
  have hdescent : baseEnd_2264793 < baseStart_2264793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264851 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 6]
def baseStart_2264851 : Nat := 118140960795 + 2264851 * 2 ^ 59
def prefixEnd_2264851 : Nat := 4983230072969 + 3 ^ 40 * 2264851 * 2
def baseEnd_2264851 : Nat := 258434927514716331943699

theorem tailTrace_2264851 : CollatzResearch.WordTrace tailWord_2264851 prefixEnd_2264851 258434927514716331943699 := by
  unfold tailWord_2264851
  simp only [CollatzResearch.WordTrace]
  refine ⟨82605902317839107600730407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55070601545226071733820271 82605902317839107600730407)
  ·
    refine ⟨123908853476758661401095611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82605902317839107600730407 123908853476758661401095611)
    ·
      refine ⟨185863280215137992101643417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123908853476758661401095611 185863280215137992101643417)
      ·
        refine ⟨139397460161353494076232563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185863280215137992101643417 139397460161353494076232563)
        ·
          refine ⟨209096190242030241114348845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139397460161353494076232563 209096190242030241114348845)
          ·
            refine ⟨78411071340761340417880817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209096190242030241114348845 78411071340761340417880817)
            ·
              refine ⟨58808303505571005313410613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78411071340761340417880817 58808303505571005313410613)
              ·
                refine ⟨5513278453647281748132245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58808303505571005313410613 5513278453647281748132245)
                ·
                  refine ⟨258434927514716331943699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5513278453647281748132245 258434927514716331943699)
                  ·
                    rfl

theorem cell22_2264851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_2264851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264851 prefixEnd_2264851 := by exact prefixLift 2264851
  have htrace : WordTrace (prefixWord ++ tailWord_2264851) baseStart_2264851 baseEnd_2264851 := by
    simpa [prefixWord, tailWord_2264851, baseEnd_2264851] using wordTrace_append hprefix tailTrace_2264851
  have hstable : (prefixWord ++ tailWord_2264851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264851).length < 2 ^ (prefixWord ++ tailWord_2264851).sum := by decide
  have hdescent : baseEnd_2264851 < baseStart_2264851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264913 : List Nat := [1, 2, 2, 1, 5, 1, 3, 7]
def baseStart_2264913 : Nat := 118140960795 + 2264913 * 2 ^ 59
def prefixEnd_2264913 : Nat := 4983230072969 + 3 ^ 40 * 2264913 * 2
def baseEnd_2264913 : Nat := 86147334045689055642323

theorem tailTrace_2264913 : CollatzResearch.WordTrace tailWord_2264913 prefixEnd_2264913 86147334045689055642323 := by
  unfold tailWord_2264913
  simp only [CollatzResearch.WordTrace]
  refine ⟨82608163643614492189487393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55072109095742994792991595 82608163643614492189487393)
  ·
    refine ⟨61956122732710869142115545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82608163643614492189487393 61956122732710869142115545)
    ·
      refine ⟨46467092049533151856586659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61956122732710869142115545 46467092049533151856586659)
      ·
        refine ⟨69700638074299727784879989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46467092049533151856586659 69700638074299727784879989)
        ·
          refine ⟨6534434819465599479832499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69700638074299727784879989 6534434819465599479832499)
          ·
            refine ⟨9801652229198399219748749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6534434819465599479832499 9801652229198399219748749)
            ·
              refine ⟨3675619585949399707405781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9801652229198399219748749 3675619585949399707405781)
              ·
                refine ⟨86147334045689055642323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3675619585949399707405781 86147334045689055642323)
                ·
                  rfl

theorem cell22_2264913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 7].length) (baseStart_2264913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264913 prefixEnd_2264913 := by exact prefixLift 2264913
  have htrace : WordTrace (prefixWord ++ tailWord_2264913) baseStart_2264913 baseEnd_2264913 := by
    simpa [prefixWord, tailWord_2264913, baseEnd_2264913] using wordTrace_append hprefix tailTrace_2264913
  have hstable : (prefixWord ++ tailWord_2264913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264913).length < 2 ^ (prefixWord ++ tailWord_2264913).sum := by decide
  have hdescent : baseEnd_2264913 < baseStart_2264913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264932 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2264932 : Nat := 118140960795 + 2264932 * 2 ^ 59
def prefixEnd_2264932 : Nat := 4983230072969 + 3 ^ 40 * 2264932 * 2
def baseEnd_2264932 : Nat := 775332510499491784555849

theorem tailTrace_2264932 : CollatzResearch.WordTrace tailWord_2264932 prefixEnd_2264932 775332510499491784555849 := by
  unfold tailWord_2264932
  simp only [CollatzResearch.WordTrace]
  refine ⟨41304428315272829217214525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55072571087030438956286033 41304428315272829217214525)
  ·
    refine ⟨15489160618227310956455447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41304428315272829217214525 15489160618227310956455447)
    ·
      refine ⟨23233740927340966434683171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15489160618227310956455447 23233740927340966434683171)
      ·
        refine ⟨34850611391011449652024757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23233740927340966434683171 34850611391011449652024757)
        ·
          refine ⟨3267244817907323404877321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34850611391011449652024757 3267244817907323404877321)
          ·
            refine ⟨2450433613430492553657991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3267244817907323404877321 2450433613430492553657991)
            ·
              refine ⟨3675650420145738830486987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450433613430492553657991 3675650420145738830486987)
              ·
                refine ⟨5513475630218608245730481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675650420145738830486987 5513475630218608245730481)
                ·
                  refine ⟨4135106722663956184297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5513475630218608245730481 4135106722663956184297861)
                  ·
                    refine ⟨775332510499491784555849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4135106722663956184297861 775332510499491784555849)
                    ·
                      rfl

theorem cell22_2264932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2264932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2264932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2264932 prefixEnd_2264932 := by exact prefixLift 2264932
  have htrace : WordTrace (prefixWord ++ tailWord_2264932) baseStart_2264932 baseEnd_2264932 := by
    simpa [prefixWord, tailWord_2264932, baseEnd_2264932] using wordTrace_append hprefix tailTrace_2264932
  have hstable : (prefixWord ++ tailWord_2264932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264932).length < 2 ^ (prefixWord ++ tailWord_2264932).sum := by decide
  have hdescent : baseEnd_2264932 < baseStart_2264932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265018 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_2265018 : Nat := 118140960795 + 2265018 * 2 ^ 59
def prefixEnd_2265018 : Nat := 4983230072969 + 3 ^ 40 * 2265018 * 2
def baseEnd_2265018 : Nat := 775361950057016226905585

theorem tailTrace_2265018 : CollatzResearch.WordTrace tailWord_2265018 prefixEnd_2265018 775361950057016226905585 := by
  unfold tailWord_2265018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20652998327058523780514927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55074662205489396748039805 20652998327058523780514927)
  ·
    refine ⟨30979497490587785670772391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20652998327058523780514927 30979497490587785670772391)
    ·
      refine ⟨46469246235881678506158587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30979497490587785670772391 46469246235881678506158587)
      ·
        refine ⟨69703869353822517759237881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46469246235881678506158587 69703869353822517759237881)
        ·
          refine ⟨52277902015366888319428411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69703869353822517759237881 52277902015366888319428411)
          ·
            refine ⟨78416853023050332479142617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52277902015366888319428411 78416853023050332479142617)
            ·
              refine ⟨58812639767287749359356963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78416853023050332479142617 58812639767287749359356963)
              ·
                refine ⟨88218959650931624039035445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58812639767287749359356963 88218959650931624039035445)
                ·
                  refine ⟨8270527467274839753659573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88218959650931624039035445 8270527467274839753659573)
                  ·
                    refine ⟨775361950057016226905585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8270527467274839753659573 775361950057016226905585)
                    ·
                      rfl

theorem cell22_2265018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_2265018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2265018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2265018 prefixEnd_2265018 := by exact prefixLift 2265018
  have htrace : WordTrace (prefixWord ++ tailWord_2265018) baseStart_2265018 baseEnd_2265018 := by
    simpa [prefixWord, tailWord_2265018, baseEnd_2265018] using wordTrace_append hprefix tailTrace_2265018
  have hstable : (prefixWord ++ tailWord_2265018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265018).length < 2 ^ (prefixWord ++ tailWord_2265018).sum := by decide
  have hdescent : baseEnd_2265018 < baseStart_2265018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
