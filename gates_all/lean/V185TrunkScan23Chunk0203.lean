import V185TrunkScan23Chunk0202

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1201439 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 2, 2, 3]
def baseStart_1201439 : Nat := 118140960795 + 1201439 * 2 ^ 59
def prefixEnd_1201439 : Nat := 4983230072969 + 3 ^ 40 * 1201439 * 2
def baseEnd_1201439 : Nat := 616915684057230098087189

theorem tailTrace_1201439 : CollatzResearch.WordTrace tailWord_1201439 prefixEnd_1201439 616915684057230098087189 := by
  unfold tailWord_1201439
  simp only [CollatzResearch.WordTrace]
  refine ⟨43820080294399167290343371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29213386862932778193562247 43820080294399167290343371)
  ·
    refine ⟨65730120441598750935515057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43820080294399167290343371 65730120441598750935515057)
    ·
      refine ⟨49297590331199063201636293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65730120441598750935515057 49297590331199063201636293)
      ·
        refine ⟨9243298187099824350306805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49297590331199063201636293 9243298187099824350306805)
        ·
          refine ⟨866559205040608532841263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9243298187099824350306805 866559205040608532841263)
          ·
            refine ⟨1299838807560912799261895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866559205040608532841263 1299838807560912799261895)
            ·
              refine ⟨1949758211341369198892843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299838807560912799261895 1949758211341369198892843)
              ·
                refine ⟨2924637317012053798339265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949758211341369198892843 2924637317012053798339265)
                ·
                  refine ⟨2193477987759040348754449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2924637317012053798339265 2193477987759040348754449)
                  ·
                    refine ⟨1645108490819280261565837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2193477987759040348754449 1645108490819280261565837)
                    ·
                      refine ⟨616915684057230098087189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1645108490819280261565837 616915684057230098087189)
                      ·
                        rfl

theorem cell23_1201439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_1201439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201439 prefixEnd_1201439 := by exact prefixLift 1201439
  have htrace : WordTrace (prefixWord ++ tailWord_1201439) baseStart_1201439 baseEnd_1201439 := by
    simpa [prefixWord, tailWord_1201439, baseEnd_1201439] using wordTrace_append hprefix tailTrace_1201439
  have hstable : (prefixWord ++ tailWord_1201439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201439).length < 2 ^ (prefixWord ++ tailWord_1201439).sum := by decide
  have hdescent : baseEnd_1201439 < baseStart_1201439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201488 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_1201488 : Nat := 118140960795 + 1201488 * 2 ^ 59
def prefixEnd_1201488 : Nat := 4983230072969 + 3 ^ 40 * 1201488 * 2
def baseEnd_1201488 : Nat := 616940844609300406374463

theorem tailTrace_1201488 : CollatzResearch.WordTrace tailWord_1201488 prefixEnd_1201488 616940844609300406374463 := by
  unfold tailWord_1201488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910933735610824329438559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29214578314147765772584745 21910933735610824329438559)
  ·
    refine ⟨32866400603416236494157839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21910933735610824329438559 32866400603416236494157839)
    ·
      refine ⟨49299600905124354741236759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32866400603416236494157839 49299600905124354741236759)
      ·
        refine ⟨73949401357686532111855139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49299600905124354741236759 73949401357686532111855139)
        ·
          refine ⟨110924102036529798167782709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73949401357686532111855139 110924102036529798167782709)
          ·
            refine ⟨10399134565924668578229629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110924102036529798167782709 10399134565924668578229629)
            ·
              refine ⟨3899675462221750716836111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10399134565924668578229629 3899675462221750716836111)
              ·
                refine ⟨5849513193332626075254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899675462221750716836111 5849513193332626075254167)
                ·
                  refine ⟨8774269789998939112881251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5849513193332626075254167 8774269789998939112881251)
                  ·
                    refine ⟨13161404684998408669321877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8774269789998939112881251 13161404684998408669321877)
                    ·
                      refine ⟨616940844609300406374463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13161404684998408669321877 616940844609300406374463)
                      ·
                        rfl

theorem cell23_1201488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_1201488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201488 prefixEnd_1201488 := by exact prefixLift 1201488
  have htrace : WordTrace (prefixWord ++ tailWord_1201488) baseStart_1201488 baseEnd_1201488 := by
    simpa [prefixWord, tailWord_1201488, baseEnd_1201488] using wordTrace_append hprefix tailTrace_1201488
  have hstable : (prefixWord ++ tailWord_1201488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201488).length < 2 ^ (prefixWord ++ tailWord_1201488).sum := by decide
  have hdescent : baseEnd_1201488 < baseStart_1201488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201492 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1201492 : Nat := 118140960795 + 1201492 * 2 ^ 59
def prefixEnd_1201492 : Nat := 4983230072969 + 3 ^ 40 * 1201492 * 2
def baseEnd_1201492 : Nat := 616942898531918390724445

theorem tailTrace_1201492 : CollatzResearch.WordTrace tailWord_1201492 prefixEnd_1201492 616942898531918390724445 := by
  unfold tailWord_1201492
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911006681603578671011365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29214675575471438228015153 21911006681603578671011365)
  ·
    refine ⟨4108313752800671000814631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21911006681603578671011365 4108313752800671000814631)
    ·
      refine ⟨6162470629201006501221947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108313752800671000814631 6162470629201006501221947)
      ·
        refine ⟨9243705943801509751832921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6162470629201006501221947 9243705943801509751832921)
        ·
          refine ⟨6932779457851132313874691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9243705943801509751832921 6932779457851132313874691)
          ·
            refine ⟨10399169186776698470812037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932779457851132313874691 10399169186776698470812037)
            ·
              refine ⟨1949844222520630963277257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10399169186776698470812037 1949844222520630963277257)
              ·
                refine ⟨1462383166890473222457943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1949844222520630963277257 1462383166890473222457943)
                ·
                  refine ⟨2193574750335709833686915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462383166890473222457943 2193574750335709833686915)
                  ·
                    refine ⟨3290362125503564750530373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193574750335709833686915 3290362125503564750530373)
                    ·
                      refine ⟨616942898531918390724445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3290362125503564750530373 616942898531918390724445)
                      ·
                        rfl

theorem cell23_1201492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1201492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201492 prefixEnd_1201492 := by exact prefixLift 1201492
  have htrace : WordTrace (prefixWord ++ tailWord_1201492) baseStart_1201492 baseEnd_1201492 := by
    simpa [prefixWord, tailWord_1201492, baseEnd_1201492] using wordTrace_append hprefix tailTrace_1201492
  have hstable : (prefixWord ++ tailWord_1201492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201492).length < 2 ^ (prefixWord ++ tailWord_1201492).sum := by decide
  have hdescent : baseEnd_1201492 < baseStart_1201492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201512 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1201512 : Nat := 118140960795 + 1201512 * 2 ^ 59
def prefixEnd_1201512 : Nat := 4983230072969 + 3 ^ 40 * 1201512 * 2
def baseEnd_1201512 : Nat := 616953168145008312474353

theorem tailTrace_1201512 : CollatzResearch.WordTrace tailWord_1201512 prefixEnd_1201512 616953168145008312474353 := by
  unfold tailWord_1201512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911371411567350378875395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29215161882089800505167193 21911371411567350378875395)
  ·
    refine ⟨32867057117351025568313093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21911371411567350378875395 32867057117351025568313093)
    ·
      refine ⟨6162573209503317294058705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32867057117351025568313093 6162573209503317294058705)
      ·
        refine ⟨4621929907127487970544029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6162573209503317294058705 4621929907127487970544029)
        ·
          refine ⟨1733223715172807988954011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4621929907127487970544029 1733223715172807988954011)
          ·
            refine ⟨2599835572759211983431017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733223715172807988954011 2599835572759211983431017)
            ·
              refine ⟨1949876679569408987573263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599835572759211983431017 1949876679569408987573263)
              ·
                refine ⟨2924815019354113481359895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949876679569408987573263 2924815019354113481359895)
                ·
                  refine ⟨4387222529031170222039843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924815019354113481359895 4387222529031170222039843)
                  ·
                    refine ⟨6580833793546755333059765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4387222529031170222039843 6580833793546755333059765)
                    ·
                      refine ⟨616953168145008312474353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6580833793546755333059765 616953168145008312474353)
                      ·
                        rfl

theorem cell23_1201512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1201512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201512 prefixEnd_1201512 := by exact prefixLift 1201512
  have htrace : WordTrace (prefixWord ++ tailWord_1201512) baseStart_1201512 baseEnd_1201512 := by
    simpa [prefixWord, tailWord_1201512, baseEnd_1201512] using wordTrace_append hprefix tailTrace_1201512
  have hstable : (prefixWord ++ tailWord_1201512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201512).length < 2 ^ (prefixWord ++ tailWord_1201512).sum := by decide
  have hdescent : baseEnd_1201512 < baseStart_1201512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201575 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1201575 : Nat := 118140960795 + 1201575 * 2 ^ 59
def prefixEnd_1201575 : Nat := 4983230072969 + 3 ^ 40 * 1201575 * 2
def baseEnd_1201575 : Nat := 205661839142080521995521

theorem tailTrace_1201575 : CollatzResearch.WordTrace tailWord_1201575 prefixEnd_1201575 205661839142080521995521 := by
  unfold tailWord_1201575
  simp only [CollatzResearch.WordTrace]
  refine ⟨43825040621906462517294179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29216693747937641678196119 43825040621906462517294179)
  ·
    refine ⟨65737560932859693775941269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43825040621906462517294179 65737560932859693775941269)
    ·
      refine ⟨3081448168727798145747247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65737560932859693775941269 3081448168727798145747247)
      ·
        refine ⟨4622172253091697218620871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081448168727798145747247 4622172253091697218620871)
        ·
          refine ⟨6933258379637545827931307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622172253091697218620871 6933258379637545827931307)
          ·
            refine ⟨10399887569456318741896961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933258379637545827931307 10399887569456318741896961)
            ·
              refine ⟨7799915677092239056422721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10399887569456318741896961 7799915677092239056422721)
              ·
                refine ⟨5849936757819179292317041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7799915677092239056422721 5849936757819179292317041)
                ·
                  refine ⟨4387452568364384469237781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5849936757819179292317041 4387452568364384469237781)
                  ·
                    refine ⟨205661839142080521995521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4387452568364384469237781 205661839142080521995521)
                    ·
                      rfl

theorem cell23_1201575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1201575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201575 prefixEnd_1201575 := by exact prefixLift 1201575
  have htrace : WordTrace (prefixWord ++ tailWord_1201575) baseStart_1201575 baseEnd_1201575 := by
    simpa [prefixWord, tailWord_1201575, baseEnd_1201575] using wordTrace_append hprefix tailTrace_1201575
  have hstable : (prefixWord ++ tailWord_1201575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201575).length < 2 ^ (prefixWord ++ tailWord_1201575).sum := by decide
  have hdescent : baseEnd_1201575 < baseStart_1201575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201585 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1201585 : Nat := 118140960795 + 1201585 * 2 ^ 59
def prefixEnd_1201585 : Nat := 4983230072969 + 3 ^ 40 * 1201585 * 2
def baseEnd_1201585 : Nat := 616990652232786526861517

theorem tailTrace_1201585 : CollatzResearch.WordTrace tailWord_1201585 prefixEnd_1201585 616990652232786526861517 := by
  unfold tailWord_1201585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43825405351870234225158209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29216936901246822816772139 43825405351870234225158209)
  ·
    refine ⟨32869054013902675668868657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43825405351870234225158209 32869054013902675668868657)
    ·
      refine ⟨24651790510427006751651493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32869054013902675668868657 24651790510427006751651493)
      ·
        refine ⟨4622210720705063765934655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24651790510427006751651493 4622210720705063765934655)
        ·
          refine ⟨6933316081057595648901983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622210720705063765934655 6933316081057595648901983)
          ·
            refine ⟨10399974121586393473352975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6933316081057595648901983 10399974121586393473352975)
            ·
              refine ⟨15599961182379590210029463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10399974121586393473352975 15599961182379590210029463)
              ·
                refine ⟨23399941773569385315044195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15599961182379590210029463 23399941773569385315044195)
                ·
                  refine ⟨35099912660354077972566293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23399941773569385315044195 35099912660354077972566293)
                  ·
                    refine ⟨1645308405954097404964045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35099912660354077972566293 1645308405954097404964045)
                    ·
                      refine ⟨616990652232786526861517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1645308405954097404964045 616990652232786526861517)
                      ·
                        rfl

theorem cell23_1201585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1201585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201585 prefixEnd_1201585 := by exact prefixLift 1201585
  have htrace : WordTrace (prefixWord ++ tailWord_1201585) baseStart_1201585 baseEnd_1201585 := by
    simpa [prefixWord, tailWord_1201585, baseEnd_1201585] using wordTrace_append hprefix tailTrace_1201585
  have hstable : (prefixWord ++ tailWord_1201585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201585).length < 2 ^ (prefixWord ++ tailWord_1201585).sum := by decide
  have hdescent : baseEnd_1201585 < baseStart_1201585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201620 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1201620 : Nat := 118140960795 + 1201620 * 2 ^ 59
def prefixEnd_1201620 : Nat := 4983230072969 + 3 ^ 40 * 1201620 * 2
def baseEnd_1201620 : Nat := 617008624055693889923857

theorem tailTrace_1201620 : CollatzResearch.WordTrace tailWord_1201620 prefixEnd_1201620 617008624055693889923857 := by
  unfold tailWord_1201620
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913340953371717601341157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29217787937828956801788209 21913340953371717601341157)
  ·
    refine ⟨4108751428757197050251467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21913340953371717601341157 4108751428757197050251467)
    ·
      refine ⟨6163127143135795575377201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108751428757197050251467 6163127143135795575377201)
      ·
        refine ⟨4622345357351846681532901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6163127143135795575377201 4622345357351846681532901)
        ·
          refine ⟨866689754503471252787419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4622345357351846681532901 866689754503471252787419)
          ·
            refine ⟨1300034631755206879181129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866689754503471252787419 1300034631755206879181129)
            ·
              refine ⟨975025973816405159385847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300034631755206879181129 975025973816405159385847)
              ·
                refine ⟨1462538960724607739078771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975025973816405159385847 1462538960724607739078771)
                ·
                  refine ⟨2193808441086911608618157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462538960724607739078771 2193808441086911608618157)
                  ·
                    refine ⟨822678165407591853231809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193808441086911608618157 822678165407591853231809)
                    ·
                      refine ⟨617008624055693889923857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822678165407591853231809 617008624055693889923857)
                      ·
                        rfl

theorem cell23_1201620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1201620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201620 prefixEnd_1201620 := by exact prefixLift 1201620
  have htrace : WordTrace (prefixWord ++ tailWord_1201620) baseStart_1201620 baseEnd_1201620 := by
    simpa [prefixWord, tailWord_1201620, baseEnd_1201620] using wordTrace_append hprefix tailTrace_1201620
  have hstable : (prefixWord ++ tailWord_1201620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201620).length < 2 ^ (prefixWord ++ tailWord_1201620).sum := by decide
  have hdescent : baseEnd_1201620 < baseStart_1201620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201655 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1201655 : Nat := 118140960795 + 1201655 * 2 ^ 59
def prefixEnd_1201655 : Nat := 4983230072969 + 3 ^ 40 * 1201655 * 2
def baseEnd_1201655 : Nat := 617026595878601252986195

theorem tailTrace_1201655 : CollatzResearch.WordTrace tailWord_1201655 prefixEnd_1201655 617026595878601252986195 := by
  unfold tailWord_1201655
  simp only [CollatzResearch.WordTrace]
  refine ⟨43827958461616636180206419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29218638974411090786804279 43827958461616636180206419)
  ·
    refine ⟨65741937692424954270309629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43827958461616636180206419 65741937692424954270309629)
    ·
      refine ⟨24653226634659357851366111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65741937692424954270309629 24653226634659357851366111)
      ·
        refine ⟨36979839951989036777049167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24653226634659357851366111 36979839951989036777049167)
        ·
          refine ⟨55469759927983555165573751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36979839951989036777049167 55469759927983555165573751)
          ·
            refine ⟨83204639891975332748360627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55469759927983555165573751 83204639891975332748360627)
            ·
              refine ⟨124806959837962999122540941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83204639891975332748360627 124806959837962999122540941)
              ·
                refine ⟨46802609939236124670952853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124806959837962999122540941 46802609939236124670952853)
                ·
                  refine ⟨2193872340901693343950915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46802609939236124670952853 2193872340901693343950915)
                  ·
                    refine ⟨3290808511352540015926373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2193872340901693343950915 3290808511352540015926373)
                    ·
                      refine ⟨617026595878601252986195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3290808511352540015926373 617026595878601252986195)
                      ·
                        rfl

theorem cell23_1201655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1201655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201655 prefixEnd_1201655 := by exact prefixLift 1201655
  have htrace : WordTrace (prefixWord ++ tailWord_1201655) baseStart_1201655 baseEnd_1201655 := by
    simpa [prefixWord, tailWord_1201655, baseEnd_1201655] using wordTrace_append hprefix tailTrace_1201655
  have hstable : (prefixWord ++ tailWord_1201655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201655).length < 2 ^ (prefixWord ++ tailWord_1201655).sum := by decide
  have hdescent : baseEnd_1201655 < baseStart_1201655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201672 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_1201672 : Nat := 118140960795 + 1201672 * 2 ^ 59
def prefixEnd_1201672 : Nat := 4983230072969 + 3 ^ 40 * 1201672 * 2
def baseEnd_1201672 : Nat := 617035325049727686473617

theorem tailTrace_1201672 : CollatzResearch.WordTrace tailWord_1201672 prefixEnd_1201672 617035325049727686473617 := by
  unfold tailWord_1201672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21914289251277524041787635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29219052335036698722383513 21914289251277524041787635)
  ·
    refine ⟨32871433876916286062681453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21914289251277524041787635 32871433876916286062681453)
    ·
      refine ⟨12326787703843607273505545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32871433876916286062681453 12326787703843607273505545)
      ·
        refine ⟨9245090777882705455129159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12326787703843607273505545 9245090777882705455129159)
        ·
          refine ⟨13867636166824058182693739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245090777882705455129159 13867636166824058182693739)
          ·
            refine ⟨20801454250236087274040609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13867636166824058182693739 20801454250236087274040609)
            ·
              refine ⟨15601090687677065455530457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20801454250236087274040609 15601090687677065455530457)
              ·
                refine ⟨11700818015757799091647843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15601090687677065455530457 11700818015757799091647843)
                ·
                  refine ⟨17551227023636698637471765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11700818015757799091647843 17551227023636698637471765)
                  ·
                    refine ⟨822713766732970248631489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17551227023636698637471765 822713766732970248631489)
                    ·
                      refine ⟨617035325049727686473617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822713766732970248631489 617035325049727686473617)
                      ·
                        rfl

theorem cell23_1201672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_1201672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201672 prefixEnd_1201672 := by exact prefixLift 1201672
  have htrace : WordTrace (prefixWord ++ tailWord_1201672) baseStart_1201672 baseEnd_1201672 := by
    simpa [prefixWord, tailWord_1201672, baseEnd_1201672] using wordTrace_append hprefix tailTrace_1201672
  have hstable : (prefixWord ++ tailWord_1201672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201672).length < 2 ^ (prefixWord ++ tailWord_1201672).sum := by decide
  have hdescent : baseEnd_1201672 < baseStart_1201672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201695 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 8]
def baseStart_1201695 : Nat := 118140960795 + 1201695 * 2 ^ 59
def prefixEnd_1201695 : Nat := 4983230072969 + 3 ^ 40 * 1201695 * 2
def baseEnd_1201695 : Nat := 68560792789420121831779

theorem tailTrace_1201695 : CollatzResearch.WordTrace tailWord_1201695 prefixEnd_1201695 68560792789420121831779 := by
  unfold tailWord_1201695
  simp only [CollatzResearch.WordTrace]
  refine ⟨43829417381471723011662539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29219611587647815341108359 43829417381471723011662539)
  ·
    refine ⟨65744126072207584517493809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43829417381471723011662539 65744126072207584517493809)
    ·
      refine ⟨49308094554155688388120357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65744126072207584517493809 49308094554155688388120357)
      ·
        refine ⟨9245267728904191572772567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49308094554155688388120357 9245267728904191572772567)
        ·
          refine ⟨13867901593356287359158851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9245267728904191572772567 13867901593356287359158851)
          ·
            refine ⟨20801852390034431038738277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13867901593356287359158851 20801852390034431038738277)
            ·
              refine ⟨3900347323131455819763427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20801852390034431038738277 3900347323131455819763427)
              ·
                refine ⟨5850520984697183729645141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900347323131455819763427 5850520984697183729645141)
                ·
                  refine ⟨68560792789420121831779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5850520984697183729645141 68560792789420121831779)
                  ·
                    rfl

theorem cell23_1201695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 8].length) (baseStart_1201695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201695 prefixEnd_1201695 := by exact prefixLift 1201695
  have htrace : WordTrace (prefixWord ++ tailWord_1201695) baseStart_1201695 baseEnd_1201695 := by
    simpa [prefixWord, tailWord_1201695, baseEnd_1201695] using wordTrace_append hprefix tailTrace_1201695
  have hstable : (prefixWord ++ tailWord_1201695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201695).length < 2 ^ (prefixWord ++ tailWord_1201695).sum := by decide
  have hdescent : baseEnd_1201695 < baseStart_1201695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201772 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_1201772 : Nat := 118140960795 + 1201772 * 2 ^ 59
def prefixEnd_1201772 : Nat := 4983230072969 + 3 ^ 40 * 1201772 * 2
def baseEnd_1201772 : Nat := 205695557705059098407719

theorem tailTrace_1201772 : CollatzResearch.WordTrace tailWord_1201772 prefixEnd_1201772 205695557705059098407719 := by
  unfold tailWord_1201772
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916112901096382581107785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29221483868128510108143713 21916112901096382581107785)
  ·
    refine ⟨16437084675822286935830839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21916112901096382581107785 16437084675822286935830839)
    ·
      refine ⟨24655627013733430403746259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16437084675822286935830839 24655627013733430403746259)
      ·
        refine ⟨36983440520600145605619389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24655627013733430403746259 36983440520600145605619389)
        ·
          refine ⟨13868790195225054602107271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36983440520600145605619389 13868790195225054602107271)
          ·
            refine ⟨20803185292837581903160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13868790195225054602107271 20803185292837581903160907)
            ·
              refine ⟨31204777939256372854741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20803185292837581903160907 31204777939256372854741361)
              ·
                refine ⟨23403583454442279641056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31204777939256372854741361 23403583454442279641056021)
                ·
                  refine ⟨1097042974426981858174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23403583454442279641056021 1097042974426981858174501)
                  ·
                    refine ⟨205695557705059098407719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097042974426981858174501 205695557705059098407719)
                    ·
                      rfl

theorem cell23_1201772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_1201772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201772 prefixEnd_1201772 := by exact prefixLift 1201772
  have htrace : WordTrace (prefixWord ++ tailWord_1201772) baseStart_1201772 baseEnd_1201772 := by
    simpa [prefixWord, tailWord_1201772, baseEnd_1201772] using wordTrace_append hprefix tailTrace_1201772
  have hstable : (prefixWord ++ tailWord_1201772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201772).length < 2 ^ (prefixWord ++ tailWord_1201772).sum := by decide
  have hdescent : baseEnd_1201772 < baseStart_1201772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201792 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1201792 : Nat := 118140960795 + 1201792 * 2 ^ 59
def prefixEnd_1201792 : Nat := 4983230072969 + 3 ^ 40 * 1201792 * 2
def baseEnd_1201792 : Nat := 617096942728267216973065

theorem tailTrace_1201792 : CollatzResearch.WordTrace tailWord_1201792 prefixEnd_1201792 617096942728267216973065 := by
  unfold tailWord_1201792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916477631060154288971815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29221970174746872385295753 21916477631060154288971815)
  ·
    refine ⟨32874716446590231433457723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21916477631060154288971815 32874716446590231433457723)
    ·
      refine ⟨49312074669885347150186585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32874716446590231433457723 49312074669885347150186585)
      ·
        refine ⟨36984056002414010362639939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49312074669885347150186585 36984056002414010362639939)
        ·
          refine ⟨55476084003621015543959909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36984056002414010362639939 55476084003621015543959909)
          ·
            refine ⟨10401765750678940414492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55476084003621015543959909 10401765750678940414492483)
            ·
              refine ⟨15602648626018410621738725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10401765750678940414492483 15602648626018410621738725)
              ·
                refine ⟨2925496617378451991576011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15602648626018410621738725 2925496617378451991576011)
                ·
                  refine ⟨4388244926067677987364017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925496617378451991576011 4388244926067677987364017)
                  ·
                    refine ⟨3291183694550758490523013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4388244926067677987364017 3291183694550758490523013)
                    ·
                      refine ⟨617096942728267216973065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3291183694550758490523013 617096942728267216973065)
                      ·
                        rfl

theorem cell23_1201792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1201792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201792 prefixEnd_1201792 := by exact prefixLift 1201792
  have htrace : WordTrace (prefixWord ++ tailWord_1201792) baseStart_1201792 baseEnd_1201792 := by
    simpa [prefixWord, tailWord_1201792, baseEnd_1201792] using wordTrace_append hprefix tailTrace_1201792
  have hstable : (prefixWord ++ tailWord_1201792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201792).length < 2 ^ (prefixWord ++ tailWord_1201792).sum := by decide
  have hdescent : baseEnd_1201792 < baseStart_1201792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201796 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1201796 : Nat := 118140960795 + 1201796 * 2 ^ 59
def prefixEnd_1201796 : Nat := 4983230072969 + 3 ^ 40 * 1201796 * 2
def baseEnd_1201796 : Nat := 617098996650885201323047

theorem tailTrace_1201796 : CollatzResearch.WordTrace tailWord_1201796 prefixEnd_1201796 617098996650885201323047 := by
  unfold tailWord_1201796
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916550577052908630544621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29222067436070544840726161 21916550577052908630544621)
  ·
    refine ⟨8218706466394840736454233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21916550577052908630544621 8218706466394840736454233)
    ·
      refine ⟨6164029849796130552340675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8218706466394840736454233 6164029849796130552340675)
      ·
        refine ⟨9246044774694195828511013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6164029849796130552340675 9246044774694195828511013)
        ·
          refine ⟨1733633395255161717845815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9246044774694195828511013 1733633395255161717845815)
          ·
            refine ⟨2600450092882742576768723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733633395255161717845815 2600450092882742576768723)
            ·
              refine ⟨3900675139324113865153085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600450092882742576768723 3900675139324113865153085)
              ·
                refine ⟨1462753177246542699432407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3900675139324113865153085 1462753177246542699432407)
                ·
                  refine ⟨2194129765869814049148611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462753177246542699432407 2194129765869814049148611)
                  ·
                    refine ⟨3291194648804721073722917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194129765869814049148611 3291194648804721073722917)
                    ·
                      refine ⟨617098996650885201323047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3291194648804721073722917 617098996650885201323047)
                      ·
                        rfl

theorem cell23_1201796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1201796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201796 prefixEnd_1201796 := by exact prefixLift 1201796
  have htrace : WordTrace (prefixWord ++ tailWord_1201796) baseStart_1201796 baseEnd_1201796 := by
    simpa [prefixWord, tailWord_1201796, baseEnd_1201796] using wordTrace_append hprefix tailTrace_1201796
  have hstable : (prefixWord ++ tailWord_1201796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201796).length < 2 ^ (prefixWord ++ tailWord_1201796).sum := by decide
  have hdescent : baseEnd_1201796 < baseStart_1201796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201802 : List Nat := [3, 1, 2, 3, 2, 2, 10]
def baseStart_1201802 : Nat := 118140960795 + 1201802 * 2 ^ 59
def prefixEnd_1201802 : Nat := 4983230072969 + 3 ^ 40 * 1201802 * 2
def baseEnd_1201802 : Nat := 7618544167096446640099

theorem tailTrace_1201802 : CollatzResearch.WordTrace tailWord_1201802 prefixEnd_1201802 7618544167096446640099 := by
  unfold tailWord_1201802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958329998021020071451915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29222213328056053523871773 10958329998021020071451915)
  ·
    refine ⟨16437494997031530107177873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958329998021020071451915 16437494997031530107177873)
    ·
      refine ⟨12328121247773647580383405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16437494997031530107177873 12328121247773647580383405)
      ·
        refine ⟨4623045467915117842643777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12328121247773647580383405 4623045467915117842643777)
        ·
          refine ⟨3467284100936338381982833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4623045467915117842643777 3467284100936338381982833)
          ·
            refine ⟨2600463075702253786487125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3467284100936338381982833 2600463075702253786487125)
            ·
              refine ⟨7618544167096446640099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2600463075702253786487125 7618544167096446640099)
              ·
                rfl

theorem cell23_1201802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 10].length) (baseStart_1201802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201802 prefixEnd_1201802 := by exact prefixLift 1201802
  have htrace : WordTrace (prefixWord ++ tailWord_1201802) baseStart_1201802 baseEnd_1201802 := by
    simpa [prefixWord, tailWord_1201802, baseEnd_1201802] using wordTrace_append hprefix tailTrace_1201802
  have hstable : (prefixWord ++ tailWord_1201802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201802).length < 2 ^ (prefixWord ++ tailWord_1201802).sum := by decide
  have hdescent : baseEnd_1201802 < baseStart_1201802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201806 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_1201806 : Nat := 118140960795 + 1201806 * 2 ^ 59
def prefixEnd_1201806 : Nat := 4983230072969 + 3 ^ 40 * 1201806 * 2
def baseEnd_1201806 : Nat := 205701377152476720732667

theorem tailTrace_1201806 : CollatzResearch.WordTrace tailWord_1201806 prefixEnd_1201806 205701377152476720732667 := by
  unfold tailWord_1201806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479183235508698621119159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29222310589379725979302181 5479183235508698621119159)
  ·
    refine ⟨8218774853263047931678739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479183235508698621119159 8218774853263047931678739)
    ·
      refine ⟨12328162279894571897518109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218774853263047931678739 12328162279894571897518109)
      ·
        refine ⟨4623060854960464461569291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12328162279894571897518109 4623060854960464461569291)
        ·
          refine ⟨6934591282440696692353937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623060854960464461569291 6934591282440696692353937)
          ·
            refine ⟨5200943461830522519265453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6934591282440696692353937 5200943461830522519265453)
            ·
              refine ⟨1950353798186445944724545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5200943461830522519265453 1950353798186445944724545)
              ·
                refine ⟨1462765348639834458543409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950353798186445944724545 1462765348639834458543409)
                ·
                  refine ⟨1097074011479875843907557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462765348639834458543409 1097074011479875843907557)
                  ·
                    refine ⟨205701377152476720732667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097074011479875843907557 205701377152476720732667)
                    ·
                      rfl

theorem cell23_1201806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_1201806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201806 prefixEnd_1201806 := by exact prefixLift 1201806
  have htrace : WordTrace (prefixWord ++ tailWord_1201806) baseStart_1201806 baseEnd_1201806 := by
    simpa [prefixWord, tailWord_1201806, baseEnd_1201806] using wordTrace_append hprefix tailTrace_1201806
  have hstable : (prefixWord ++ tailWord_1201806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201806).length < 2 ^ (prefixWord ++ tailWord_1201806).sum := by decide
  have hdescent : baseEnd_1201806 < baseStart_1201806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201823 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 6]
def baseStart_1201823 : Nat := 118140960795 + 1201823 * 2 ^ 59
def prefixEnd_1201823 : Nat := 4983230072969 + 3 ^ 40 * 1201823 * 2
def baseEnd_1201823 : Nat := 205704286876185531895141

theorem tailTrace_1201823 : CollatzResearch.WordTrace tailWord_1201823 prefixEnd_1201823 205704286876185531895141 := by
  unfold tailWord_1201823
  simp only [CollatzResearch.WordTrace]
  refine ⟨43834085925008000872322123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29222723950005333914881415 43834085925008000872322123)
  ·
    refine ⟨65751128887512001308483185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43834085925008000872322123 65751128887512001308483185)
    ·
      refine ⟨49313346665634000981362389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65751128887512001308483185 49313346665634000981362389)
      ·
        refine ⟨1155781562475796898000681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49313346665634000981362389 1155781562475796898000681)
        ·
          refine ⟨866836171856847673500511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155781562475796898000681 866836171856847673500511)
          ·
            refine ⟨1300254257785271510250767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866836171856847673500511 1300254257785271510250767)
            ·
              refine ⟨1950381386677907265376151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300254257785271510250767 1950381386677907265376151)
              ·
                refine ⟨2925572080016860898064227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950381386677907265376151 2925572080016860898064227)
                ·
                  refine ⟨4388358120025291347096341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925572080016860898064227 4388358120025291347096341)
                  ·
                    refine ⟨205704286876185531895141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4388358120025291347096341 205704286876185531895141)
                    ·
                      rfl

theorem cell23_1201823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_1201823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201823 prefixEnd_1201823 := by exact prefixLift 1201823
  have htrace : WordTrace (prefixWord ++ tailWord_1201823) baseStart_1201823 baseEnd_1201823 := by
    simpa [prefixWord, tailWord_1201823, baseEnd_1201823] using wordTrace_append hprefix tailTrace_1201823
  have hstable : (prefixWord ++ tailWord_1201823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201823).length < 2 ^ (prefixWord ++ tailWord_1201823).sum := by decide
  have hdescent : baseEnd_1201823 < baseStart_1201823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201826 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1201826 : Nat := 118140960795 + 1201826 * 2 ^ 59
def prefixEnd_1201826 : Nat := 4983230072969 + 3 ^ 40 * 1201826 * 2
def baseEnd_1201826 : Nat := 617114401070520083947909

theorem tailTrace_1201826 : CollatzResearch.WordTrace tailWord_1201826 prefixEnd_1201826 617114401070520083947909 := by
  unfold tailWord_1201826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958548835999283096170333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29222796895998088256454221 10958548835999283096170333)
  ·
    refine ⟨4109455813499731161063875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10958548835999283096170333 4109455813499731161063875)
    ·
      refine ⟨6164183720249596741595813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109455813499731161063875 6164183720249596741595813)
      ·
        refine ⟨1155784447546799389049215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6164183720249596741595813 1155784447546799389049215)
        ·
          refine ⟨1733676671320199083573823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155784447546799389049215 1733676671320199083573823)
          ·
            refine ⟨2600515006980298625360735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733676671320199083573823 2600515006980298625360735)
            ·
              refine ⟨3900772510470447938041103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600515006980298625360735 3900772510470447938041103)
              ·
                refine ⟨5851158765705671907061655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900772510470447938041103 5851158765705671907061655)
                ·
                  refine ⟨8776738148558507860592483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5851158765705671907061655 8776738148558507860592483)
                  ·
                    refine ⟨13165107222837761790888725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8776738148558507860592483 13165107222837761790888725)
                    ·
                      refine ⟨617114401070520083947909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13165107222837761790888725 617114401070520083947909)
                      ·
                        rfl

theorem cell23_1201826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1201826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201826 prefixEnd_1201826 := by exact prefixLift 1201826
  have htrace : WordTrace (prefixWord ++ tailWord_1201826) baseStart_1201826 baseEnd_1201826 := by
    simpa [prefixWord, tailWord_1201826, baseEnd_1201826] using wordTrace_append hprefix tailTrace_1201826
  have hstable : (prefixWord ++ tailWord_1201826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201826).length < 2 ^ (prefixWord ++ tailWord_1201826).sum := by decide
  have hdescent : baseEnd_1201826 < baseStart_1201826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201829 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_1201829 : Nat := 118140960795 + 1201829 * 2 ^ 59
def prefixEnd_1201829 : Nat := 4983230072969 + 3 ^ 40 * 1201829 * 2
def baseEnd_1201829 : Nat := 617115941512483572210395

theorem tailTrace_1201829 : CollatzResearch.WordTrace tailWord_1201829 prefixEnd_1201829 617115941512483572210395 := by
  unfold tailWord_1201829
  simp only [CollatzResearch.WordTrace]
  refine ⟨43834304762986263897040541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29222869841990842598027027 43834304762986263897040541)
  ·
    refine ⟨16437864286119848961390203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43834304762986263897040541 16437864286119848961390203)
    ·
      refine ⟨24656796429179773442085305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16437864286119848961390203 24656796429179773442085305)
      ·
        refine ⟨18492597321884830081563979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24656796429179773442085305 18492597321884830081563979)
        ·
          refine ⟨27738895982827245122345969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18492597321884830081563979 27738895982827245122345969)
          ·
            refine ⟨20804171987120433841759477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27738895982827245122345969 20804171987120433841759477)
            ·
              refine ⟨1950391123792540672664951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20804171987120433841759477 1950391123792540672664951)
              ·
                refine ⟨2925586685688811008997427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950391123792540672664951 2925586685688811008997427)
                ·
                  refine ⟨4388380028533216513496141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2925586685688811008997427 4388380028533216513496141)
                  ·
                    refine ⟨1645642510699956192561053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4388380028533216513496141 1645642510699956192561053)
                    ·
                      refine ⟨617115941512483572210395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1645642510699956192561053 617115941512483572210395)
                      ·
                        rfl

theorem cell23_1201829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_1201829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201829 prefixEnd_1201829 := by exact prefixLift 1201829
  have htrace : WordTrace (prefixWord ++ tailWord_1201829) baseStart_1201829 baseEnd_1201829 := by
    simpa [prefixWord, tailWord_1201829, baseEnd_1201829] using wordTrace_append hprefix tailTrace_1201829
  have hstable : (prefixWord ++ tailWord_1201829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201829).length < 2 ^ (prefixWord ++ tailWord_1201829).sum := by decide
  have hdescent : baseEnd_1201829 < baseStart_1201829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201842 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1201842 : Nat := 118140960795 + 1201842 * 2 ^ 59
def prefixEnd_1201842 : Nat := 4983230072969 + 3 ^ 40 * 1201842 * 2
def baseEnd_1201842 : Nat := 617122616760992021347835

theorem tailTrace_1201842 : CollatzResearch.WordTrace tailWord_1201842 prefixEnd_1201842 617122616760992021347835 := by
  unfold tailWord_1201842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958694727984791779315945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29223185941292778078175853 10958694727984791779315945)
  ·
    refine ⟨8219021045988593834486959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10958694727984791779315945 8219021045988593834486959)
    ·
      refine ⟨12328531568982890751730439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219021045988593834486959 12328531568982890751730439)
      ·
        refine ⟨18492797353474336127595659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12328531568982890751730439 18492797353474336127595659)
        ·
          refine ⟨27739196030211504191393489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18492797353474336127595659 27739196030211504191393489)
          ·
            refine ⟨20804397022658628143545117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27739196030211504191393489 20804397022658628143545117)
            ·
              refine ⟨7801648883496985553829419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20804397022658628143545117 7801648883496985553829419)
              ·
                refine ⟨11702473325245478330744129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801648883496985553829419 11702473325245478330744129)
                ·
                  refine ⟨8776854993934108748058097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11702473325245478330744129 8776854993934108748058097)
                  ·
                    refine ⟨6582641245450581561043573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8776854993934108748058097 6582641245450581561043573)
                    ·
                      refine ⟨617122616760992021347835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6582641245450581561043573 617122616760992021347835)
                      ·
                        rfl

theorem cell23_1201842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1201842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201842 prefixEnd_1201842 := by exact prefixLift 1201842
  have htrace : WordTrace (prefixWord ++ tailWord_1201842) baseStart_1201842 baseEnd_1201842 := by
    simpa [prefixWord, tailWord_1201842, baseEnd_1201842] using wordTrace_append hprefix tailTrace_1201842
  have hstable : (prefixWord ++ tailWord_1201842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201842).length < 2 ^ (prefixWord ++ tailWord_1201842).sum := by decide
  have hdescent : baseEnd_1201842 < baseStart_1201842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201856 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2]
def baseStart_1201856 : Nat := 118140960795 + 1201856 * 2 ^ 59
def prefixEnd_1201856 : Nat := 4983230072969 + 3 ^ 40 * 1201856 * 2
def baseEnd_1201856 : Nat := 617129805490154966572771

theorem tailTrace_1201856 : CollatzResearch.WordTrace tailWord_1201856 prefixEnd_1201856 617129805490154966572771 := by
  unfold tailWord_1201856
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917644766944223754136711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29223526355925631672182281 21917644766944223754136711)
  ·
    refine ⟨32876467150416335631205067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917644766944223754136711 32876467150416335631205067)
    ·
      refine ⟨49314700725624503446807601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32876467150416335631205067 49314700725624503446807601)
      ·
        refine ⟨36986025544218377585105701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49314700725624503446807601 36986025544218377585105701)
        ·
          refine ⟨6934879789540945797207319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36986025544218377585105701 6934879789540945797207319)
          ·
            refine ⟨10402319684311418695810979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6934879789540945797207319 10402319684311418695810979)
            ·
              refine ⟨15603479526467128043716469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10402319684311418695810979 15603479526467128043716469)
              ·
                refine ⟨1462826205606293254098419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15603479526467128043716469 1462826205606293254098419)
                ·
                  refine ⟨2194239308409439881147629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462826205606293254098419 2194239308409439881147629)
                  ·
                    refine ⟨822839740653539955430361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2194239308409439881147629 822839740653539955430361)
                    ·
                      refine ⟨617129805490154966572771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822839740653539955430361 617129805490154966572771)
                      ·
                        rfl

theorem cell23_1201856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_1201856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201856 prefixEnd_1201856 := by exact prefixLift 1201856
  have htrace : WordTrace (prefixWord ++ tailWord_1201856) baseStart_1201856 baseEnd_1201856 := by
    simpa [prefixWord, tailWord_1201856, baseEnd_1201856] using wordTrace_append hprefix tailTrace_1201856
  have hstable : (prefixWord ++ tailWord_1201856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201856).length < 2 ^ (prefixWord ++ tailWord_1201856).sum := by decide
  have hdescent : baseEnd_1201856 < baseStart_1201856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201892 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1201892 : Nat := 118140960795 + 1201892 * 2 ^ 59
def prefixEnd_1201892 : Nat := 4983230072969 + 3 ^ 40 * 1201892 * 2
def baseEnd_1201892 : Nat := 68572032310412980635845

theorem tailTrace_1201892 : CollatzResearch.WordTrace tailWord_1201892 prefixEnd_1201892 68572032310412980635845 := by
  unfold tailWord_1201892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918301280879012828291965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29224401707838683771055953 21918301280879012828291965)
  ·
    refine ⟨8219362980329629810609487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21918301280879012828291965 8219362980329629810609487)
    ·
      refine ⟨12329044470494444715914231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219362980329629810609487 12329044470494444715914231)
      ·
        refine ⟨18493566705741667073871347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12329044470494444715914231 18493566705741667073871347)
        ·
          refine ⟨27740350058612500610807021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18493566705741667073871347 27740350058612500610807021)
          ·
            refine ⟨10402631271979687729052633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27740350058612500610807021 10402631271979687729052633)
            ·
              refine ⟨7801973453984765796789475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10402631271979687729052633 7801973453984765796789475)
              ·
                refine ⟨11702960180977148695184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7801973453984765796789475 11702960180977148695184213)
                ·
                  refine ⟨68572032310412980635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11702960180977148695184213 68572032310412980635845)
                  ·
                    rfl

theorem cell23_1201892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1201892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201892 prefixEnd_1201892 := by exact prefixLift 1201892
  have htrace : WordTrace (prefixWord ++ tailWord_1201892) baseStart_1201892 baseEnd_1201892 := by
    simpa [prefixWord, tailWord_1201892, baseEnd_1201892] using wordTrace_append hprefix tailTrace_1201892
  have hstable : (prefixWord ++ tailWord_1201892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201892).length < 2 ^ (prefixWord ++ tailWord_1201892).sum := by decide
  have hdescent : baseEnd_1201892 < baseStart_1201892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201956 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_1201956 : Nat := 118140960795 + 1201956 * 2 ^ 59
def prefixEnd_1201956 : Nat := 4983230072969 + 3 ^ 40 * 1201956 * 2
def baseEnd_1201956 : Nat := 205727051185201525107437

theorem tailTrace_1201956 : CollatzResearch.WordTrace tailWord_1201956 prefixEnd_1201956 205727051185201525107437 := by
  unfold tailWord_1201956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21919468416763082293456861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29225957889017443057942481 21919468416763082293456861)
  ·
    refine ⟨8219800656286155860046323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21919468416763082293456861 8219800656286155860046323)
    ·
      refine ⟨12329700984429233790069485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219800656286155860046323 12329700984429233790069485)
      ·
        refine ⟨4623637869160962671276057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12329700984429233790069485 4623637869160962671276057)
        ·
          refine ⟨3467728401870722003457043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4623637869160962671276057 3467728401870722003457043)
          ·
            refine ⟨5201592602806083005185565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467728401870722003457043 5201592602806083005185565)
            ·
              refine ⟨1950597226052281126944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5201592602806083005185565 1950597226052281126944587)
              ·
                refine ⟨2925895839078421690416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950597226052281126944587 2925895839078421690416881)
                ·
                  refine ⟨2194421879308816267812661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925895839078421690416881 2194421879308816267812661)
                  ·
                    refine ⟨205727051185201525107437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2194421879308816267812661 205727051185201525107437)
                    ·
                      rfl

theorem cell23_1201956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_1201956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201956 prefixEnd_1201956 := by exact prefixLift 1201956
  have htrace : WordTrace (prefixWord ++ tailWord_1201956) baseStart_1201956 baseEnd_1201956 := by
    simpa [prefixWord, tailWord_1201956, baseEnd_1201956] using wordTrace_append hprefix tailTrace_1201956
  have hstable : (prefixWord ++ tailWord_1201956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201956).length < 2 ^ (prefixWord ++ tailWord_1201956).sum := by decide
  have hdescent : baseEnd_1201956 < baseStart_1201956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201976 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_1201976 : Nat := 118140960795 + 1201976 * 2 ^ 59
def prefixEnd_1201976 : Nat := 4983230072969 + 3 ^ 40 * 1201976 * 2
def baseEnd_1201976 : Nat := 617191423168694497072219

theorem tailTrace_1201976 : CollatzResearch.WordTrace tailWord_1201976 prefixEnd_1201976 617191423168694497072219 := by
  unfold tailWord_1201976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21919833146726854001320891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29226444195635805335094521 21919833146726854001320891)
  ·
    refine ⟨32879749720090281001981337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21919833146726854001320891 32879749720090281001981337)
    ·
      refine ⟨24659812290067710751486003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32879749720090281001981337 24659812290067710751486003)
      ·
        refine ⟨36989718435101566127229005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24659812290067710751486003 36989718435101566127229005)
        ·
          refine ⟨13871144413163087297710877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36989718435101566127229005 13871144413163087297710877)
          ·
            refine ⟨5201679154936157736641579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13871144413163087297710877 5201679154936157736641579)
            ·
              refine ⟨7802518732404236604962369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5201679154936157736641579 7802518732404236604962369)
              ·
                refine ⟨5851889049303177453721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7802518732404236604962369 5851889049303177453721777)
                ·
                  refine ⟨4388916786977383090291333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5851889049303177453721777 4388916786977383090291333)
                  ·
                    refine ⟨822921897558259329429625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4388916786977383090291333 822921897558259329429625)
                    ·
                      refine ⟨617191423168694497072219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822921897558259329429625 617191423168694497072219)
                      ·
                        rfl

theorem cell23_1201976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_1201976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201976 prefixEnd_1201976 := by exact prefixLift 1201976
  have htrace : WordTrace (prefixWord ++ tailWord_1201976) baseStart_1201976 baseEnd_1201976 := by
    simpa [prefixWord, tailWord_1201976, baseEnd_1201976] using wordTrace_append hprefix tailTrace_1201976
  have hstable : (prefixWord ++ tailWord_1201976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201976).length < 2 ^ (prefixWord ++ tailWord_1201976).sum := by decide
  have hdescent : baseEnd_1201976 < baseStart_1201976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202009 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_1202009 : Nat := 118140960795 + 1202009 * 2 ^ 59
def prefixEnd_1202009 : Nat := 4983230072969 + 3 ^ 40 * 1202009 * 2
def baseEnd_1202009 : Nat := 617208368030292867959567

theorem tailTrace_1202009 : CollatzResearch.WordTrace tailWord_1202009 prefixEnd_1202009 617208368030292867959567 := by
  unfold tailWord_1202009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43840869902334154638593081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29227246601556103092395387 43840869902334154638593081)
  ·
    refine ⟨32880652426750615978944811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43840869902334154638593081 32880652426750615978944811)
    ·
      refine ⟨49320978640125923968417217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32880652426750615978944811 49320978640125923968417217)
      ·
        refine ⟨36990733980094442976312913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49320978640125923968417217 36990733980094442976312913)
        ·
          refine ⟨27743050485070832232234685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36990733980094442976312913 27743050485070832232234685)
          ·
            refine ⟨10403643931901562087088007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27743050485070832232234685 10403643931901562087088007)
            ·
              refine ⟨15605465897852343130632011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10403643931901562087088007 15605465897852343130632011)
              ·
                refine ⟨23408198846778514695948017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15605465897852343130632011 23408198846778514695948017)
                ·
                  refine ⟨17556149135083886021961013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23408198846778514695948017 17556149135083886021961013)
                  ·
                    refine ⟨1645888981414114314558845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17556149135083886021961013 1645888981414114314558845)
                    ·
                      refine ⟨617208368030292867959567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1645888981414114314558845 617208368030292867959567)
                      ·
                        rfl

theorem cell23_1202009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_1202009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202009 prefixEnd_1202009 := by exact prefixLift 1202009
  have htrace : WordTrace (prefixWord ++ tailWord_1202009) baseStart_1202009 baseEnd_1202009 := by
    simpa [prefixWord, tailWord_1202009, baseEnd_1202009] using wordTrace_append hprefix tailTrace_1202009
  have hstable : (prefixWord ++ tailWord_1202009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202009).length < 2 ^ (prefixWord ++ tailWord_1202009).sum := by decide
  have hdescent : baseEnd_1202009 < baseStart_1202009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202059 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 6]
def baseStart_1202059 : Nat := 118140960795 + 1202059 * 2 ^ 59
def prefixEnd_1202059 : Nat := 4983230072969 + 3 ^ 40 * 1202059 * 2
def baseEnd_1202059 : Nat := 205744680687672557444779

theorem tailTrace_1202059 : CollatzResearch.WordTrace tailWord_1202059 prefixEnd_1202059 205744680687672557444779 := by
  unfold tailWord_1202059
  simp only [CollatzResearch.WordTrace]
  refine ⟨43842693552153013177913231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29228462368102008785275487 43842693552153013177913231)
  ·
    refine ⟨65764040328229519766869847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43842693552153013177913231 65764040328229519766869847)
    ·
      refine ⟨98646060492344279650304771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65764040328229519766869847 98646060492344279650304771)
      ·
        refine ⟨147969090738516419475457157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98646060492344279650304771 147969090738516419475457157)
        ·
          refine ⟨27744204513471828651648217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147969090738516419475457157 27744204513471828651648217)
          ·
            refine ⟨20808153385103871488736163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27744204513471828651648217 20808153385103871488736163)
            ·
              refine ⟨31212230077655807233104245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20808153385103871488736163 31212230077655807233104245)
              ·
                refine ⟨2926146569780231928103523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31212230077655807233104245 2926146569780231928103523)
                ·
                  refine ⟨4389219854670347892155285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926146569780231928103523 4389219854670347892155285)
                  ·
                    refine ⟨205744680687672557444779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4389219854670347892155285 205744680687672557444779)
                    ·
                      rfl

theorem cell23_1202059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_1202059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202059 prefixEnd_1202059 := by exact prefixLift 1202059
  have htrace : WordTrace (prefixWord ++ tailWord_1202059) baseStart_1202059 baseEnd_1202059 := by
    simpa [prefixWord, tailWord_1202059, baseEnd_1202059] using wordTrace_append hprefix tailTrace_1202059
  have hstable : (prefixWord ++ tailWord_1202059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202059).length < 2 ^ (prefixWord ++ tailWord_1202059).sum := by decide
  have hdescent : baseEnd_1202059 < baseStart_1202059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202076 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1202076 : Nat := 118140960795 + 1202076 * 2 ^ 59
def prefixEnd_1202076 : Nat := 4983230072969 + 3 ^ 40 * 1202076 * 2
def baseEnd_1202076 : Nat := 205747590411381368607253

theorem tailTrace_1202076 : CollatzResearch.WordTrace tailWord_1202076 prefixEnd_1202076 205747590411381368607253 := by
  unfold tailWord_1202076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921656796545712540641041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29228875728727616720854721 21921656796545712540641041)
  ·
    refine ⟨16441242597409284405480781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21921656796545712540641041 16441242597409284405480781)
    ·
      refine ⟨6165465974028481652055293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16441242597409284405480781 6165465974028481652055293)
      ·
        refine ⟨2312049740260680619520735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6165465974028481652055293 2312049740260680619520735)
        ·
          refine ⟨3468074610391020929281103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312049740260680619520735 3468074610391020929281103)
          ·
            refine ⟨5202111915586531393921655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468074610391020929281103 5202111915586531393921655)
            ·
              refine ⟨7803167873379797090882483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202111915586531393921655 7803167873379797090882483)
              ·
                refine ⟨11704751810069695636323725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803167873379797090882483 11704751810069695636323725)
                ·
                  refine ⟨4389281928776135863621397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11704751810069695636323725 4389281928776135863621397)
                  ·
                    refine ⟨205747590411381368607253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4389281928776135863621397 205747590411381368607253)
                    ·
                      rfl

theorem cell23_1202076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1202076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202076 prefixEnd_1202076 := by exact prefixLift 1202076
  have htrace : WordTrace (prefixWord ++ tailWord_1202076) baseStart_1202076 baseEnd_1202076 := by
    simpa [prefixWord, tailWord_1202076, baseEnd_1202076] using wordTrace_append hprefix tailTrace_1202076
  have hstable : (prefixWord ++ tailWord_1202076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202076).length < 2 ^ (prefixWord ++ tailWord_1202076).sum := by decide
  have hdescent : baseEnd_1202076 < baseStart_1202076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202119 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 7]
def baseStart_1202119 : Nat := 118140960795 + 1202119 * 2 ^ 59
def prefixEnd_1202119 : Nat := 4983230072969 + 3 ^ 40 * 1202119 * 2
def baseEnd_1202119 : Nat := 205754950300762479194687

theorem tailTrace_1202119 : CollatzResearch.WordTrace tailWord_1202119 prefixEnd_1202119 205754950300762479194687 := by
  unfold tailWord_1202119
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844881931935643425097411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29229921287957095616731607 43844881931935643425097411)
  ·
    refine ⟨65767322897903465137646117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43844881931935643425097411 65767322897903465137646117)
    ·
      refine ⟨12331373043356899713308647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65767322897903465137646117 12331373043356899713308647)
      ·
        refine ⟨18497059565035349569962971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12331373043356899713308647 18497059565035349569962971)
        ·
          refine ⟨27745589347553024354944457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18497059565035349569962971 27745589347553024354944457)
          ·
            refine ⟨20809192010664768266208343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27745589347553024354944457 20809192010664768266208343)
            ·
              refine ⟨31213788015997152399312515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20809192010664768266208343 31213788015997152399312515)
              ·
                refine ⟨46820682023995728598968773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31213788015997152399312515 46820682023995728598968773)
                ·
                  refine ⟨8778877879499199112306645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46820682023995728598968773 8778877879499199112306645)
                  ·
                    refine ⟨205754950300762479194687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8778877879499199112306645 205754950300762479194687)
                    ·
                      rfl

theorem cell23_1202119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_1202119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202119 prefixEnd_1202119 := by exact prefixLift 1202119
  have htrace : WordTrace (prefixWord ++ tailWord_1202119) baseStart_1202119 baseEnd_1202119 := by
    simpa [prefixWord, tailWord_1202119, baseEnd_1202119] using wordTrace_append hprefix tailTrace_1202119
  have hstable : (prefixWord ++ tailWord_1202119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202119).length < 2 ^ (prefixWord ++ tailWord_1202119).sum := by decide
  have hdescent : baseEnd_1202119 < baseStart_1202119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202133 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1202133 : Nat := 118140960795 + 1202133 * 2 ^ 59
def prefixEnd_1202133 : Nat := 4983230072969 + 3 ^ 40 * 1202133 * 2
def baseEnd_1202133 : Nat := 617272039631450382808997

theorem tailTrace_1202133 : CollatzResearch.WordTrace tailWord_1202133 prefixEnd_1202133 617272039631450382808997 := by
  unfold tailWord_1202133
  simp only [CollatzResearch.WordTrace]
  refine ⟨43845392553884923816107053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29230261702589949210738035 43845392553884923816107053)
  ·
    refine ⟨16442022207706846431040145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43845392553884923816107053 16442022207706846431040145)
    ·
      refine ⟨12331516655780134823280109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16442022207706846431040145 12331516655780134823280109)
      ·
        refine ⟨4624318745917550558730041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12331516655780134823280109 4624318745917550558730041)
        ·
          refine ⟨3468239059438162919047531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4624318745917550558730041 3468239059438162919047531)
          ·
            refine ⟨5202358589157244378571297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468239059438162919047531 5202358589157244378571297)
            ·
              refine ⟨3901768941867933283928473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202358589157244378571297 3901768941867933283928473)
              ·
                refine ⟨2926326706400949962946355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3901768941867933283928473 2926326706400949962946355)
                ·
                  refine ⟨4389490059601424944419533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926326706400949962946355 4389490059601424944419533)
                  ·
                    refine ⟨1646058772350534354157325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4389490059601424944419533 1646058772350534354157325)
                    ·
                      refine ⟨617272039631450382808997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646058772350534354157325 617272039631450382808997)
                      ·
                        rfl

theorem cell23_1202133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1202133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202133 prefixEnd_1202133 := by exact prefixLift 1202133
  have htrace : WordTrace (prefixWord ++ tailWord_1202133) baseStart_1202133 baseEnd_1202133 := by
    simpa [prefixWord, tailWord_1202133, baseEnd_1202133] using wordTrace_append hprefix tailTrace_1202133
  have hstable : (prefixWord ++ tailWord_1202133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202133).length < 2 ^ (prefixWord ++ tailWord_1202133).sum := by decide
  have hdescent : baseEnd_1202133 < baseStart_1202133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202134 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1202134 : Nat := 118140960795 + 1202134 * 2 ^ 59
def prefixEnd_1202134 : Nat := 4983230072969 + 3 ^ 40 * 1202134 * 2
def baseEnd_1202134 : Nat := 617272553112104878896493

theorem tailTrace_1202134 : CollatzResearch.WordTrace tailWord_1202134 prefixEnd_1202134 617272553112104878896493 := by
  unfold tailWord_1202134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740339314180081311680841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29230286017920867324595637 2740339314180081311680841)
  ·
    refine ⟨2055254485635060983760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2740339314180081311680841 2055254485635060983760631)
    ·
      refine ⟨3082881728452591475640947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055254485635060983760631 3082881728452591475640947)
      ·
        refine ⟨4624322592678887213461421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082881728452591475640947 4624322592678887213461421)
        ·
          refine ⟨1734120972254582705048033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4624322592678887213461421 1734120972254582705048033)
          ·
            refine ⟨1300590729190937028786025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734120972254582705048033 1300590729190937028786025)
            ·
              refine ⟨975443046893202771589519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300590729190937028786025 975443046893202771589519)
              ·
                refine ⟨1463164570339804157384279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975443046893202771589519 1463164570339804157384279)
                ·
                  refine ⟨2194746855509706236076419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463164570339804157384279 2194746855509706236076419)
                  ·
                    refine ⟨3292120283264559354114629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194746855509706236076419 3292120283264559354114629)
                    ·
                      refine ⟨617272553112104878896493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3292120283264559354114629 617272553112104878896493)
                      ·
                        rfl

theorem cell23_1202134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1202134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202134 prefixEnd_1202134 := by exact prefixLift 1202134
  have htrace : WordTrace (prefixWord ++ tailWord_1202134) baseStart_1202134 baseEnd_1202134 := by
    simpa [prefixWord, tailWord_1202134, baseEnd_1202134] using wordTrace_append hprefix tailTrace_1202134
  have hstable : (prefixWord ++ tailWord_1202134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202134).length < 2 ^ (prefixWord ++ tailWord_1202134).sum := by decide
  have hdescent : baseEnd_1202134 < baseStart_1202134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202137 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 1, 2, 3]
def baseStart_1202137 : Nat := 118140960795 + 1202137 * 2 ^ 59
def prefixEnd_1202137 : Nat := 4983230072969 + 3 ^ 40 * 1202137 * 2
def baseEnd_1202137 : Nat := 617274093554068367158979

theorem tailTrace_1202137 : CollatzResearch.WordTrace tailWord_1202137 prefixEnd_1202137 617274093554068367158979 := by
  unfold tailWord_1202137
  simp only [CollatzResearch.WordTrace]
  refine ⟨43845538445870432499252665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29230358963913621666168443 43845538445870432499252665)
  ·
    refine ⟨32884153834402824374439499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43845538445870432499252665 32884153834402824374439499)
    ·
      refine ⟨49326230751604236561659249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32884153834402824374439499 49326230751604236561659249)
      ·
        refine ⟨36994673063703177421244437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49326230751604236561659249 36994673063703177421244437)
        ·
          refine ⟨1734125299861086441620833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36994673063703177421244437 1734125299861086441620833)
          ·
            refine ⟨1300593974895814831215625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734125299861086441620833 1300593974895814831215625)
            ·
              refine ⟨975445481171861123411719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300593974895814831215625 975445481171861123411719)
              ·
                refine ⟨1463168221757791685117579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975445481171861123411719 1463168221757791685117579)
                ·
                  refine ⟨2194752332636687527676369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463168221757791685117579 2194752332636687527676369)
                  ·
                    refine ⟨1646064249477515645757277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2194752332636687527676369 1646064249477515645757277)
                    ·
                      refine ⟨617274093554068367158979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646064249477515645757277 617274093554068367158979)
                      ·
                        rfl

theorem cell23_1202137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_1202137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202137 prefixEnd_1202137 := by exact prefixLift 1202137
  have htrace : WordTrace (prefixWord ++ tailWord_1202137) baseStart_1202137 baseEnd_1202137 := by
    simpa [prefixWord, tailWord_1202137, baseEnd_1202137] using wordTrace_append hprefix tailTrace_1202137
  have hstable : (prefixWord ++ tailWord_1202137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202137).length < 2 ^ (prefixWord ++ tailWord_1202137).sum := by decide
  have hdescent : baseEnd_1202137 < baseStart_1202137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202140 : List Nat := [2, 2, 6, 1, 1, 1, 10]
def baseStart_1202140 : Nat := 118140960795 + 1202140 * 2 ^ 59
def prefixEnd_1202140 : Nat := 4983230072969 + 3 ^ 40 * 1202140 * 2
def baseEnd_1202140 : Nat := 7620686839457183400265

theorem tailTrace_1202140 : CollatzResearch.WordTrace tailWord_1202140 prefixEnd_1202140 7620686839457183400265 := by
  unfold tailWord_1202140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21922823932429782005805937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29230431909906376007741249 21922823932429782005805937)
  ·
    refine ⟨16442117949322336504354453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21922823932429782005805937 16442117949322336504354453)
    ·
      refine ⟨770724278874484523641615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16442117949322336504354453 770724278874484523641615)
      ·
        refine ⟨1156086418311726785462423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770724278874484523641615 1156086418311726785462423)
        ·
          refine ⟨1734129627467590178193635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156086418311726785462423 1734129627467590178193635)
          ·
            refine ⟨2601194441201385267290453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734129627467590178193635 2601194441201385267290453)
            ·
              refine ⟨7620686839457183400265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2601194441201385267290453 7620686839457183400265)
              ·
                rfl

theorem cell23_1202140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 10].length) (baseStart_1202140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202140 prefixEnd_1202140 := by exact prefixLift 1202140
  have htrace : WordTrace (prefixWord ++ tailWord_1202140) baseStart_1202140 baseEnd_1202140 := by
    simpa [prefixWord, tailWord_1202140, baseEnd_1202140] using wordTrace_append hprefix tailTrace_1202140
  have hstable : (prefixWord ++ tailWord_1202140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202140).length < 2 ^ (prefixWord ++ tailWord_1202140).sum := by decide
  have hdescent : baseEnd_1202140 < baseStart_1202140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202190 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1202190 : Nat := 118140960795 + 1202190 * 2 ^ 59
def prefixEnd_1202190 : Nat := 4983230072969 + 3 ^ 40 * 1202190 * 2
def baseEnd_1202190 : Nat := 617301308028756659796235

theorem tailTrace_1202190 : CollatzResearch.WordTrace tailWord_1202190 prefixEnd_1202190 617301308028756659796235 := by
  unfold tailWord_1202190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480933939334802818866503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29231647676452281700621349 5480933939334802818866503)
  ·
    refine ⟨8221400909002204228299755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5480933939334802818866503 8221400909002204228299755)
    ·
      refine ⟨12332101363503306342449633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8221400909002204228299755 12332101363503306342449633)
      ·
        refine ⟨9249076022627479756837225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12332101363503306342449633 9249076022627479756837225)
        ·
          refine ⟨6936807016970609817627919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249076022627479756837225 6936807016970609817627919)
          ·
            refine ⟨10405210525455914726441879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936807016970609817627919 10405210525455914726441879)
            ·
              refine ⟨15607815788183872089662819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10405210525455914726441879 15607815788183872089662819)
              ·
                refine ⟨23411723682275808134494229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15607815788183872089662819 23411723682275808134494229)
                ·
                  refine ⟨1097424547606678506304417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23411723682275808134494229 1097424547606678506304417)
                  ·
                    refine ⟨823068410705008879728313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097424547606678506304417 823068410705008879728313)
                    ·
                      refine ⟨617301308028756659796235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823068410705008879728313 617301308028756659796235)
                      ·
                        rfl

theorem cell23_1202190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1202190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202190 prefixEnd_1202190 := by exact prefixLift 1202190
  have htrace : WordTrace (prefixWord ++ tailWord_1202190) baseStart_1202190 baseEnd_1202190 := by
    simpa [prefixWord, tailWord_1202190, baseEnd_1202190] using wordTrace_append hprefix tailTrace_1202190
  have hstable : (prefixWord ++ tailWord_1202190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202190).length < 2 ^ (prefixWord ++ tailWord_1202190).sum := by decide
  have hdescent : baseEnd_1202190 < baseStart_1202190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202213 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 7]
def baseStart_1202213 : Nat := 118140960795 + 1202213 * 2 ^ 59
def prefixEnd_1202213 : Nat := 4983230072969 + 3 ^ 40 * 1202213 * 2
def baseEnd_1202213 : Nat := 68590346453756674423181

theorem tailTrace_1202213 : CollatzResearch.WordTrace tailWord_1202213 prefixEnd_1202213 68590346453756674423181 := by
  unfold tailWord_1202213
  simp only [CollatzResearch.WordTrace]
  refine ⟨43848310393595097479019293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29232206929063398319346195 43848310393595097479019293)
  ·
    refine ⟨16443116397598161554632235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43848310393595097479019293 16443116397598161554632235)
    ·
      refine ⟨24664674596397242331948353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443116397598161554632235 24664674596397242331948353)
      ·
        refine ⟨18498505947297931748961265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24664674596397242331948353 18498505947297931748961265)
        ·
          refine ⟨13873879460473448811720949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18498505947297931748961265 13873879460473448811720949)
          ·
            refine ⟨1300676199419385826098839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13873879460473448811720949 1300676199419385826098839)
            ·
              refine ⟨1951014299129078739148259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300676199419385826098839 1951014299129078739148259)
              ·
                refine ⟨2926521448693618108722389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951014299129078739148259 2926521448693618108722389)
                ·
                  refine ⟨68590346453756674423181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2926521448693618108722389 68590346453756674423181)
                  ·
                    rfl

theorem cell23_1202213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_1202213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202213 prefixEnd_1202213 := by exact prefixLift 1202213
  have htrace : WordTrace (prefixWord ++ tailWord_1202213) baseStart_1202213 baseEnd_1202213 := by
    simpa [prefixWord, tailWord_1202213, baseEnd_1202213] using wordTrace_append hprefix tailTrace_1202213
  have hstable : (prefixWord ++ tailWord_1202213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202213).length < 2 ^ (prefixWord ++ tailWord_1202213).sum := by decide
  have hdescent : baseEnd_1202213 < baseStart_1202213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202224 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2]
def baseStart_1202224 : Nat := 118140960795 + 1202224 * 2 ^ 59
def prefixEnd_1202224 : Nat := 4983230072969 + 3 ^ 40 * 1202224 * 2
def baseEnd_1202224 : Nat := 617318766371009526771079

theorem tailTrace_1202224 : CollatzResearch.WordTrace tailWord_1202224 prefixEnd_1202224 617318766371009526771079 := by
  unfold tailWord_1202224
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924355798277623178834863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29232474397703497571779817 21924355798277623178834863)
  ·
    refine ⟨32886533697416434768252295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21924355798277623178834863 32886533697416434768252295)
    ·
      refine ⟨49329800546124652152378443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32886533697416434768252295 49329800546124652152378443)
      ·
        refine ⟨73994700819186978228567665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49329800546124652152378443 73994700819186978228567665)
        ·
          refine ⟨55496025614390233671425749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73994700819186978228567665 55496025614390233671425749)
          ·
            refine ⟨1300688100337271101674041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55496025614390233671425749 1300688100337271101674041)
            ·
              refine ⟨975516075252953326255531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300688100337271101674041 975516075252953326255531)
              ·
                refine ⟨1463274112879429989383297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975516075252953326255531 1463274112879429989383297)
                ·
                  refine ⟨1097455584659572492037473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463274112879429989383297 1097455584659572492037473)
                  ·
                    refine ⟨823091688494679369028105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097455584659572492037473 823091688494679369028105)
                    ·
                      refine ⟨617318766371009526771079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823091688494679369028105 617318766371009526771079)
                      ·
                        rfl

theorem cell23_1202224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2].length) (baseStart_1202224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202224 prefixEnd_1202224 := by exact prefixLift 1202224
  have htrace : WordTrace (prefixWord ++ tailWord_1202224) baseStart_1202224 baseEnd_1202224 := by
    simpa [prefixWord, tailWord_1202224, baseEnd_1202224] using wordTrace_append hprefix tailTrace_1202224
  have hstable : (prefixWord ++ tailWord_1202224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202224).length < 2 ^ (prefixWord ++ tailWord_1202224).sum := by decide
  have hdescent : baseEnd_1202224 < baseStart_1202224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202236 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1202236 : Nat := 118140960795 + 1202236 * 2 ^ 59
def prefixEnd_1202236 : Nat := 4983230072969 + 3 ^ 40 * 1202236 * 2
def baseEnd_1202236 : Nat := 617324928138863479821023

theorem tailTrace_1202236 : CollatzResearch.WordTrace tailWord_1202236 prefixEnd_1202236 617324928138863479821023 := by
  unfold tailWord_1202236
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924574636255886203553281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29232766181674514938071041 21924574636255886203553281)
  ·
    refine ⟨16443430977191914652664961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21924574636255886203553281 16443430977191914652664961)
    ·
      refine ⟨12332573232893935989498721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16443430977191914652664961 12332573232893935989498721)
      ·
        refine ⟨9249429924670451992124041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12332573232893935989498721 9249429924670451992124041)
        ·
          refine ⟨6937072443502838994093031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249429924670451992124041 6937072443502838994093031)
          ·
            refine ⟨10405608665254258491139547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937072443502838994093031 10405608665254258491139547)
            ·
              refine ⟨15608412997881387736709321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10405608665254258491139547 15608412997881387736709321)
              ·
                refine ⟨11706309748411040802531991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15608412997881387736709321 11706309748411040802531991)
                ·
                  refine ⟨17559464622616561203797987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11706309748411040802531991 17559464622616561203797987)
                  ·
                    refine ⟨26339196933924841805696981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17559464622616561203797987 26339196933924841805696981)
                    ·
                      refine ⟨617324928138863479821023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26339196933924841805696981 617324928138863479821023)
                      ·
                        rfl

theorem cell23_1202236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1202236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202236 prefixEnd_1202236 := by exact prefixLift 1202236
  have htrace : WordTrace (prefixWord ++ tailWord_1202236) baseStart_1202236 baseEnd_1202236 := by
    simpa [prefixWord, tailWord_1202236, baseEnd_1202236] using wordTrace_append hprefix tailTrace_1202236
  have hstable : (prefixWord ++ tailWord_1202236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202236).length < 2 ^ (prefixWord ++ tailWord_1202236).sum := by decide
  have hdescent : baseEnd_1202236 < baseStart_1202236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202253 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1202253 : Nat := 118140960795 + 1202253 * 2 ^ 59
def prefixEnd_1202253 : Nat := 4983230072969 + 3 ^ 40 * 1202253 * 2
def baseEnd_1202253 : Nat := 617333657309989913308445

theorem tailTrace_1202253 : CollatzResearch.WordTrace tailWord_1202253 prefixEnd_1202253 617333657309989913308445 := by
  unfold tailWord_1202253
  simp only [CollatzResearch.WordTrace]
  refine ⟨43849769313450184310475413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29233179542300122873650275 43849769313450184310475413)
  ·
    refine ⟨2055457936567977389553535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43849769313450184310475413 2055457936567977389553535)
    ·
      refine ⟨3083186904851966084330303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055457936567977389553535 3083186904851966084330303)
      ·
        refine ⟨4624780357277949126495455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083186904851966084330303 4624780357277949126495455)
        ·
          refine ⟨6937170535916923689743183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624780357277949126495455 6937170535916923689743183)
          ·
            refine ⟨10405755803875385534614775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937170535916923689743183 10405755803875385534614775)
            ·
              refine ⟨15608633705813078301922163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10405755803875385534614775 15608633705813078301922163)
              ·
                refine ⟨23412950558719617452883245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15608633705813078301922163 23412950558719617452883245)
                ·
                  refine ⟨8779856459519856544831217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23412950558719617452883245 8779856459519856544831217)
                  ·
                    refine ⟨6584892344639892408623413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8779856459519856544831217 6584892344639892408623413)
                    ·
                      refine ⟨617333657309989913308445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6584892344639892408623413 617333657309989913308445)
                      ·
                        rfl

theorem cell23_1202253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1202253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202253 prefixEnd_1202253 := by exact prefixLift 1202253
  have htrace : WordTrace (prefixWord ++ tailWord_1202253) baseStart_1202253 baseEnd_1202253 := by
    simpa [prefixWord, tailWord_1202253, baseEnd_1202253] using wordTrace_append hprefix tailTrace_1202253
  have hstable : (prefixWord ++ tailWord_1202253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202253).length < 2 ^ (prefixWord ++ tailWord_1202253).sum := by decide
  have hdescent : baseEnd_1202253 < baseStart_1202253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202263 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1202263 : Nat := 118140960795 + 1202263 * 2 ^ 59
def prefixEnd_1202263 : Nat := 4983230072969 + 3 ^ 40 * 1202263 * 2
def baseEnd_1202263 : Nat := 617338792116534874183399

theorem tailTrace_1202263 : CollatzResearch.WordTrace tailWord_1202263 prefixEnd_1202263 617338792116534874183399 := by
  unfold tailWord_1202263
  simp only [CollatzResearch.WordTrace]
  refine ⟨43850134043413956018339443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29233422695609304012226295 43850134043413956018339443)
  ·
    refine ⟨65775201065120934027509165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43850134043413956018339443 65775201065120934027509165)
    ·
      refine ⟨24665700399420350260315937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65775201065120934027509165 24665700399420350260315937)
      ·
        refine ⟨18499275299565262695236953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24665700399420350260315937 18499275299565262695236953)
        ·
          refine ⟨13874456474673947021427715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18499275299565262695236953 13874456474673947021427715)
          ·
            refine ⟨20811684712010920532141573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13874456474673947021427715 20811684712010920532141573)
            ·
              refine ⟨3902190883502047599776545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20811684712010920532141573 3902190883502047599776545)
              ·
                refine ⟨2926643162626535699832409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902190883502047599776545 2926643162626535699832409)
                ·
                  refine ⟨2194982371969901774874307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926643162626535699832409 2194982371969901774874307)
                  ·
                    refine ⟨3292473557954852662311461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2194982371969901774874307 3292473557954852662311461)
                    ·
                      refine ⟨617338792116534874183399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3292473557954852662311461 617338792116534874183399)
                      ·
                        rfl

theorem cell23_1202263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1202263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202263 prefixEnd_1202263 := by exact prefixLift 1202263
  have htrace : WordTrace (prefixWord ++ tailWord_1202263) baseStart_1202263 baseEnd_1202263 := by
    simpa [prefixWord, tailWord_1202263, baseEnd_1202263] using wordTrace_append hprefix tailTrace_1202263
  have hstable : (prefixWord ++ tailWord_1202263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202263).length < 2 ^ (prefixWord ++ tailWord_1202263).sum := by decide
  have hdescent : baseEnd_1202263 < baseStart_1202263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202266 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1202266 : Nat := 118140960795 + 1202266 * 2 ^ 59
def prefixEnd_1202266 : Nat := 4983230072969 + 3 ^ 40 * 1202266 * 2
def baseEnd_1202266 : Nat := 617340332558498362445885

theorem tailTrace_1202266 : CollatzResearch.WordTrace tailWord_1202266 prefixEnd_1202266 617340332558498362445885 := by
  unfold tailWord_1202266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962560865600771882674663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29233495641602058353799101 10962560865600771882674663)
  ·
    refine ⟨16443841298401157824011995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10962560865600771882674663 16443841298401157824011995)
    ·
      refine ⟨24665761947601736736017993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16443841298401157824011995 24665761947601736736017993)
      ·
        refine ⟨18499321460701302552013495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24665761947601736736017993 18499321460701302552013495)
        ·
          refine ⟨27748982191051953828020243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499321460701302552013495 27748982191051953828020243)
          ·
            refine ⟨41623473286577930742030365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748982191051953828020243 41623473286577930742030365)
            ·
              refine ⟨15608802482466724028261387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41623473286577930742030365 15608802482466724028261387)
              ·
                refine ⟨23413203723700086042392081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15608802482466724028261387 23413203723700086042392081)
                ·
                  refine ⟨17559902792775064531794061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23413203723700086042392081 17559902792775064531794061)
                  ·
                    refine ⟨6584963547290649199422773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17559902792775064531794061 6584963547290649199422773)
                    ·
                      refine ⟨617340332558498362445885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6584963547290649199422773 617340332558498362445885)
                      ·
                        rfl

theorem cell23_1202266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1202266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202266 prefixEnd_1202266 := by exact prefixLift 1202266
  have htrace : WordTrace (prefixWord ++ tailWord_1202266) baseStart_1202266 baseEnd_1202266 := by
    simpa [prefixWord, tailWord_1202266, baseEnd_1202266] using wordTrace_append hprefix tailTrace_1202266
  have hstable : (prefixWord ++ tailWord_1202266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202266).length < 2 ^ (prefixWord ++ tailWord_1202266).sum := by decide
  have hdescent : baseEnd_1202266 < baseStart_1202266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202273 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1202273 : Nat := 118140960795 + 1202273 * 2 ^ 59
def prefixEnd_1202273 : Nat := 4983230072969 + 3 ^ 40 * 1202273 * 2
def baseEnd_1202273 : Nat := 205781308974359945019451

theorem tailTrace_1202273 : CollatzResearch.WordTrace tailWord_1202273 prefixEnd_1202273 205781308974359945019451 := by
  unfold tailWord_1202273
  simp only [CollatzResearch.WordTrace]
  refine ⟨43850498773377727726203473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29233665848918485150802315 43850498773377727726203473)
  ·
    refine ⟨32887874080033295794652605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43850498773377727726203473 32887874080033295794652605)
    ·
      refine ⟨12332952780012485922994727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32887874080033295794652605 12332952780012485922994727)
      ·
        refine ⟨18499429170018728884492091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332952780012485922994727 18499429170018728884492091)
        ·
          refine ⟨27749143755028093326738137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499429170018728884492091 27749143755028093326738137)
          ·
            refine ⟨20811857816271069995053603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27749143755028093326738137 20811857816271069995053603)
            ·
              refine ⟨31217786724406604992580405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20811857816271069995053603 31217786724406604992580405)
              ·
                refine ⟨2926667505413119218054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31217786724406604992580405 2926667505413119218054413)
                ·
                  refine ⟨1097500314529919706770405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2926667505413119218054413 1097500314529919706770405)
                  ·
                    refine ⟨205781308974359945019451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097500314529919706770405 205781308974359945019451)
                    ·
                      rfl

theorem cell23_1202273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1202273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202273 prefixEnd_1202273 := by exact prefixLift 1202273
  have htrace : WordTrace (prefixWord ++ tailWord_1202273) baseStart_1202273 baseEnd_1202273 := by
    simpa [prefixWord, tailWord_1202273, baseEnd_1202273] using wordTrace_append hprefix tailTrace_1202273
  have hstable : (prefixWord ++ tailWord_1202273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202273).length < 2 ^ (prefixWord ++ tailWord_1202273).sum := by decide
  have hdescent : baseEnd_1202273 < baseStart_1202273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202290 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1202290 : Nat := 118140960795 + 1202290 * 2 ^ 59
def prefixEnd_1202290 : Nat := 4983230072969 + 3 ^ 40 * 1202290 * 2
def baseEnd_1202290 : Nat := 205784218698068756181925

theorem tailTrace_1202290 : CollatzResearch.WordTrace tailWord_1202290 prefixEnd_1202290 205784218698068756181925 := by
  unfold tailWord_1202290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962779703579034907393081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29234079209544093086381549 10962779703579034907393081)
  ·
    refine ⟨8222084777684276180544811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10962779703579034907393081 8222084777684276180544811)
    ·
      refine ⟨12333127166526414270817217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8222084777684276180544811 12333127166526414270817217)
      ·
        refine ⟨9249845374894810703112913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12333127166526414270817217 9249845374894810703112913)
        ·
          refine ⟨6937384031171108027334685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249845374894810703112913 6937384031171108027334685)
          ·
            refine ⟨2601519011689165510250507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6937384031171108027334685 2601519011689165510250507)
            ·
              refine ⟨3902278517533748265375761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601519011689165510250507 3902278517533748265375761)
              ·
                refine ⟨2926708888150311199031821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3902278517533748265375761 2926708888150311199031821)
                ·
                  refine ⟨1097515833056366699636933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2926708888150311199031821 1097515833056366699636933)
                  ·
                    refine ⟨205784218698068756181925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097515833056366699636933 205784218698068756181925)
                    ·
                      rfl

theorem cell23_1202290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1202290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202290 prefixEnd_1202290 := by exact prefixLift 1202290
  have htrace : WordTrace (prefixWord ++ tailWord_1202290) baseStart_1202290 baseEnd_1202290 := by
    simpa [prefixWord, tailWord_1202290, baseEnd_1202290] using wordTrace_append hprefix tailTrace_1202290
  have hstable : (prefixWord ++ tailWord_1202290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202290).length < 2 ^ (prefixWord ++ tailWord_1202290).sum := by decide
  have hdescent : baseEnd_1202290 < baseStart_1202290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202300 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_1202300 : Nat := 118140960795 + 1202300 * 2 ^ 59
def prefixEnd_1202300 : Nat := 4983230072969 + 3 ^ 40 * 1202300 * 2
def baseEnd_1202300 : Nat := 617357790900751229420729

theorem tailTrace_1202300 : CollatzResearch.WordTrace tailWord_1202300 prefixEnd_1202300 617357790900751229420729 := by
  unfold tailWord_1202300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925741772139955668718177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29234322362853274224957569 21925741772139955668718177)
  ·
    refine ⟨16444306329104966751538633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21925741772139955668718177 16444306329104966751538633)
    ·
      refine ⟨12333229746828725063653975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16444306329104966751538633 12333229746828725063653975)
      ·
        refine ⟨18499844620243087595480963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12333229746828725063653975 18499844620243087595480963)
        ·
          refine ⟨27749766930364631393221445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499844620243087595480963 27749766930364631393221445)
          ·
            refine ⟨5203081299443368386229021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27749766930364631393221445 5203081299443368386229021)
            ·
              refine ⟨1951155487291263144835883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5203081299443368386229021 1951155487291263144835883)
              ·
                refine ⟨2926733230936894717253825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951155487291263144835883 2926733230936894717253825)
                ·
                  refine ⟨2195049923202671037940369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926733230936894717253825 2195049923202671037940369)
                  ·
                    refine ⟨1646287442402003278455277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195049923202671037940369 1646287442402003278455277)
                    ·
                      refine ⟨617357790900751229420729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646287442402003278455277 617357790900751229420729)
                      ·
                        rfl

theorem cell23_1202300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_1202300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202300 prefixEnd_1202300 := by exact prefixLift 1202300
  have htrace : WordTrace (prefixWord ++ tailWord_1202300) baseStart_1202300 baseEnd_1202300 := by
    simpa [prefixWord, tailWord_1202300, baseEnd_1202300] using wordTrace_append hprefix tailTrace_1202300
  have hstable : (prefixWord ++ tailWord_1202300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202300).length < 2 ^ (prefixWord ++ tailWord_1202300).sum := by decide
  have hdescent : baseEnd_1202300 < baseStart_1202300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202307 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 1, 4]
def baseStart_1202307 : Nat := 118140960795 + 1202307 * 2 ^ 59
def prefixEnd_1202307 : Nat := 4983230072969 + 3 ^ 40 * 1202307 * 2
def baseEnd_1202307 : Nat := 205787128421777567344399

theorem tailTrace_1202307 : CollatzResearch.WordTrace tailWord_1202307 prefixEnd_1202307 205787128421777567344399 := by
  unfold tailWord_1202307
  simp only [CollatzResearch.WordTrace]
  refine ⟨43851738855254551532941175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29234492570169701021960783 43851738855254551532941175)
  ·
    refine ⟨65777608282881827299411763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43851738855254551532941175 65777608282881827299411763)
    ·
      refine ⟨98666412424322740949117645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65777608282881827299411763 98666412424322740949117645)
      ·
        refine ⟨36999904659121027855919117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98666412424322740949117645 36999904659121027855919117)
        ·
          refine ⟨13874964247170385445969669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36999904659121027855919117 13874964247170385445969669)
          ·
            refine ⟨2601555796344447271119313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13874964247170385445969669 2601555796344447271119313)
            ·
              refine ⟨1951166847258335453339485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601555796344447271119313 1951166847258335453339485)
              ·
                refine ⟨731687567721875795002307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951166847258335453339485 731687567721875795002307)
                ·
                  refine ⟨1097531351582813692503461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731687567721875795002307 1097531351582813692503461)
                  ·
                    refine ⟨205787128421777567344399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097531351582813692503461 205787128421777567344399)
                    ·
                      rfl

theorem cell23_1202307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 1, 4].length) (baseStart_1202307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202307 prefixEnd_1202307 := by exact prefixLift 1202307
  have htrace : WordTrace (prefixWord ++ tailWord_1202307) baseStart_1202307 baseEnd_1202307 := by
    simpa [prefixWord, tailWord_1202307, baseEnd_1202307] using wordTrace_append hprefix tailTrace_1202307
  have hstable : (prefixWord ++ tailWord_1202307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202307).length < 2 ^ (prefixWord ++ tailWord_1202307).sum := by decide
  have hdescent : baseEnd_1202307 < baseStart_1202307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202324 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1202324 : Nat := 118140960795 + 1202324 * 2 ^ 59
def prefixEnd_1202324 : Nat := 4983230072969 + 3 ^ 40 * 1202324 * 2
def baseEnd_1202324 : Nat := 205790038145486378506873

theorem tailTrace_1202324 : CollatzResearch.WordTrace tailWord_1202324 prefixEnd_1202324 205790038145486378506873 := by
  unfold tailWord_1202324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21926179448096481718155013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29234905930795308957540017 21926179448096481718155013)
  ·
    refine ⟨4111158646518090322154065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21926179448096481718155013 4111158646518090322154065)
    ·
      refine ⟨3083368984888567741615549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4111158646518090322154065 3083368984888567741615549)
      ·
        refine ⟨1156263369333212903105831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3083368984888567741615549 1156263369333212903105831)
        ·
          refine ⟨1734395053999819354658747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156263369333212903105831 1734395053999819354658747)
          ·
            refine ⟨2601592580999729031988121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734395053999819354658747 2601592580999729031988121)
            ·
              refine ⟨1951194435749796773991091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601592580999729031988121 1951194435749796773991091)
              ·
                refine ⟨2926791653624695160986637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951194435749796773991091 2926791653624695160986637)
                ·
                  refine ⟨1097546870109260685369989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2926791653624695160986637 1097546870109260685369989)
                  ·
                    refine ⟨205790038145486378506873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097546870109260685369989 205790038145486378506873)
                    ·
                      rfl

theorem cell23_1202324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1202324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202324 prefixEnd_1202324 := by exact prefixLift 1202324
  have htrace : WordTrace (prefixWord ++ tailWord_1202324) baseStart_1202324 baseEnd_1202324 := by
    simpa [prefixWord, tailWord_1202324, baseEnd_1202324] using wordTrace_append hprefix tailTrace_1202324
  have hstable : (prefixWord ++ tailWord_1202324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202324).length < 2 ^ (prefixWord ++ tailWord_1202324).sum := by decide
  have hdescent : baseEnd_1202324 < baseStart_1202324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202363 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 6, 4]
def baseStart_1202363 : Nat := 118140960795 + 1202363 * 2 ^ 59
def prefixEnd_1202363 : Nat := 4983230072969 + 3 ^ 40 * 1202363 * 2
def baseEnd_1202363 : Nat := 205796713393994827644313

theorem tailTrace_1202363 : CollatzResearch.WordTrace tailWord_1202363 prefixEnd_1202363 205796713393994827644313 := by
  unfold tailWord_1202363
  simp only [CollatzResearch.WordTrace]
  refine ⟨43853781343051673096979743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29235854228701115397986495 43853781343051673096979743)
  ·
    refine ⟨65780672014577509645469615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43853781343051673096979743 65780672014577509645469615)
    ·
      refine ⟨98671008021866264468204423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65780672014577509645469615 98671008021866264468204423)
      ·
        refine ⟨148006512032799396702306635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98671008021866264468204423 148006512032799396702306635)
        ·
          refine ⟨222009768049199095053459953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148006512032799396702306635 222009768049199095053459953)
          ·
            refine ⟨166507326036899321290094965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222009768049199095053459953 166507326036899321290094965)
            ·
              refine ⟨15610061815959311370946403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166507326036899321290094965 15610061815959311370946403)
              ·
                refine ⟨23415092723938967056419605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15610061815959311370946403 23415092723938967056419605)
                ·
                  refine ⟨1097582471434639080769669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23415092723938967056419605 1097582471434639080769669)
                  ·
                    refine ⟨205796713393994827644313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097582471434639080769669 205796713393994827644313)
                    ·
                      rfl

theorem cell23_1202363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 4].length) (baseStart_1202363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202363 prefixEnd_1202363 := by exact prefixLift 1202363
  have htrace : WordTrace (prefixWord ++ tailWord_1202363) baseStart_1202363 baseEnd_1202363 := by
    simpa [prefixWord, tailWord_1202363, baseEnd_1202363] using wordTrace_append hprefix tailTrace_1202363
  have hstable : (prefixWord ++ tailWord_1202363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202363).length < 2 ^ (prefixWord ++ tailWord_1202363).sum := by decide
  have hdescent : baseEnd_1202363 < baseStart_1202363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202373 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_1202373 : Nat := 118140960795 + 1202373 * 2 ^ 59
def prefixEnd_1202373 : Nat := 4983230072969 + 3 ^ 40 * 1202373 * 2
def baseEnd_1202373 : Nat := 617395274988529443807893

theorem tailTrace_1202373 : CollatzResearch.WordTrace tailWord_1202373 prefixEnd_1202373 617395274988529443807893 := by
  unfold tailWord_1202373
  simp only [CollatzResearch.WordTrace]
  refine ⟨43854146073015444804843773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29236097382010296536562515 43854146073015444804843773)
  ·
    refine ⟨16445304777380791801816415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43854146073015444804843773 16445304777380791801816415)
    ·
      refine ⟨24667957166071187702724623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445304777380791801816415 24667957166071187702724623)
      ·
        refine ⟨37001935749106781554086935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24667957166071187702724623 37001935749106781554086935)
        ·
          refine ⟨55502903623660172331130403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37001935749106781554086935 55502903623660172331130403)
          ·
            refine ⟨83254355435490258496695605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55502903623660172331130403 83254355435490258496695605)
            ·
              refine ⟨7805095822077211734065213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83254355435490258496695605 7805095822077211734065213)
              ·
                refine ⟨2926910933278954400274455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7805095822077211734065213 2926910933278954400274455)
                ·
                  refine ⟨4390366399918431600411683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926910933278954400274455 4390366399918431600411683)
                  ·
                    refine ⟨6585549599877647400617525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4390366399918431600411683 6585549599877647400617525)
                    ·
                      refine ⟨617395274988529443807893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6585549599877647400617525 617395274988529443807893)
                      ·
                        rfl

theorem cell23_1202373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_1202373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202373 prefixEnd_1202373 := by exact prefixLift 1202373
  have htrace : WordTrace (prefixWord ++ tailWord_1202373) baseStart_1202373 baseEnd_1202373 := by
    simpa [prefixWord, tailWord_1202373, baseEnd_1202373] using wordTrace_append hprefix tailTrace_1202373
  have hstable : (prefixWord ++ tailWord_1202373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202373).length < 2 ^ (prefixWord ++ tailWord_1202373).sum := by decide
  have hdescent : baseEnd_1202373 < baseStart_1202373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202407 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1202407 : Nat := 118140960795 + 1202407 * 2 ^ 59
def prefixEnd_1202407 : Nat := 4983230072969 + 3 ^ 40 * 1202407 * 2
def baseEnd_1202407 : Nat := 617412733330782310782737

theorem tailTrace_1202407 : CollatzResearch.WordTrace tailWord_1202407 prefixEnd_1202407 617412733330782310782737 := by
  unfold tailWord_1202407
  simp only [CollatzResearch.WordTrace]
  refine ⟨43855386154892268611581475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29236924103261512407720983 43855386154892268611581475)
  ·
    refine ⟨65783079232338402917372213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43855386154892268611581475 65783079232338402917372213)
    ·
      refine ⟨6167163678031725273503645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65783079232338402917372213 6167163678031725273503645)
      ·
        refine ⟨2312686379261896977563867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6167163678031725273503645 2312686379261896977563867)
        ·
          refine ⟨3469029568892845466345801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312686379261896977563867 3469029568892845466345801)
          ·
            refine ⟨2601772176669634099759351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469029568892845466345801 2601772176669634099759351)
            ·
              refine ⟨3902658265004451149639027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601772176669634099759351 3902658265004451149639027)
              ·
                refine ⟨5853987397506676724458541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902658265004451149639027 5853987397506676724458541)
                ·
                  refine ⟨2195245274065003771671953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5853987397506676724458541 2195245274065003771671953)
                  ·
                    refine ⟨1646433955548752828753965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195245274065003771671953 1646433955548752828753965)
                    ·
                      refine ⟨617412733330782310782737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646433955548752828753965 617412733330782310782737)
                      ·
                        rfl

theorem cell23_1202407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1202407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202407 prefixEnd_1202407 := by exact prefixLift 1202407
  have htrace : WordTrace (prefixWord ++ tailWord_1202407) baseStart_1202407 baseEnd_1202407 := by
    simpa [prefixWord, tailWord_1202407, baseEnd_1202407] using wordTrace_append hprefix tailTrace_1202407
  have hstable : (prefixWord ++ tailWord_1202407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202407).length < 2 ^ (prefixWord ++ tailWord_1202407).sum := by decide
  have hdescent : baseEnd_1202407 < baseStart_1202407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202443 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_1202443 : Nat := 118140960795 + 1202443 * 2 ^ 59
def prefixEnd_1202443 : Nat := 4983230072969 + 3 ^ 40 * 1202443 * 2
def baseEnd_1202443 : Nat := 617431218634344169932571

theorem tailTrace_1202443 : CollatzResearch.WordTrace tailWord_1202443 prefixEnd_1202443 617431218634344169932571 := by
  unfold tailWord_1202443
  simp only [CollatzResearch.WordTrace]
  refine ⟨43856699182761846759891983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29237799455174564506594655 43856699182761846759891983)
  ·
    refine ⟨65785048774142770139837975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43856699182761846759891983 65785048774142770139837975)
    ·
      refine ⟨98677573161214155209756963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65785048774142770139837975 98677573161214155209756963)
      ·
        refine ⟨148016359741821232814635445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98677573161214155209756963 148016359741821232814635445)
        ·
          refine ⟨13876533725795740576372073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148016359741821232814635445 13876533725795740576372073)
          ·
            refine ⟨10407400294346805432279055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13876533725795740576372073 10407400294346805432279055)
            ·
              refine ⟨15611100441520208148418583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407400294346805432279055 15611100441520208148418583)
              ·
                refine ⟨23416650662280312222627875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15611100441520208148418583 23416650662280312222627875)
                ·
                  refine ⟨35124975993420468333941813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23416650662280312222627875 35124975993420468333941813)
                  ·
                    refine ⟨3292966499383168906307045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35124975993420468333941813 3292966499383168906307045)
                    ·
                      refine ⟨617431218634344169932571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3292966499383168906307045 617431218634344169932571)
                      ·
                        rfl

theorem cell23_1202443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_1202443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202443 prefixEnd_1202443 := by exact prefixLift 1202443
  have htrace : WordTrace (prefixWord ++ tailWord_1202443) baseStart_1202443 baseEnd_1202443 := by
    simpa [prefixWord, tailWord_1202443, baseEnd_1202443] using wordTrace_append hprefix tailTrace_1202443
  have hstable : (prefixWord ++ tailWord_1202443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202443).length < 2 ^ (prefixWord ++ tailWord_1202443).sum := by decide
  have hdescent : baseEnd_1202443 < baseStart_1202443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202453 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_1202453 : Nat := 118140960795 + 1202453 * 2 ^ 59
def prefixEnd_1202453 : Nat := 4983230072969 + 3 ^ 40 * 1202453 * 2
def baseEnd_1202453 : Nat := 205812117813629710269175

theorem tailTrace_1202453 : CollatzResearch.WordTrace tailWord_1202453 prefixEnd_1202453 205812117813629710269175 := by
  unfold tailWord_1202453
  simp only [CollatzResearch.WordTrace]
  refine ⟨43857063912725618467756013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29238042608483745645170675 43857063912725618467756013)
  ·
    refine ⟨16446398967272106925408505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43857063912725618467756013 16446398967272106925408505)
    ·
      refine ⟨12334799225454080194056379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16446398967272106925408505 12334799225454080194056379)
      ·
        refine ⟨18502198838181120291084569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12334799225454080194056379 18502198838181120291084569)
        ·
          refine ⟨13876649128635840218313427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18502198838181120291084569 13876649128635840218313427)
          ·
            refine ⟨20814973692953760327470141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13876649128635840218313427 20814973692953760327470141)
            ·
              refine ⟨7805615134857660122801303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20814973692953760327470141 7805615134857660122801303)
              ·
                refine ⟨11708422702286490184201955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7805615134857660122801303 11708422702286490184201955)
                ·
                  refine ⟨17562634053429735276302933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11708422702286490184201955 17562634053429735276302933)
                  ·
                    refine ⟨205812117813629710269175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17562634053429735276302933 205812117813629710269175)
                    ·
                      rfl

theorem cell23_1202453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_1202453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202453 prefixEnd_1202453 := by exact prefixLift 1202453
  have htrace : WordTrace (prefixWord ++ tailWord_1202453) baseStart_1202453 baseEnd_1202453 := by
    simpa [prefixWord, tailWord_1202453, baseEnd_1202453] using wordTrace_append hprefix tailTrace_1202453
  have hstable : (prefixWord ++ tailWord_1202453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202453).length < 2 ^ (prefixWord ++ tailWord_1202453).sum := by decide
  have hdescent : baseEnd_1202453 < baseStart_1202453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202483 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 9]
def baseStart_1202483 : Nat := 118140960795 + 1202483 * 2 ^ 59
def prefixEnd_1202483 : Nat := 4983230072969 + 3 ^ 40 * 1202483 * 2
def baseEnd_1202483 : Nat := 68605750873391557048043

theorem tailTrace_1202483 : CollatzResearch.WordTrace tailWord_1202483 prefixEnd_1202483 68605750873391557048043 := by
  unfold tailWord_1202483
  simp only [CollatzResearch.WordTrace]
  refine ⟨43858158102616933591348103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29238772068411289060898735 43858158102616933591348103)
  ·
    refine ⟨65787237153925400387022155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43858158102616933591348103 65787237153925400387022155)
    ·
      refine ⟨98680855730888100580533233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65787237153925400387022155 98680855730888100580533233)
      ·
        refine ⟨74010641798166075435399925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98680855730888100580533233 74010641798166075435399925)
        ·
          refine ⟨6938497668578069572068743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74010641798166075435399925 6938497668578069572068743)
          ·
            refine ⟨10407746502867104358103115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938497668578069572068743 10407746502867104358103115)
            ·
              refine ⟨15611619754300656537154673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10407746502867104358103115 15611619754300656537154673)
              ·
                refine ⟨11708714815725492402866005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15611619754300656537154673 11708714815725492402866005)
                ·
                  refine ⟨68605750873391557048043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11708714815725492402866005 68605750873391557048043)
                  ·
                    rfl

theorem cell23_1202483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 9].length) (baseStart_1202483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202483 prefixEnd_1202483 := by exact prefixLift 1202483
  have htrace : WordTrace (prefixWord ++ tailWord_1202483) baseStart_1202483 baseEnd_1202483 := by
    simpa [prefixWord, tailWord_1202483, baseEnd_1202483] using wordTrace_append hprefix tailTrace_1202483
  have hstable : (prefixWord ++ tailWord_1202483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202483).length < 2 ^ (prefixWord ++ tailWord_1202483).sum := by decide
  have hdescent : baseEnd_1202483 < baseStart_1202483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202490 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1202490 : Nat := 118140960795 + 1202490 * 2 ^ 59
def prefixEnd_1202490 : Nat := 4983230072969 + 3 ^ 40 * 1202490 * 2
def baseEnd_1202490 : Nat := 617455352225105486044855

theorem tailTrace_1202490 : CollatzResearch.WordTrace tailWord_1202490 prefixEnd_1202490 617455352225105486044855 := by
  unfold tailWord_1202490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964603353397893446713231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29238942275727715857901949 10964603353397893446713231)
  ·
    refine ⟨16446905030096840170069847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10964603353397893446713231 16446905030096840170069847)
    ·
      refine ⟨24670357545145260255104771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16446905030096840170069847 24670357545145260255104771)
      ·
        refine ⟨37005536317717890382657157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24670357545145260255104771 37005536317717890382657157)
        ·
          refine ⟨6938538059572104446748217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37005536317717890382657157 6938538059572104446748217)
          ·
            refine ⟨5203903544679078335061163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6938538059572104446748217 5203903544679078335061163)
            ·
              refine ⟨7805855317018617502591745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203903544679078335061163 7805855317018617502591745)
              ·
                refine ⟨5854391487763963126943809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7805855317018617502591745 5854391487763963126943809)
                ·
                  refine ⟨4390793615822972345207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5854391487763963126943809 4390793615822972345207857)
                  ·
                    refine ⟨3293095211867229258905893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4390793615822972345207857 3293095211867229258905893)
                    ·
                      refine ⟨617455352225105486044855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3293095211867229258905893 617455352225105486044855)
                      ·
                        rfl

theorem cell23_1202490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1202490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202490 prefixEnd_1202490 := by exact prefixLift 1202490
  have htrace : WordTrace (prefixWord ++ tailWord_1202490) baseStart_1202490 baseEnd_1202490 := by
    simpa [prefixWord, tailWord_1202490, baseEnd_1202490] using wordTrace_append hprefix tailTrace_1202490
  have hstable : (prefixWord ++ tailWord_1202490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202490).length < 2 ^ (prefixWord ++ tailWord_1202490).sum := by decide
  have hdescent : baseEnd_1202490 < baseStart_1202490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202510 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_1202510 : Nat := 118140960795 + 1202510 * 2 ^ 59
def prefixEnd_1202510 : Nat := 4983230072969 + 3 ^ 40 * 1202510 * 2
def baseEnd_1202510 : Nat := 617465621838195407794763

theorem tailTrace_1202510 : CollatzResearch.WordTrace tailWord_1202510 prefixEnd_1202510 617465621838195407794763 := by
  unfold tailWord_1202510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482392859189889650322623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29239428582346078135053989 5482392859189889650322623)
  ·
    refine ⟨8223589288784834475483935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482392859189889650322623 8223589288784834475483935)
    ·
      refine ⟨12335383933177251713225903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8223589288784834475483935 12335383933177251713225903)
      ·
        refine ⟨18503075899765877569838855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12335383933177251713225903 18503075899765877569838855)
        ·
          refine ⟨27754613849648816354758283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18503075899765877569838855 27754613849648816354758283)
          ·
            refine ⟨41631920774473224532137425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27754613849648816354758283 41631920774473224532137425)
            ·
              refine ⟨31223940580854918399103069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41631920774473224532137425 31223940580854918399103069)
              ·
                refine ⟨11708977717820594399663651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31223940580854918399103069 11708977717820594399663651)
                ·
                  refine ⟨17563466576730891599495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11708977717820594399663651 17563466576730891599495477)
                  ·
                    refine ⟨1646574991568521087452701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17563466576730891599495477 1646574991568521087452701)
                    ·
                      refine ⟨617465621838195407794763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646574991568521087452701 617465621838195407794763)
                      ·
                        rfl

theorem cell23_1202510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_1202510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202510 prefixEnd_1202510 := by exact prefixLift 1202510
  have htrace : WordTrace (prefixWord ++ tailWord_1202510) baseStart_1202510 baseEnd_1202510 := by
    simpa [prefixWord, tailWord_1202510, baseEnd_1202510] using wordTrace_append hprefix tailTrace_1202510
  have hstable : (prefixWord ++ tailWord_1202510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202510).length < 2 ^ (prefixWord ++ tailWord_1202510).sum := by decide
  have hdescent : baseEnd_1202510 < baseStart_1202510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202562 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1202562 : Nat := 118140960795 + 1202562 * 2 ^ 59
def prefixEnd_1202562 : Nat := 4983230072969 + 3 ^ 40 * 1202562 * 2
def baseEnd_1202562 : Nat := 617492322832229204344525

theorem tailTrace_1202562 : CollatzResearch.WordTrace tailWord_1202562 prefixEnd_1202562 617492322832229204344525 := by
  unfold tailWord_1202562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965259867332682520868485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29240692979553820055649293 10965259867332682520868485)
  ·
    refine ⟨2055986225124877972662841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10965259867332682520868485 2055986225124877972662841)
    ·
      refine ⟨1541989668843658479497131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2055986225124877972662841 1541989668843658479497131)
      ·
        refine ⟨2312984503265487719245697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541989668843658479497131 2312984503265487719245697)
        ·
          refine ⟨1734738377449115789434273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312984503265487719245697 1734738377449115789434273)
          ·
            refine ⟨1301053783086836842075705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734738377449115789434273 1301053783086836842075705)
            ·
              refine ⟨975790337315127631556779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301053783086836842075705 975790337315127631556779)
              ·
                refine ⟨1463685505972691447335169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975790337315127631556779 1463685505972691447335169)
                ·
                  refine ⟨1097764129479518585501377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463685505972691447335169 1097764129479518585501377)
                  ·
                    refine ⟨823323097109638939126033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097764129479518585501377 823323097109638939126033)
                    ·
                      refine ⟨617492322832229204344525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823323097109638939126033 617492322832229204344525)
                      ·
                        rfl

theorem cell23_1202562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1202562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202562 prefixEnd_1202562 := by exact prefixLift 1202562
  have htrace : WordTrace (prefixWord ++ tailWord_1202562) baseStart_1202562 baseEnd_1202562 := by
    simpa [prefixWord, tailWord_1202562, baseEnd_1202562] using wordTrace_append hprefix tailTrace_1202562
  have hstable : (prefixWord ++ tailWord_1202562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202562).length < 2 ^ (prefixWord ++ tailWord_1202562).sum := by decide
  have hdescent : baseEnd_1202562 < baseStart_1202562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202567 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 6, 2]
def baseStart_1202567 : Nat := 118140960795 + 1202567 * 2 ^ 59
def prefixEnd_1202567 : Nat := 4983230072969 + 3 ^ 40 * 1202567 * 2
def baseEnd_1202567 : Nat := 617494890235501684782001

theorem tailTrace_1202567 : CollatzResearch.WordTrace tailWord_1202567 prefixEnd_1202567 617494890235501684782001 := by
  unfold tailWord_1202567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43861221834312615937405955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29240814556208410624937303 43861221834312615937405955)
  ·
    refine ⟨65791832751468923906108933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43861221834312615937405955 65791832751468923906108933)
    ·
      refine ⟨12335968640900423232395425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65791832751468923906108933 12335968640900423232395425)
      ·
        refine ⟨9251976480675317424296569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12335968640900423232395425 9251976480675317424296569)
        ·
          refine ⟨6938982360506488068222427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9251976480675317424296569 6938982360506488068222427)
          ·
            refine ⟨10408473540759732102333641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6938982360506488068222427 10408473540759732102333641)
            ·
              refine ⟨7806355155569799076750231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10408473540759732102333641 7806355155569799076750231)
              ·
                refine ⟨11709532733354698615125347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806355155569799076750231 11709532733354698615125347)
                ·
                  refine ⟨17564299100032047922688021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11709532733354698615125347 17564299100032047922688021)
                  ·
                    refine ⟨823326520314002246376001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17564299100032047922688021 823326520314002246376001)
                    ·
                      refine ⟨617494890235501684782001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823326520314002246376001 617494890235501684782001)
                      ·
                        rfl

theorem cell23_1202567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_1202567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202567 prefixEnd_1202567 := by exact prefixLift 1202567
  have htrace : WordTrace (prefixWord ++ tailWord_1202567) baseStart_1202567 baseEnd_1202567 := by
    simpa [prefixWord, tailWord_1202567, baseEnd_1202567] using wordTrace_append hprefix tailTrace_1202567
  have hstable : (prefixWord ++ tailWord_1202567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202567).length < 2 ^ (prefixWord ++ tailWord_1202567).sum := by decide
  have hdescent : baseEnd_1202567 < baseStart_1202567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202584 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1202584 : Nat := 118140960795 + 1202584 * 2 ^ 59
def prefixEnd_1202584 : Nat := 4983230072969 + 3 ^ 40 * 1202584 * 2
def baseEnd_1202584 : Nat := 617503619406628118269423

theorem tailTrace_1202584 : CollatzResearch.WordTrace tailWord_1202584 prefixEnd_1202584 617503619406628118269423 := by
  unfold tailWord_1202584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21930920937625513920387403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29241227916834018560516537 21930920937625513920387403)
  ·
    refine ⟨32896381406438270880581105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21930920937625513920387403 32896381406438270880581105)
    ·
      refine ⟨24672286054828703160435829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32896381406438270880581105 24672286054828703160435829)
      ·
        refine ⟨2313026817640190921290859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24672286054828703160435829 2313026817640190921290859)
        ·
          refine ⟨3469540226460286381936289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313026817640190921290859 3469540226460286381936289)
          ·
            refine ⟨2602155169845214786452217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469540226460286381936289 2602155169845214786452217)
            ·
              refine ⟨1951616377383911089839163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602155169845214786452217 1951616377383911089839163)
              ·
                refine ⟨2927424566075866634758745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951616377383911089839163 2927424566075866634758745)
                ·
                  refine ⟨2195568424556899976069059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2927424566075866634758745 2195568424556899976069059)
                  ·
                    refine ⟨3293352636835349964103589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195568424556899976069059 3293352636835349964103589)
                    ·
                      refine ⟨617503619406628118269423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3293352636835349964103589 617503619406628118269423)
                      ·
                        rfl

theorem cell23_1202584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1202584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202584 prefixEnd_1202584 := by exact prefixLift 1202584
  have htrace : WordTrace (prefixWord ++ tailWord_1202584) baseStart_1202584 baseEnd_1202584 := by
    simpa [prefixWord, tailWord_1202584, baseEnd_1202584] using wordTrace_append hprefix tailTrace_1202584
  have hstable : (prefixWord ++ tailWord_1202584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202584).length < 2 ^ (prefixWord ++ tailWord_1202584).sum := by decide
  have hdescent : baseEnd_1202584 < baseStart_1202584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202602 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_1202602 : Nat := 118140960795 + 1202602 * 2 ^ 59
def prefixEnd_1202602 : Nat := 4983230072969 + 3 ^ 40 * 1202602 * 2
def baseEnd_1202602 : Nat := 68612540228712116427149

theorem tailTrace_1202602 : CollatzResearch.WordTrace tailWord_1202602 prefixEnd_1202602 68612540228712116427149 := by
  unfold tailWord_1202602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965624597296454228732515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29241665592790544609953373 10965624597296454228732515)
  ·
    refine ⟨16448436895944681343098773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10965624597296454228732515 16448436895944681343098773)
    ·
      refine ⟨771020479497406937957755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16448436895944681343098773 771020479497406937957755)
      ·
        refine ⟨1156530719246110406936633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771020479497406937957755 1156530719246110406936633)
        ·
          refine ⟨867398039434582805202475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156530719246110406936633 867398039434582805202475)
          ·
            refine ⟨1301097059151874207803713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867398039434582805202475 1301097059151874207803713)
            ·
              refine ⟨975822794363905655852785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301097059151874207803713 975822794363905655852785)
              ·
                refine ⟨731867095772929241889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975822794363905655852785 731867095772929241889589)
                ·
                  refine ⟨68612540228712116427149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731867095772929241889589 68612540228712116427149)
                  ·
                    rfl

theorem cell23_1202602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_1202602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202602 prefixEnd_1202602 := by exact prefixLift 1202602
  have htrace : WordTrace (prefixWord ++ tailWord_1202602) baseStart_1202602 baseEnd_1202602 := by
    simpa [prefixWord, tailWord_1202602, baseEnd_1202602] using wordTrace_append hprefix tailTrace_1202602
  have hstable : (prefixWord ++ tailWord_1202602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202602).length < 2 ^ (prefixWord ++ tailWord_1202602).sum := by decide
  have hdescent : baseEnd_1202602 < baseStart_1202602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202610 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1202610 : Nat := 118140960795 + 1202610 * 2 ^ 59
def prefixEnd_1202610 : Nat := 4983230072969 + 3 ^ 40 * 1202610 * 2
def baseEnd_1202610 : Nat := 617516969903645016544303

theorem tailTrace_1202610 : CollatzResearch.WordTrace tailWord_1202610 prefixEnd_1202610 617516969903645016544303 := by
  unfold tailWord_1202610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965697543289208570305321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29241860115437889520814189 10965697543289208570305321)
  ·
    refine ⟨8224273157466906427728991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10965697543289208570305321 8224273157466906427728991)
    ·
      refine ⟨12336409736200359641593487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8224273157466906427728991 12336409736200359641593487)
      ·
        refine ⟨18504614604300539462390231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336409736200359641593487 18504614604300539462390231)
        ·
          refine ⟨27756921906450809193585347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18504614604300539462390231 27756921906450809193585347)
          ·
            refine ⟨41635382859676213790378021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27756921906450809193585347 41635382859676213790378021)
            ·
              refine ⟨7806634286189290085695879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41635382859676213790378021 7806634286189290085695879)
              ·
                refine ⟨11709951429283935128543819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7806634286189290085695879 11709951429283935128543819)
                ·
                  refine ⟨17564927143925902692815729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11709951429283935128543819 17564927143925902692815729)
                  ·
                    refine ⟨13173695357944427019611797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17564927143925902692815729 13173695357944427019611797)
                    ·
                      refine ⟨617516969903645016544303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13173695357944427019611797 617516969903645016544303)
                      ·
                        rfl

theorem cell23_1202610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1202610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202610 prefixEnd_1202610 := by exact prefixLift 1202610
  have htrace : WordTrace (prefixWord ++ tailWord_1202610) baseStart_1202610 baseEnd_1202610 := by
    simpa [prefixWord, tailWord_1202610, baseEnd_1202610] using wordTrace_append hprefix tailTrace_1202610
  have hstable : (prefixWord ++ tailWord_1202610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202610).length < 2 ^ (prefixWord ++ tailWord_1202610).sum := by decide
  have hdescent : baseEnd_1202610 < baseStart_1202610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202627 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 5, 2]
def baseStart_1202627 : Nat := 118140960795 + 1202627 * 2 ^ 59
def prefixEnd_1202627 : Nat := 4983230072969 + 3 ^ 40 * 1202627 * 2
def baseEnd_1202627 : Nat := 617525699074771450031725

theorem tailTrace_1202627 : CollatzResearch.WordTrace tailWord_1202627 prefixEnd_1202627 617525699074771450031725 := by
  unfold tailWord_1202627
  simp only [CollatzResearch.WordTrace]
  refine ⟨43863410214095246184590135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29242273476063497456393423 43863410214095246184590135)
  ·
    refine ⟨65795115321142869276885203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43863410214095246184590135 65795115321142869276885203)
    ·
      refine ⟨98692672981714303915327805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65795115321142869276885203 98692672981714303915327805)
      ·
        refine ⟨37009752368142863968247927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98692672981714303915327805 37009752368142863968247927)
        ·
          refine ⟨55514628552214295952371891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37009752368142863968247927 55514628552214295952371891)
          ·
            refine ⟨83271942828321443928557837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55514628552214295952371891 83271942828321443928557837)
            ·
              refine ⟨31226978560620541473209189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83271942828321443928557837 31226978560620541473209189)
              ·
                refine ⟨5855058480116351526226723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31226978560620541473209189 5855058480116351526226723)
                ·
                  refine ⟨8782587720174527289340085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5855058480116351526226723 8782587720174527289340085)
                  ·
                    refine ⟨823367598766361933375633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8782587720174527289340085 823367598766361933375633)
                    ·
                      refine ⟨617525699074771450031725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823367598766361933375633 617525699074771450031725)
                      ·
                        rfl

theorem cell23_1202627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_1202627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202627 prefixEnd_1202627 := by exact prefixLift 1202627
  have htrace : WordTrace (prefixWord ++ tailWord_1202627) baseStart_1202627 baseEnd_1202627 := by
    simpa [prefixWord, tailWord_1202627, baseEnd_1202627] using wordTrace_append hprefix tailTrace_1202627
  have hstable : (prefixWord ++ tailWord_1202627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202627).length < 2 ^ (prefixWord ++ tailWord_1202627).sum := by decide
  have hdescent : baseEnd_1202627 < baseStart_1202627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202634 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1202634 : Nat := 118140960795 + 1202634 * 2 ^ 59
def prefixEnd_1202634 : Nat := 4983230072969 + 3 ^ 40 * 1202634 * 2
def baseEnd_1202634 : Nat := 617529293439352922644193

theorem tailTrace_1202634 : CollatzResearch.WordTrace tailWord_1202634 prefixEnd_1202634 617529293439352922644193 := by
  unfold tailWord_1202634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965916381267471595023739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29242443683379924253396637 10965916381267471595023739)
  ·
    refine ⟨16448874571901207392535609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10965916381267471595023739 16448874571901207392535609)
    ·
      refine ⟨12336655928925905544401707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16448874571901207392535609 12336655928925905544401707)
      ·
        refine ⟨18504983893388858316602561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336655928925905544401707 18504983893388858316602561)
        ·
          refine ⟨13878737920041643737451921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18504983893388858316602561 13878737920041643737451921)
          ·
            refine ⟨10409053440031232803088941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13878737920041643737451921 10409053440031232803088941)
            ·
              refine ⟨3903395040011712301158353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10409053440031232803088941 3903395040011712301158353)
              ·
                refine ⟨2927546280008784225868765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903395040011712301158353 2927546280008784225868765)
                ·
                  refine ⟨1097829855003294084700787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2927546280008784225868765 1097829855003294084700787)
                  ·
                    refine ⟨1646744782504941127051181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1097829855003294084700787 1646744782504941127051181)
                    ·
                      refine ⟨617529293439352922644193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646744782504941127051181 617529293439352922644193)
                      ·
                        rfl

theorem cell23_1202634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1202634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202634 prefixEnd_1202634 := by exact prefixLift 1202634
  have htrace : WordTrace (prefixWord ++ tailWord_1202634) baseStart_1202634 baseEnd_1202634 := by
    simpa [prefixWord, tailWord_1202634, baseEnd_1202634] using wordTrace_append hprefix tailTrace_1202634
  have hstable : (prefixWord ++ tailWord_1202634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202634).length < 2 ^ (prefixWord ++ tailWord_1202634).sum := by decide
  have hdescent : baseEnd_1202634 < baseStart_1202634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202658 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1202658 : Nat := 118140960795 + 1202658 * 2 ^ 59
def prefixEnd_1202658 : Nat := 4983230072969 + 3 ^ 40 * 1202658 * 2
def baseEnd_1202658 : Nat := 68615735219451203193787

theorem tailTrace_1202658 : CollatzResearch.WordTrace tailWord_1202658 prefixEnd_1202658 68615735219451203193787 := by
  unfold tailWord_1202658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966135219245734619742157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29243027251321958985979085 10966135219245734619742157)
  ·
    refine ⟨4112300707217150482403309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10966135219245734619742157 4112300707217150482403309)
    ·
      refine ⟨1542112765206431430901241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4112300707217150482403309 1542112765206431430901241)
      ·
        refine ⟨1156584573904823573175931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542112765206431430901241 1156584573904823573175931)
        ·
          refine ⟨1734876860857235359763897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156584573904823573175931 1734876860857235359763897)
          ·
            refine ⟨1301157645642926519822923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734876860857235359763897 1301157645642926519822923)
            ·
              refine ⟨1951736468464389779734385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301157645642926519822923 1951736468464389779734385)
              ·
                refine ⟨1463802351348292334800789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1951736468464389779734385 1463802351348292334800789)
                ·
                  refine ⟨68615735219451203193787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1463802351348292334800789 68615735219451203193787)
                  ·
                    rfl

theorem cell23_1202658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1202658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202658 prefixEnd_1202658 := by exact prefixLift 1202658
  have htrace : WordTrace (prefixWord ++ tailWord_1202658) baseStart_1202658 baseEnd_1202658 := by
    simpa [prefixWord, tailWord_1202658, baseEnd_1202658] using wordTrace_append hprefix tailTrace_1202658
  have hstable : (prefixWord ++ tailWord_1202658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202658).length < 2 ^ (prefixWord ++ tailWord_1202658).sum := by decide
  have hdescent : baseEnd_1202658 < baseStart_1202658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202667 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 4, 4]
def baseStart_1202667 : Nat := 118140960795 + 1202667 * 2 ^ 59
def prefixEnd_1202667 : Nat := 4983230072969 + 3 ^ 40 * 1202667 * 2
def baseEnd_1202667 : Nat := 205848746100317097843847

theorem tailTrace_1202667 : CollatzResearch.WordTrace tailWord_1202667 prefixEnd_1202667 205848746100317097843847 := by
  unfold tailWord_1202667
  simp only [CollatzResearch.WordTrace]
  refine ⟨43864869133950333016046255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29243246089300222010697503 43864869133950333016046255)
  ·
    refine ⟨65797303700925499524069383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43864869133950333016046255 65797303700925499524069383)
    ·
      refine ⟨98695955551388249286104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65797303700925499524069383 98695955551388249286104075)
      ·
        refine ⟨148043933327082373929156113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98695955551388249286104075 148043933327082373929156113)
        ·
          refine ⟨111032949995311780446867085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148043933327082373929156113 111032949995311780446867085)
          ·
            refine ⟨41637356248241917667575157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111032949995311780446867085 41637356248241917667575157)
            ·
              refine ⟨3903502148272679781335171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41637356248241917667575157 3903502148272679781335171)
              ·
                refine ⟨5855253222409019672002757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903502148272679781335171 5855253222409019672002757)
                ·
                  refine ⟨1097859979201691188500517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5855253222409019672002757 1097859979201691188500517)
                  ·
                    refine ⟨205848746100317097843847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097859979201691188500517 205848746100317097843847)
                    ·
                      rfl

theorem cell23_1202667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 4].length) (baseStart_1202667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202667 prefixEnd_1202667 := by exact prefixLift 1202667
  have htrace : WordTrace (prefixWord ++ tailWord_1202667) baseStart_1202667 baseEnd_1202667 := by
    simpa [prefixWord, tailWord_1202667, baseEnd_1202667] using wordTrace_append hprefix tailTrace_1202667
  have hstable : (prefixWord ++ tailWord_1202667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202667).length < 2 ^ (prefixWord ++ tailWord_1202667).sum := by decide
  have hdescent : baseEnd_1202667 < baseStart_1202667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202680 : List Nat := [2, 1, 2, 1, 1, 4, 2, 10]
def baseStart_1202680 : Nat := 118140960795 + 1202680 * 2 ^ 59
def prefixEnd_1202680 : Nat := 4983230072969 + 3 ^ 40 * 1202680 * 2
def baseEnd_1202680 : Nat := 22872330131461471950703

theorem tailTrace_1202680 : CollatzResearch.WordTrace tailWord_1202680 prefixEnd_1202680 22872330131461471950703 := by
  unfold tailWord_1202680
  simp only [CollatzResearch.WordTrace]
  refine ⟨21932671641451618118134747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29243562188602157490846329 21932671641451618118134747)
  ·
    refine ⟨32899007462177427177202121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21932671641451618118134747 32899007462177427177202121)
    ·
      refine ⟨24674255596633070382901591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32899007462177427177202121 24674255596633070382901591)
      ·
        refine ⟨37011383394949605574352387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24674255596633070382901591 37011383394949605574352387)
        ·
          refine ⟨55517075092424408361528581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37011383394949605574352387 55517075092424408361528581)
          ·
            refine ⟨10409451579829576567786609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55517075092424408361528581 10409451579829576567786609)
            ·
              refine ⟨7807088684872182425839957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10409451579829576567786609 7807088684872182425839957)
              ·
                refine ⟨22872330131461471950703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7807088684872182425839957 22872330131461471950703)
                ·
                  rfl

theorem cell23_1202680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 10].length) (baseStart_1202680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202680 prefixEnd_1202680 := by exact prefixLift 1202680
  have htrace : WordTrace (prefixWord ++ tailWord_1202680) baseStart_1202680 baseEnd_1202680 := by
    simpa [prefixWord, tailWord_1202680, baseEnd_1202680] using wordTrace_append hprefix tailTrace_1202680
  have hstable : (prefixWord ++ tailWord_1202680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202680).length < 2 ^ (prefixWord ++ tailWord_1202680).sum := by decide
  have hdescent : baseEnd_1202680 < baseStart_1202680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202707 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3]
def baseStart_1202707 : Nat := 118140960795 + 1202707 * 2 ^ 59
def prefixEnd_1202707 : Nat := 4983230072969 + 3 ^ 40 * 1202707 * 2
def baseEnd_1202707 : Nat := 617566777527131137031357

theorem tailTrace_1202707 : CollatzResearch.WordTrace tailWord_1202707 prefixEnd_1202707 617566777527131137031357 := by
  unfold tailWord_1202707
  simp only [CollatzResearch.WordTrace]
  refine ⟨43866328053805419847502375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29244218702536946565001583 43866328053805419847502375)
  ·
    refine ⟨65799492080708129771253563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43866328053805419847502375 65799492080708129771253563)
    ·
      refine ⟨98699238121062194656880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65799492080708129771253563 98699238121062194656880345)
      ·
        refine ⟨74024428590796645992660259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98699238121062194656880345 74024428590796645992660259)
        ·
          refine ⟨111036642886194968988990389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74024428590796645992660259 111036642886194968988990389)
          ·
            refine ⟨10409685270580778342717849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111036642886194968988990389 10409685270580778342717849)
            ·
              refine ⟨7807263952935583757038387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10409685270580778342717849 7807263952935583757038387)
              ·
                refine ⟨11710895929403375635557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7807263952935583757038387 11710895929403375635557581)
                ·
                  refine ⟨4391585973526265863334093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11710895929403375635557581 4391585973526265863334093)
                  ·
                    refine ⟨1646844740072349698750285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4391585973526265863334093 1646844740072349698750285)
                    ·
                      refine ⟨617566777527131137031357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646844740072349698750285 617566777527131137031357)
                      ·
                        rfl

theorem cell23_1202707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_1202707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202707 prefixEnd_1202707 := by exact prefixLift 1202707
  have htrace : WordTrace (prefixWord ++ tailWord_1202707) baseStart_1202707 baseEnd_1202707 := by
    simpa [prefixWord, tailWord_1202707, baseEnd_1202707] using wordTrace_append hprefix tailTrace_1202707
  have hstable : (prefixWord ++ tailWord_1202707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202707).length < 2 ^ (prefixWord ++ tailWord_1202707).sum := by decide
  have hdescent : baseEnd_1202707 < baseStart_1202707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202711 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1202711 : Nat := 118140960795 + 1202711 * 2 ^ 59
def prefixEnd_1202711 : Nat := 4983230072969 + 3 ^ 40 * 1202711 * 2
def baseEnd_1202711 : Nat := 617568831449749121381339

theorem tailTrace_1202711 : CollatzResearch.WordTrace tailWord_1202711 prefixEnd_1202711 617568831449749121381339 := by
  unfold tailWord_1202711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43866473945790928530647987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29244315963860619020431991 43866473945790928530647987)
  ·
    refine ⟨65799710918686392795971981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43866473945790928530647987 65799710918686392795971981)
    ·
      refine ⟨24674891594507397298489493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65799710918686392795971981 24674891594507397298489493)
      ·
        refine ⟨1156635543492534248366695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24674891594507397298489493 1156635543492534248366695)
        ·
          refine ⟨1734953315238801372550043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156635543492534248366695 1734953315238801372550043)
          ·
            refine ⟨2602429972858202058825065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734953315238801372550043 2602429972858202058825065)
            ·
              refine ⟨1951822479643651544118799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602429972858202058825065 1951822479643651544118799)
              ·
                refine ⟨2927733719465477316178199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951822479643651544118799 2927733719465477316178199)
                ·
                  refine ⟨4391600579198215974267299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927733719465477316178199 4391600579198215974267299)
                  ·
                    refine ⟨6587400868797323961400949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391600579198215974267299 6587400868797323961400949)
                    ·
                      refine ⟨617568831449749121381339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6587400868797323961400949 617568831449749121381339)
                      ·
                        rfl

theorem cell23_1202711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1202711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202711 prefixEnd_1202711 := by exact prefixLift 1202711
  have htrace : WordTrace (prefixWord ++ tailWord_1202711) baseStart_1202711 baseEnd_1202711 := by
    simpa [prefixWord, tailWord_1202711, baseEnd_1202711] using wordTrace_append hprefix tailTrace_1202711
  have hstable : (prefixWord ++ tailWord_1202711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202711).length < 2 ^ (prefixWord ++ tailWord_1202711).sum := by decide
  have hdescent : baseEnd_1202711 < baseStart_1202711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202741 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1202741 : Nat := 118140960795 + 1202741 * 2 ^ 59
def prefixEnd_1202741 : Nat := 4983230072969 + 3 ^ 40 * 1202741 * 2
def baseEnd_1202741 : Nat := 617584235869384004006201

theorem tailTrace_1202741 : CollatzResearch.WordTrace tailWord_1202741 prefixEnd_1202741 617584235869384004006201 := by
  unfold tailWord_1202741
  simp only [CollatzResearch.WordTrace]
  refine ⟨43867568135682243654240077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29245045423788162436160051 43867568135682243654240077)
  ·
    refine ⟨16450338050880841370340029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43867568135682243654240077 16450338050880841370340029)
    ·
      refine ⟨6168876769080315513877511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16450338050880841370340029 6168876769080315513877511)
      ·
        refine ⟨9253315153620473270816267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6168876769080315513877511 9253315153620473270816267)
        ·
          refine ⟨13879972730430709906224401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9253315153620473270816267 13879972730430709906224401)
          ·
            refine ⟨10409979547823032429668301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13879972730430709906224401 10409979547823032429668301)
            ·
              refine ⟨3903742330433637161125613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10409979547823032429668301 3903742330433637161125613)
              ·
                refine ⟨1463903373912613935422105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3903742330433637161125613 1463903373912613935422105)
                ·
                  refine ⟨1097927530434460451566579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463903373912613935422105 1097927530434460451566579)
                  ·
                    refine ⟨1646891295651690677349869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1097927530434460451566579 1646891295651690677349869)
                    ·
                      refine ⟨617584235869384004006201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646891295651690677349869 617584235869384004006201)
                      ·
                        rfl

theorem cell23_1202741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1202741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202741 prefixEnd_1202741 := by exact prefixLift 1202741
  have htrace : WordTrace (prefixWord ++ tailWord_1202741) baseStart_1202741 baseEnd_1202741 := by
    simpa [prefixWord, tailWord_1202741, baseEnd_1202741] using wordTrace_append hprefix tailTrace_1202741
  have hstable : (prefixWord ++ tailWord_1202741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202741).length < 2 ^ (prefixWord ++ tailWord_1202741).sum := by decide
  have hdescent : baseEnd_1202741 < baseStart_1202741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202758 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1202758 : Nat := 118140960795 + 1202758 * 2 ^ 59
def prefixEnd_1202758 : Nat := 4983230072969 + 3 ^ 40 * 1202758 * 2
def baseEnd_1202758 : Nat := 617592965040510437493623

theorem tailTrace_1202758 : CollatzResearch.WordTrace tailWord_1202758 prefixEnd_1202758 617592965040510437493623 := by
  unfold tailWord_1202758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370880880519395486175279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29245458784413770371739285 1370880880519395486175279)
  ·
    refine ⟨2056321320779093229262919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370880880519395486175279 2056321320779093229262919)
    ·
      refine ⟨3084481981168639843894379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056321320779093229262919 3084481981168639843894379)
      ·
        refine ⟨4626722971752959765841569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084481981168639843894379 4626722971752959765841569)
        ·
          refine ⟨3470042228814719824381177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4626722971752959765841569 3470042228814719824381177)
          ·
            refine ⟨2602531671611039868285883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3470042228814719824381177 2602531671611039868285883)
            ·
              refine ⟨3903797507416559802428825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602531671611039868285883 3903797507416559802428825)
              ·
                refine ⟨2927848130562419851821619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903797507416559802428825 2927848130562419851821619)
                ·
                  refine ⟨4391772195843629777732429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927848130562419851821619 4391772195843629777732429)
                  ·
                    refine ⟨1646914573441361166649661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4391772195843629777732429 1646914573441361166649661)
                    ·
                      refine ⟨617592965040510437493623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1646914573441361166649661 617592965040510437493623)
                      ·
                        rfl

theorem cell23_1202758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1202758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202758 prefixEnd_1202758 := by exact prefixLift 1202758
  have htrace : WordTrace (prefixWord ++ tailWord_1202758) baseStart_1202758 baseEnd_1202758 := by
    simpa [prefixWord, tailWord_1202758, baseEnd_1202758] using wordTrace_append hprefix tailTrace_1202758
  have hstable : (prefixWord ++ tailWord_1202758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202758).length < 2 ^ (prefixWord ++ tailWord_1202758).sum := by decide
  have hdescent : baseEnd_1202758 < baseStart_1202758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202767 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_1202767 : Nat := 118140960795 + 1202767 * 2 ^ 59
def prefixEnd_1202767 : Nat := 4983230072969 + 3 ^ 40 * 1202767 * 2
def baseEnd_1202767 : Nat := 617597586366400902281081

theorem tailTrace_1202767 : CollatzResearch.WordTrace tailWord_1202767 prefixEnd_1202767 617597586366400902281081 := by
  unfold tailWord_1202767
  simp only [CollatzResearch.WordTrace]
  refine ⟨43868516433588050094686555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29245677622392033396457703 43868516433588050094686555)
  ·
    refine ⟨65802774650382075142029833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43868516433588050094686555 65802774650382075142029833)
    ·
      refine ⟨49352080987786556356522375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65802774650382075142029833 49352080987786556356522375)
      ·
        refine ⟨74028121481679834534783563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49352080987786556356522375 74028121481679834534783563)
        ·
          refine ⟨111042182222519751802175345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74028121481679834534783563 111042182222519751802175345)
          ·
            refine ⟨83281636666889813851631509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111042182222519751802175345 83281636666889813851631509)
            ·
              refine ⟨3903826718760460024295227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83281636666889813851631509 3903826718760460024295227)
              ·
                refine ⟨5855740078140690036442841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903826718760460024295227 5855740078140690036442841)
                ·
                  refine ⟨4391805058605517527332131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855740078140690036442841 4391805058605517527332131)
                  ·
                    refine ⟨6587707587908276290998197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4391805058605517527332131 6587707587908276290998197)
                    ·
                      refine ⟨617597586366400902281081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6587707587908276290998197 617597586366400902281081)
                      ·
                        rfl

theorem cell23_1202767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_1202767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202767 prefixEnd_1202767 := by exact prefixLift 1202767
  have htrace : WordTrace (prefixWord ++ tailWord_1202767) baseStart_1202767 baseEnd_1202767 := by
    simpa [prefixWord, tailWord_1202767, baseEnd_1202767] using wordTrace_append hprefix tailTrace_1202767
  have hstable : (prefixWord ++ tailWord_1202767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202767).length < 2 ^ (prefixWord ++ tailWord_1202767).sum := by decide
  have hdescent : baseEnd_1202767 < baseStart_1202767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202787 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 7]
def baseStart_1202787 : Nat := 118140960795 + 1202787 * 2 ^ 59
def prefixEnd_1202787 : Nat := 4983230072969 + 3 ^ 40 * 1202787 * 2
def baseEnd_1202787 : Nat := 68623095108832313781221

theorem tailTrace_1202787 : CollatzResearch.WordTrace tailWord_1202787 prefixEnd_1202787 68623095108832313781221 := by
  unfold tailWord_1202787
  simp only [CollatzResearch.WordTrace]
  refine ⟨43869245893515593510414615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29246163929010395673609743 43869245893515593510414615)
  ·
    refine ⟨65803868840273390265621923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43869245893515593510414615 65803868840273390265621923)
    ·
      refine ⟨98705803260410085398432885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65803868840273390265621923 98705803260410085398432885)
      ·
        refine ⟨9253669055663445506103083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98705803260410085398432885 9253669055663445506103083)
        ·
          refine ⟨13880503583495168259154625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9253669055663445506103083 13880503583495168259154625)
          ·
            refine ⟨10410377687621376194365969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13880503583495168259154625 10410377687621376194365969)
            ·
              refine ⟨7807783265716032145774477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10410377687621376194365969 7807783265716032145774477)
              ·
                refine ⟨2927918724643512054665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7807783265716032145774477 2927918724643512054665429)
                ·
                  refine ⟨68623095108832313781221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2927918724643512054665429 68623095108832313781221)
                  ·
                    rfl

theorem cell23_1202787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 7].length) (baseStart_1202787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202787 prefixEnd_1202787 := by exact prefixLift 1202787
  have htrace : WordTrace (prefixWord ++ tailWord_1202787) baseStart_1202787 baseEnd_1202787 := by
    simpa [prefixWord, tailWord_1202787, baseEnd_1202787] using wordTrace_append hprefix tailTrace_1202787
  have hstable : (prefixWord ++ tailWord_1202787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202787).length < 2 ^ (prefixWord ++ tailWord_1202787).sum := by decide
  have hdescent : baseEnd_1202787 < baseStart_1202787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202794 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1202794 : Nat := 118140960795 + 1202794 * 2 ^ 59
def prefixEnd_1202794 : Nat := 4983230072969 + 3 ^ 40 * 1202794 * 2
def baseEnd_1202794 : Nat := 617611450344072296643457

theorem tailTrace_1202794 : CollatzResearch.WordTrace tailWord_1202794 prefixEnd_1202794 617611450344072296643457 := by
  unfold tailWord_1202794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967375301122558426479859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29246334136326822470612957 10967375301122558426479859)
  ·
    refine ⟨16451062951683837639719789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10967375301122558426479859 16451062951683837639719789)
    ·
      refine ⟨6169148606881439114894921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16451062951683837639719789 6169148606881439114894921)
      ·
        refine ⟨4626861455161079336171191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169148606881439114894921 4626861455161079336171191)
        ·
          refine ⟨6940292182741619004256787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626861455161079336171191 6940292182741619004256787)
          ·
            refine ⟨10410438274112428506385181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6940292182741619004256787 10410438274112428506385181)
            ·
              refine ⟨3903914352792160689894443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10410438274112428506385181 3903914352792160689894443)
              ·
                refine ⟨5855871529188241034841665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903914352792160689894443 5855871529188241034841665)
                ·
                  refine ⟨4391903646891180776131249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5855871529188241034841665 4391903646891180776131249)
                  ·
                    refine ⟨3293927735168385582098437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4391903646891180776131249 3293927735168385582098437)
                    ·
                      refine ⟨617611450344072296643457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3293927735168385582098437 617611450344072296643457)
                      ·
                        rfl

theorem cell23_1202794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1202794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202794 prefixEnd_1202794 := by exact prefixLift 1202794
  have htrace : WordTrace (prefixWord ++ tailWord_1202794) baseStart_1202794 baseEnd_1202794 := by
    simpa [prefixWord, tailWord_1202794, baseEnd_1202794] using wordTrace_append hprefix tailTrace_1202794
  have hstable : (prefixWord ++ tailWord_1202794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202794).length < 2 ^ (prefixWord ++ tailWord_1202794).sum := by decide
  have hdescent : baseEnd_1202794 < baseStart_1202794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202798 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1202798 : Nat := 118140960795 + 1202798 * 2 ^ 59
def prefixEnd_1202798 : Nat := 4983230072969 + 3 ^ 40 * 1202798 * 2
def baseEnd_1202798 : Nat := 617613504266690280993439

theorem tailTrace_1202798 : CollatzResearch.WordTrace tailWord_1202798 prefixEnd_1202798 617613504266690280993439 := by
  unfold tailWord_1202798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483705887059467798633131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29246431397650494926043365 5483705887059467798633131)
  ·
    refine ⟨8225558830589201697949697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5483705887059467798633131 8225558830589201697949697)
    ·
      refine ⟨6169169122941901273462273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8225558830589201697949697 6169169122941901273462273)
      ·
        refine ⟨4626876842206425955096705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169169122941901273462273 4626876842206425955096705)
        ·
          refine ⟨3470157631654819466322529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4626876842206425955096705 3470157631654819466322529)
          ·
            refine ⟨2602618223741114599741897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3470157631654819466322529 2602618223741114599741897)
            ·
              refine ⟨1951963667805835949806423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602618223741114599741897 1951963667805835949806423)
              ·
                refine ⟨2927945501708753924709635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951963667805835949806423 2927945501708753924709635)
                ·
                  refine ⟨4391918252563130887064453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2927945501708753924709635 4391918252563130887064453)
                  ·
                    refine ⟨823484672355587041324585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4391918252563130887064453 823484672355587041324585)
                    ·
                      refine ⟨617613504266690280993439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823484672355587041324585 617613504266690280993439)
                      ·
                        rfl

theorem cell23_1202798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1202798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202798 prefixEnd_1202798 := by exact prefixLift 1202798
  have htrace : WordTrace (prefixWord ++ tailWord_1202798) baseStart_1202798 baseEnd_1202798 := by
    simpa [prefixWord, tailWord_1202798, baseEnd_1202798] using wordTrace_append hprefix tailTrace_1202798
  have hstable : (prefixWord ++ tailWord_1202798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202798).length < 2 ^ (prefixWord ++ tailWord_1202798).sum := by decide
  have hdescent : baseEnd_1202798 < baseStart_1202798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202821 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 5]
def baseStart_1202821 : Nat := 118140960795 + 1202821 * 2 ^ 59
def prefixEnd_1202821 : Nat := 4983230072969 + 3 ^ 40 * 1202821 * 2
def baseEnd_1202821 : Nat := 68625034924638187889537

theorem tailTrace_1202821 : CollatzResearch.WordTrace tailWord_1202821 prefixEnd_1202821 68625034924638187889537 := by
  unfold tailWord_1202821
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870485975392417317152317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29246990650261611544768211 43870485975392417317152317)
  ·
    refine ⟨16451432240772156493932119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43870485975392417317152317 16451432240772156493932119)
    ·
      refine ⟨24677148361158234740898179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16451432240772156493932119 24677148361158234740898179)
      ·
        refine ⟨37015722541737352111347269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24677148361158234740898179 37015722541737352111347269)
        ·
          refine ⟨6940447976575753520877613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37015722541737352111347269 6940447976575753520877613)
          ·
            refine ⟨2602667991215907570329105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6940447976575753520877613 2602667991215907570329105)
            ·
              refine ⟨1952000993411930677746829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602667991215907570329105 1952000993411930677746829)
              ·
                refine ⟨732000372529474004155061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1952000993411930677746829 732000372529474004155061)
                ·
                  refine ⟨68625034924638187889537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732000372529474004155061 68625034924638187889537)
                  ·
                    rfl

theorem cell23_1202821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_1202821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202821 prefixEnd_1202821 := by exact prefixLift 1202821
  have htrace : WordTrace (prefixWord ++ tailWord_1202821) baseStart_1202821 baseEnd_1202821 := by
    simpa [prefixWord, tailWord_1202821, baseEnd_1202821] using wordTrace_append hprefix tailTrace_1202821
  have hstable : (prefixWord ++ tailWord_1202821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202821).length < 2 ^ (prefixWord ++ tailWord_1202821).sum := by decide
  have hdescent : baseEnd_1202821 < baseStart_1202821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202827 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_1202827 : Nat := 118140960795 + 1202827 * 2 ^ 59
def prefixEnd_1202827 : Nat := 4983230072969 + 3 ^ 40 * 1202827 * 2
def baseEnd_1202827 : Nat := 617628395205670667530805

theorem tailTrace_1202827 : CollatzResearch.WordTrace tailWord_1202827 prefixEnd_1202827 617628395205670667530805 := by
  unfold tailWord_1202827
  simp only [CollatzResearch.WordTrace]
  refine ⟨43870704813370680341870735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29247136542247120227913823 43870704813370680341870735)
  ·
    refine ⟨65806057220056020512806103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43870704813370680341870735 65806057220056020512806103)
    ·
      refine ⟨98709085830084030769209155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65806057220056020512806103 98709085830084030769209155)
      ·
        refine ⟨148063628745126046153813733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98709085830084030769209155 148063628745126046153813733)
        ·
          refine ⟨27761930389711133653840075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148063628745126046153813733 27761930389711133653840075)
          ·
            refine ⟨41642895584566700480760113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27761930389711133653840075 41642895584566700480760113)
            ·
              refine ⟨31232171688425025360570085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41642895584566700480760113 31232171688425025360570085)
              ·
                refine ⟨5856032191579692255106891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31232171688425025360570085 5856032191579692255106891)
                ·
                  refine ⟨8784048287369538382660337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856032191579692255106891 8784048287369538382660337)
                  ·
                    refine ⟨6588036215527153786995253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8784048287369538382660337 6588036215527153786995253)
                    ·
                      refine ⟨617628395205670667530805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6588036215527153786995253 617628395205670667530805)
                      ·
                        rfl

theorem cell23_1202827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_1202827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202827 prefixEnd_1202827 := by exact prefixLift 1202827
  have htrace : WordTrace (prefixWord ++ tailWord_1202827) baseStart_1202827 baseEnd_1202827 := by
    simpa [prefixWord, tailWord_1202827, baseEnd_1202827] using wordTrace_append hprefix tailTrace_1202827
  have hstable : (prefixWord ++ tailWord_1202827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202827).length < 2 ^ (prefixWord ++ tailWord_1202827).sum := by decide
  have hdescent : baseEnd_1202827 < baseStart_1202827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202874 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_1202874 : Nat := 118140960795 + 1202874 * 2 ^ 59
def prefixEnd_1202874 : Nat := 4983230072969 + 3 ^ 40 * 1202874 * 2
def baseEnd_1202874 : Nat := 617652528796431983643089

theorem tailTrace_1202874 : CollatzResearch.WordTrace tailWord_1202874 prefixEnd_1202874 617652528796431983643089 := by
  unfold tailWord_1202874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968104761050101842207919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29248279362800271579221117 10968104761050101842207919)
  ·
    refine ⟨16452157141575152763311879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968104761050101842207919 16452157141575152763311879)
    ·
      refine ⟨24678235712362729144967819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16452157141575152763311879 24678235712362729144967819)
      ·
        refine ⟨37017353568544093717451729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24678235712362729144967819 37017353568544093717451729)
        ·
          refine ⟨27763015176408070288088797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37017353568544093717451729 27763015176408070288088797)
          ·
            refine ⟨10411130691153026358033299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27763015176408070288088797 10411130691153026358033299)
            ·
              refine ⟨15616696036729539537049949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10411130691153026358033299 15616696036729539537049949)
              ·
                refine ⟨5856261013773577326393731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15616696036729539537049949 5856261013773577326393731)
                ·
                  refine ⟨8784391520660365989590597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856261013773577326393731 8784391520660365989590597)
                  ·
                    refine ⟨1647073410123818623048237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8784391520660365989590597 1647073410123818623048237)
                    ·
                      refine ⟨617652528796431983643089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1647073410123818623048237 617652528796431983643089)
                      ·
                        rfl

theorem cell23_1202874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_1202874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202874 prefixEnd_1202874 := by exact prefixLift 1202874
  have htrace : WordTrace (prefixWord ++ tailWord_1202874) baseStart_1202874 baseEnd_1202874 := by
    simpa [prefixWord, tailWord_1202874, baseEnd_1202874] using wordTrace_append hprefix tailTrace_1202874
  have hstable : (prefixWord ++ tailWord_1202874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202874).length < 2 ^ (prefixWord ++ tailWord_1202874).sum := by decide
  have hdescent : baseEnd_1202874 < baseStart_1202874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202894 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_1202894 : Nat := 118140960795 + 1202894 * 2 ^ 59
def prefixEnd_1202894 : Nat := 4983230072969 + 3 ^ 40 * 1202894 * 2
def baseEnd_1202894 : Nat := 68629199823280211710333

theorem tailTrace_1202894 : CollatzResearch.WordTrace tailWord_1202894 prefixEnd_1202894 68629199823280211710333 := by
  unfold tailWord_1202894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484143563015993848069967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29248765669418633856373157 5484143563015993848069967)
  ·
    refine ⟨8226215344523990772104951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5484143563015993848069967 8226215344523990772104951)
    ·
      refine ⟨12339323016785986158157427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8226215344523990772104951 12339323016785986158157427)
      ·
        refine ⟨18508984525178979237236141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12339323016785986158157427 18508984525178979237236141)
        ·
          refine ⟨6940869196942117213963553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18508984525178979237236141 6940869196942117213963553)
          ·
            refine ⟨5205651897706587910472665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6940869196942117213963553 5205651897706587910472665)
            ·
              refine ⟨3904238923279940932854499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5205651897706587910472665 3904238923279940932854499)
              ·
                refine ⟨5856358384919911399281749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904238923279940932854499 5856358384919911399281749)
                ·
                  refine ⟨68629199823280211710333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5856358384919911399281749 68629199823280211710333)
                  ·
                    rfl

theorem cell23_1202894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_1202894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202894 prefixEnd_1202894 := by exact prefixLift 1202894
  have htrace : WordTrace (prefixWord ++ tailWord_1202894) baseStart_1202894 baseEnd_1202894 := by
    simpa [prefixWord, tailWord_1202894, baseEnd_1202894] using wordTrace_append hprefix tailTrace_1202894
  have hstable : (prefixWord ++ tailWord_1202894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202894).length < 2 ^ (prefixWord ++ tailWord_1202894).sum := by decide
  have hdescent : baseEnd_1202894 < baseStart_1202894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202911 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 6]
def baseStart_1202911 : Nat := 118140960795 + 1202911 * 2 ^ 59
def prefixEnd_1202911 : Nat := 4983230072969 + 3 ^ 40 * 1202911 * 2
def baseEnd_1202911 : Nat := 68630169731183148764491

theorem tailTrace_1202911 : CollatzResearch.WordTrace tailWord_1202911 prefixEnd_1202911 68630169731183148764491 := by
  unfold tailWord_1202911
  simp only [CollatzResearch.WordTrace]
  refine ⟨43873768545066362687928587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29249179030044241791952391 43873768545066362687928587)
  ·
    refine ⟨65810652817599544031892881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43873768545066362687928587 65810652817599544031892881)
    ·
      refine ⟨49357989613199658023919661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65810652817599544031892881 49357989613199658023919661)
      ·
        refine ⟨18509246104949871758969873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49357989613199658023919661 18509246104949871758969873)
        ·
          refine ⟨13881934578712403819227405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18509246104949871758969873 13881934578712403819227405)
          ·
            refine ⟨5205725467017151432210277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13881934578712403819227405 5205725467017151432210277)
            ·
              refine ⟨976073525065715893539427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5205725467017151432210277 976073525065715893539427)
              ·
                refine ⟨1464110287598573840309141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976073525065715893539427 1464110287598573840309141)
                ·
                  refine ⟨68630169731183148764491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1464110287598573840309141 68630169731183148764491)
                  ·
                    rfl

theorem cell23_1202911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 6].length) (baseStart_1202911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202911 prefixEnd_1202911 := by exact prefixLift 1202911
  have htrace : WordTrace (prefixWord ++ tailWord_1202911) baseStart_1202911 baseEnd_1202911 := by
    simpa [prefixWord, tailWord_1202911, baseEnd_1202911] using wordTrace_append hprefix tailTrace_1202911
  have hstable : (prefixWord ++ tailWord_1202911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202911).length < 2 ^ (prefixWord ++ tailWord_1202911).sum := by decide
  have hdescent : baseEnd_1202911 < baseStart_1202911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202921 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_1202921 : Nat := 118140960795 + 1202921 * 2 ^ 59
def prefixEnd_1202921 : Nat := 4983230072969 + 3 ^ 40 * 1202921 * 2
def baseEnd_1202921 : Nat := 617676662387193299755373

theorem tailTrace_1202921 : CollatzResearch.WordTrace tailWord_1202921 prefixEnd_1202921 617676662387193299755373 := by
  unfold tailWord_1202921
  simp only [CollatzResearch.WordTrace]
  refine ⟨43874133275030134395792617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29249422183353422930528411 43874133275030134395792617)
  ·
    refine ⟨32905599956272600796844463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43874133275030134395792617 32905599956272600796844463)
    ·
      refine ⟨49358399934408901195266695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32905599956272600796844463 49358399934408901195266695)
      ·
        refine ⟨74037599901613351792900043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49358399934408901195266695 74037599901613351792900043)
        ·
          refine ⟨111056399852420027689350065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74037599901613351792900043 111056399852420027689350065)
          ·
            refine ⟨83292299889315020767012549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111056399852420027689350065 83292299889315020767012549)
            ·
              refine ⟨15617306229246566393814853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83292299889315020767012549 15617306229246566393814853)
              ·
                refine ⟨2928244917983731198840285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15617306229246566393814853 2928244917983731198840285)
                ·
                  refine ⟨1098091844243899199565107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2928244917983731198840285 1098091844243899199565107)
                  ·
                    refine ⟨1647137766365848799347661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098091844243899199565107 1647137766365848799347661)
                    ·
                      refine ⟨617676662387193299755373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1647137766365848799347661 617676662387193299755373)
                      ·
                        rfl

theorem cell23_1202921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_1202921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202921 prefixEnd_1202921 := by exact prefixLift 1202921
  have htrace : WordTrace (prefixWord ++ tailWord_1202921) baseStart_1202921 baseEnd_1202921 := by
    simpa [prefixWord, tailWord_1202921, baseEnd_1202921] using wordTrace_append hprefix tailTrace_1202921
  have hstable : (prefixWord ++ tailWord_1202921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202921).length < 2 ^ (prefixWord ++ tailWord_1202921).sum := by decide
  have hdescent : baseEnd_1202921 < baseStart_1202921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202944 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1202944 : Nat := 118140960795 + 1202944 * 2 ^ 59
def prefixEnd_1202944 : Nat := 4983230072969 + 3 ^ 40 * 1202944 * 2
def baseEnd_1202944 : Nat := 617688472442246709767767

theorem tailTrace_1202944 : CollatzResearch.WordTrace tailWord_1202944 prefixEnd_1202944 617688472442246709767767 := by
  unfold tailWord_1202944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21937486076973404661939943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29249981435964539549253257 21937486076973404661939943)
  ·
    refine ⟨32906229115460106992909915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21937486076973404661939943 32906229115460106992909915)
    ·
      refine ⟨49359343673190160489364873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32906229115460106992909915 49359343673190160489364873)
      ·
        refine ⟨37019507754892620367023655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49359343673190160489364873 37019507754892620367023655)
        ·
          refine ⟨55529261632338930550535483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37019507754892620367023655 55529261632338930550535483)
          ·
            refine ⟨83293892448508395825803225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55529261632338930550535483 83293892448508395825803225)
            ·
              refine ⟨62470419336381296869352419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83293892448508395825803225 62470419336381296869352419)
              ·
                refine ⟨93705629004571945304028629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62470419336381296869352419 93705629004571945304028629)
                ·
                  refine ⟨2196225679794654968063171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93705629004571945304028629 2196225679794654968063171)
                  ·
                    refine ⟨3294338519691982452094757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2196225679794654968063171 3294338519691982452094757)
                    ·
                      refine ⟨617688472442246709767767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3294338519691982452094757 617688472442246709767767)
                      ·
                        rfl

theorem cell23_1202944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1202944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202944 prefixEnd_1202944 := by exact prefixLift 1202944
  have htrace : WordTrace (prefixWord ++ tailWord_1202944) baseStart_1202944 baseEnd_1202944 := by
    simpa [prefixWord, tailWord_1202944, baseEnd_1202944] using wordTrace_append hprefix tailTrace_1202944
  have hstable : (prefixWord ++ tailWord_1202944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202944).length < 2 ^ (prefixWord ++ tailWord_1202944).sum := by decide
  have hdescent : baseEnd_1202944 < baseStart_1202944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202948 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_1202948 : Nat := 118140960795 + 1202948 * 2 ^ 59
def prefixEnd_1202948 : Nat := 4983230072969 + 3 ^ 40 * 1202948 * 2
def baseEnd_1202948 : Nat := 617690526364864694117749

theorem tailTrace_1202948 : CollatzResearch.WordTrace tailWord_1202948 prefixEnd_1202948 617690526364864694117749 := by
  unfold tailWord_1202948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21937559022966159003512749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29250078697288212004683665 21937559022966159003512749)
  ·
    refine ⟨8226584633612309626317281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21937559022966159003512749 8226584633612309626317281)
    ·
      refine ⟨6169938475209232219737961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8226584633612309626317281 6169938475209232219737961)
      ·
        refine ⟨4627453856406924164803471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6169938475209232219737961 4627453856406924164803471)
        ·
          refine ⟨6941180784610386247205207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4627453856406924164803471 6941180784610386247205207)
          ·
            refine ⟨10411771176915579370807811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6941180784610386247205207 10411771176915579370807811)
            ·
              refine ⟨15617656765373369056211717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10411771176915579370807811 15617656765373369056211717)
              ·
                refine ⟨2928310643507506698039697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15617656765373369056211717 2928310643507506698039697)
                ·
                  refine ⟨2196232982630630023529773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2928310643507506698039697 2196232982630630023529773)
                  ·
                    refine ⟨823587368486486258823665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196232982630630023529773 823587368486486258823665)
                    ·
                      refine ⟨617690526364864694117749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823587368486486258823665 617690526364864694117749)
                      ·
                        rfl

theorem cell23_1202948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_1202948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202948 prefixEnd_1202948 := by exact prefixLift 1202948
  have htrace : WordTrace (prefixWord ++ tailWord_1202948) baseStart_1202948 baseEnd_1202948 := by
    simpa [prefixWord, tailWord_1202948, baseEnd_1202948] using wordTrace_append hprefix tailTrace_1202948
  have hstable : (prefixWord ++ tailWord_1202948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202948).length < 2 ^ (prefixWord ++ tailWord_1202948).sum := by decide
  have hdescent : baseEnd_1202948 < baseStart_1202948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202954 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1202954 : Nat := 118140960795 + 1202954 * 2 ^ 59
def prefixEnd_1202954 : Nat := 4983230072969 + 3 ^ 40 * 1202954 * 2
def baseEnd_1202954 : Nat := 205897869082930556880907

theorem tailTrace_1202954 : CollatzResearch.WordTrace tailWord_1202954 prefixEnd_1202954 205897869082930556880907 := by
  unfold tailWord_1202954
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968834220977645257935979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29250224589273720687829277 10968834220977645257935979)
  ·
    refine ⟨16453251331466467886903969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968834220977645257935979 16453251331466467886903969)
    ·
      refine ⟨12339938498599850915177977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16453251331466467886903969 12339938498599850915177977)
      ·
        refine ⟨9254953873949888186383483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12339938498599850915177977 9254953873949888186383483)
        ·
          refine ⟨13882430810924832279575225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9254953873949888186383483 13882430810924832279575225)
          ·
            refine ⟨10411823108193624209681419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13882430810924832279575225 10411823108193624209681419)
            ·
              refine ⟨15617734662290436314522129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10411823108193624209681419 15617734662290436314522129)
              ·
                refine ⟨11713300996717827235891597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15617734662290436314522129 11713300996717827235891597)
                ·
                  refine ⟨4392487873769185213459349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11713300996717827235891597 4392487873769185213459349)
                  ·
                    refine ⟨205897869082930556880907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4392487873769185213459349 205897869082930556880907)
                    ·
                      rfl

theorem cell23_1202954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1202954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202954 prefixEnd_1202954 := by exact prefixLift 1202954
  have htrace : WordTrace (prefixWord ++ tailWord_1202954) baseStart_1202954 baseEnd_1202954 := by
    simpa [prefixWord, tailWord_1202954, baseEnd_1202954] using wordTrace_append hprefix tailTrace_1202954
  have hstable : (prefixWord ++ tailWord_1202954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202954).length < 2 ^ (prefixWord ++ tailWord_1202954).sum := by decide
  have hdescent : baseEnd_1202954 < baseStart_1202954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202981 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_1202981 : Nat := 118140960795 + 1202981 * 2 ^ 59
def prefixEnd_1202981 : Nat := 4983230072969 + 3 ^ 40 * 1202981 * 2
def baseEnd_1202981 : Nat := 617707471226463065005097

theorem tailTrace_1202981 : CollatzResearch.WordTrace tailWord_1202981 prefixEnd_1202981 617707471226463065005097 := by
  unfold tailWord_1202981
  simp only [CollatzResearch.WordTrace]
  refine ⟨43876321654812764642976797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29250881103208509761984531 43876321654812764642976797)
  ·
    refine ⟨16453620620554786741116299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43876321654812764642976797 16453620620554786741116299)
    ·
      refine ⟨24680430930832180111674449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16453620620554786741116299 24680430930832180111674449)
      ·
        refine ⟨18510323198124135083755837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24680430930832180111674449 18510323198124135083755837)
        ·
          refine ⟨6941371199296550656408439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18510323198124135083755837 6941371199296550656408439)
          ·
            refine ⟨10412056798944825984612659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6941371199296550656408439 10412056798944825984612659)
            ·
              refine ⟨15618085198417238976918989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412056798944825984612659 15618085198417238976918989)
              ·
                refine ⟨5856781949406464616344621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15618085198417238976918989 5856781949406464616344621)
                ·
                  refine ⟨2196293231027424231129233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5856781949406464616344621 2196293231027424231129233)
                  ·
                    refine ⟨1647219923270568173346925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196293231027424231129233 1647219923270568173346925)
                    ·
                      refine ⟨617707471226463065005097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1647219923270568173346925 617707471226463065005097)
                      ·
                        rfl

theorem cell23_1202981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_1202981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202981 prefixEnd_1202981 := by exact prefixLift 1202981
  have htrace : WordTrace (prefixWord ++ tailWord_1202981) baseStart_1202981 baseEnd_1202981 := by
    simpa [prefixWord, tailWord_1202981, baseEnd_1202981] using wordTrace_append hprefix tailTrace_1202981
  have hstable : (prefixWord ++ tailWord_1202981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202981).length < 2 ^ (prefixWord ++ tailWord_1202981).sum := by decide
  have hdescent : baseEnd_1202981 < baseStart_1202981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202995 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 1, 1, 4]
def baseStart_1202995 : Nat := 118140960795 + 1202995 * 2 ^ 59
def prefixEnd_1202995 : Nat := 4983230072969 + 3 ^ 40 * 1202995 * 2
def baseEnd_1202995 : Nat := 617714659955626010230033

theorem tailTrace_1202995 : CollatzResearch.WordTrace tailWord_1202995 prefixEnd_1202995 617714659955626010230033 := by
  unfold tailWord_1202995
  simp only [CollatzResearch.WordTrace]
  refine ⟨43876832276762045033986439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29251221517841363355990959 43876832276762045033986439)
  ·
    refine ⟨65815248415143067550979659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43876832276762045033986439 65815248415143067550979659)
    ·
      refine ⟨98722872622714601326469489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65815248415143067550979659 98722872622714601326469489)
      ·
        refine ⟨74042154467035950994852117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98722872622714601326469489 74042154467035950994852117)
        ·
          refine ⟨3470725990642310202883693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74042154467035950994852117 3470725990642310202883693)
          ·
            refine ⟨1301522246490866326081385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3470725990642310202883693 1301522246490866326081385)
            ·
              refine ⟨976141684868149744561039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301522246490866326081385 976141684868149744561039)
              ·
                refine ⟨1464212527302224616841559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976141684868149744561039 1464212527302224616841559)
                ·
                  refine ⟨2196318790953336925262339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464212527302224616841559 2196318790953336925262339)
                  ·
                    refine ⟨3294478186430005387893509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2196318790953336925262339 3294478186430005387893509)
                    ·
                      refine ⟨617714659955626010230033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3294478186430005387893509 617714659955626010230033)
                      ·
                        rfl

theorem cell23_1202995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 1, 4].length) (baseStart_1202995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1202995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1202995 prefixEnd_1202995 := by exact prefixLift 1202995
  have htrace : WordTrace (prefixWord ++ tailWord_1202995) baseStart_1202995 baseEnd_1202995 := by
    simpa [prefixWord, tailWord_1202995, baseEnd_1202995] using wordTrace_append hprefix tailTrace_1202995
  have hstable : (prefixWord ++ tailWord_1202995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202995).length < 2 ^ (prefixWord ++ tailWord_1202995).sum := by decide
  have hdescent : baseEnd_1202995 < baseStart_1202995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1203004 : Nat := 118140960795 + 1203004 * 2 ^ 59
def prefixEnd_1203004 : Nat := 4983230072969 + 3 ^ 40 * 1203004 * 2
def baseEnd_1203004 : Nat := 617719281281516475017491

theorem tailTrace_1203004 : CollatzResearch.WordTrace tailWord_1203004 prefixEnd_1203004 617719281281516475017491 := by
  unfold tailWord_1203004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21938580266864719785532033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29251440355819626380709377 21938580266864719785532033)
  ·
    refine ⟨16453935200148539839149025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21938580266864719785532033 16453935200148539839149025)
    ·
      refine ⟨12340451400111404879361769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16453935200148539839149025 12340451400111404879361769)
      ·
        refine ⟨9255338550083553659521327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12340451400111404879361769 9255338550083553659521327)
        ·
          refine ⟨13883007825125330489281991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255338550083553659521327 13883007825125330489281991)
          ·
            refine ⟨20824511737687995733922987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13883007825125330489281991 20824511737687995733922987)
            ·
              refine ⟨31236767606531993600884481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20824511737687995733922987 31236767606531993600884481)
              ·
                refine ⟨23427575704898995200663361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31236767606531993600884481 23427575704898995200663361)
                ·
                  refine ⟨17570681778674246400497521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23427575704898995200663361 17570681778674246400497521)
                  ·
                    refine ⟨13178011334005684800373141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17570681778674246400497521 13178011334005684800373141)
                    ·
                      refine ⟨617719281281516475017491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13178011334005684800373141 617719281281516475017491)
                      ·
                        rfl

theorem cell23_1203004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1203004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203004 prefixEnd_1203004 := by exact prefixLift 1203004
  have htrace : WordTrace (prefixWord ++ tailWord_1203004) baseStart_1203004 baseEnd_1203004 := by
    simpa [prefixWord, tailWord_1203004, baseEnd_1203004] using wordTrace_append hprefix tailTrace_1203004
  have hstable : (prefixWord ++ tailWord_1203004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203004).length < 2 ^ (prefixWord ++ tailWord_1203004).sum := by decide
  have hdescent : baseEnd_1203004 < baseStart_1203004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203025 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_1203025 : Nat := 118140960795 + 1203025 * 2 ^ 59
def prefixEnd_1203025 : Nat := 4983230072969 + 3 ^ 40 * 1203025 * 2
def baseEnd_1203025 : Nat := 617730064375260892854895

theorem tailTrace_1203025 : CollatzResearch.WordTrace tailWord_1203025 prefixEnd_1203025 617730064375260892854895 := by
  unfold tailWord_1203025
  simp only [CollatzResearch.WordTrace]
  refine ⟨43877926466653360157578529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29251950977768906771719019 43877926466653360157578529)
  ·
    refine ⟨32908444849990020118183897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43877926466653360157578529 32908444849990020118183897)
    ·
      refine ⟨24681333637492515088637923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32908444849990020118183897 24681333637492515088637923)
      ·
        refine ⟨37022000456238772632956885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24681333637492515088637923 37022000456238772632956885)
        ·
          refine ⟨867703135693096233584927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37022000456238772632956885 867703135693096233584927)
          ·
            refine ⟨1301554703539644350377391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867703135693096233584927 1301554703539644350377391)
            ·
              refine ⟨1952332055309466525566087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301554703539644350377391 1952332055309466525566087)
              ·
                refine ⟨2928498082964199788349131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952332055309466525566087 2928498082964199788349131)
                ·
                  refine ⟨4392747124446299682523697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2928498082964199788349131 4392747124446299682523697)
                  ·
                    refine ⟨3294560343334724761892773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4392747124446299682523697 3294560343334724761892773)
                    ·
                      refine ⟨617730064375260892854895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3294560343334724761892773 617730064375260892854895)
                      ·
                        rfl

theorem cell23_1203025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_1203025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203025 prefixEnd_1203025 := by exact prefixLift 1203025
  have htrace : WordTrace (prefixWord ++ tailWord_1203025) baseStart_1203025 baseEnd_1203025 := by
    simpa [prefixWord, tailWord_1203025, baseEnd_1203025] using wordTrace_append hprefix tailTrace_1203025
  have hstable : (prefixWord ++ tailWord_1203025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203025).length < 2 ^ (prefixWord ++ tailWord_1203025).sum := by decide
  have hdescent : baseEnd_1203025 < baseStart_1203025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203064 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1203064 : Nat := 118140960795 + 1203064 * 2 ^ 59
def prefixEnd_1203064 : Nat := 4983230072969 + 3 ^ 40 * 1203064 * 2
def baseEnd_1203064 : Nat := 617750090120786240267215

theorem tailTrace_1203064 : CollatzResearch.WordTrace tailWord_1203064 prefixEnd_1203064 617750090120786240267215 := by
  unfold tailWord_1203064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21939674456756034909124123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29252899275674713212165497 21939674456756034909124123)
  ·
    refine ⟨32909511685134052363686185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21939674456756034909124123 32909511685134052363686185)
    ·
      refine ⟨24682133763850539272764639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32909511685134052363686185 24682133763850539272764639)
      ·
        refine ⟨37023200645775808909146959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24682133763850539272764639 37023200645775808909146959)
        ·
          refine ⟨55534800968663713363720439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37023200645775808909146959 55534800968663713363720439)
          ·
            refine ⟨83302201452995570045580659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55534800968663713363720439 83302201452995570045580659)
            ·
              refine ⟨124953302179493355068370989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83302201452995570045580659 124953302179493355068370989)
              ·
                refine ⟨46857488317310008150639121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124953302179493355068370989 46857488317310008150639121)
                ·
                  refine ⟨35143116237982506112979341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46857488317310008150639121 35143116237982506112979341)
                  ·
                    refine ⟨13178668589243439792367253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35143116237982506112979341 13178668589243439792367253)
                    ·
                      refine ⟨617750090120786240267215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13178668589243439792367253 617750090120786240267215)
                      ·
                        rfl

theorem cell23_1203064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1203064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203064 prefixEnd_1203064 := by exact prefixLift 1203064
  have htrace : WordTrace (prefixWord ++ tailWord_1203064) baseStart_1203064 baseEnd_1203064 := by
    simpa [prefixWord, tailWord_1203064, baseEnd_1203064] using wordTrace_append hprefix tailTrace_1203064
  have hstable : (prefixWord ++ tailWord_1203064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203064).length < 2 ^ (prefixWord ++ tailWord_1203064).sum := by decide
  have hdescent : baseEnd_1203064 < baseStart_1203064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203108 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 5]
def baseStart_1203108 : Nat := 118140960795 + 1203108 * 2 ^ 59
def prefixEnd_1203108 : Nat := 4983230072969 + 3 ^ 40 * 1203108 * 2
def baseEnd_1203108 : Nat := 68641409252176007568557

theorem tailTrace_1203108 : CollatzResearch.WordTrace tailWord_1203108 prefixEnd_1203108 68641409252176007568557 := by
  unfold tailWord_1203108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940476862676332666424989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29253969150235110221899985 21940476862676332666424989)
  ·
    refine ⟨8227678823503624749909371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21940476862676332666424989 8227678823503624749909371)
    ·
      refine ⟨12341518235255437124864057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8227678823503624749909371 12341518235255437124864057)
      ·
        refine ⟨9256138676441577843648043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12341518235255437124864057 9256138676441577843648043)
        ·
          refine ⟨13884208014662366765472065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9256138676441577843648043 13884208014662366765472065)
          ·
            refine ⟨10413156010996775074104049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13884208014662366765472065 10413156010996775074104049)
            ·
              refine ⟨7809867008247581305578037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10413156010996775074104049 7809867008247581305578037)
              ·
                refine ⟨732175032023210747397941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7809867008247581305578037 732175032023210747397941)
                ·
                  refine ⟨68641409252176007568557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732175032023210747397941 68641409252176007568557)
                  ·
                    rfl

theorem cell23_1203108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_1203108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203108 prefixEnd_1203108 := by exact prefixLift 1203108
  have htrace : WordTrace (prefixWord ++ tailWord_1203108) baseStart_1203108 baseEnd_1203108 := by
    simpa [prefixWord, tailWord_1203108, baseEnd_1203108] using wordTrace_append hprefix tailTrace_1203108
  have hstable : (prefixWord ++ tailWord_1203108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203108).length < 2 ^ (prefixWord ++ tailWord_1203108).sum := by decide
  have hdescent : baseEnd_1203108 < baseStart_1203108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203128 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_1203128 : Nat := 118140960795 + 1203128 * 2 ^ 59
def prefixEnd_1203128 : Nat := 4983230072969 + 3 ^ 40 * 1203128 * 2
def baseEnd_1203128 : Nat := 617782952882673989866921

theorem tailTrace_1203128 : CollatzResearch.WordTrace tailWord_1203128 prefixEnd_1203128 617782952882673989866921 := by
  unfold tailWord_1203128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21940841592640104374289019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29254455456853472499052025 21940841592640104374289019)
  ·
    refine ⟨32911262388960156561433529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21940841592640104374289019 32911262388960156561433529)
    ·
      refine ⟨24683446791720117421075147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32911262388960156561433529 24683446791720117421075147)
      ·
        refine ⟨37025170187580176131612721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24683446791720117421075147 37025170187580176131612721)
        ·
          refine ⟨27768877640685132098709541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37025170187580176131612721 27768877640685132098709541)
          ·
            refine ⟨5206664557628462268508039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27768877640685132098709541 5206664557628462268508039)
            ·
              refine ⟨7809996836442693402762059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206664557628462268508039 7809996836442693402762059)
              ·
                refine ⟨11714995254664040104143089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7809996836442693402762059 11714995254664040104143089)
                ·
                  refine ⟨8786246440998030078107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11714995254664040104143089 8786246440998030078107317)
                  ·
                    refine ⟨823710603843565319822561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8786246440998030078107317 823710603843565319822561)
                    ·
                      refine ⟨617782952882673989866921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823710603843565319822561 617782952882673989866921)
                      ·
                        rfl

theorem cell23_1203128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_1203128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203128 prefixEnd_1203128 := by exact prefixLift 1203128
  have htrace : WordTrace (prefixWord ++ tailWord_1203128) baseStart_1203128 baseEnd_1203128 := by
    simpa [prefixWord, tailWord_1203128, baseEnd_1203128] using wordTrace_append hprefix tailTrace_1203128
  have hstable : (prefixWord ++ tailWord_1203128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203128).length < 2 ^ (prefixWord ++ tailWord_1203128).sum := by decide
  have hdescent : baseEnd_1203128 < baseStart_1203128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203171 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1203171 : Nat := 118140960795 + 1203171 * 2 ^ 59
def prefixEnd_1203171 : Nat := 4983230072969 + 3 ^ 40 * 1203171 * 2
def baseEnd_1203171 : Nat := 617805032550817321629223

theorem tailTrace_1203171 : CollatzResearch.WordTrace tailWord_1203171 prefixEnd_1203171 617805032550817321629223 := by
  unfold tailWord_1203171
  simp only [CollatzResearch.WordTrace]
  refine ⟨43883251524124427092393367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29255501016082951394928911 43883251524124427092393367)
  ·
    refine ⟨65824877286186640638590051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43883251524124427092393367 65824877286186640638590051)
    ·
      refine ⟨98737315929279960957885077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65824877286186640638590051 98737315929279960957885077)
      ·
        refine ⟨4628311684184998169900863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98737315929279960957885077 4628311684184998169900863)
        ·
          refine ⟨6942467526277497254851295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628311684184998169900863 6942467526277497254851295)
          ·
            refine ⟨10413701289416245882276943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6942467526277497254851295 10413701289416245882276943)
            ·
              refine ⟨15620551934124368823415415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10413701289416245882276943 15620551934124368823415415)
              ·
                refine ⟨23430827901186553235123123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15620551934124368823415415 23430827901186553235123123)
                ·
                  refine ⟨35146241851779829852684685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23430827901186553235123123 35146241851779829852684685)
                  ·
                    refine ⟨13179840694417436194756757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35146241851779829852684685 13179840694417436194756757)
                    ·
                      refine ⟨617805032550817321629223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13179840694417436194756757 617805032550817321629223)
                      ·
                        rfl

theorem cell23_1203171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1203171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203171 prefixEnd_1203171 := by exact prefixLift 1203171
  have htrace : WordTrace (prefixWord ++ tailWord_1203171) baseStart_1203171 baseEnd_1203171 := by
    simpa [prefixWord, tailWord_1203171, baseEnd_1203171] using wordTrace_append hprefix tailTrace_1203171
  have hstable : (prefixWord ++ tailWord_1203171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203171).length < 2 ^ (prefixWord ++ tailWord_1203171).sum := by decide
  have hdescent : baseEnd_1203171 < baseStart_1203171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203175 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1203175 : Nat := 118140960795 + 1203175 * 2 ^ 59
def prefixEnd_1203175 : Nat := 4983230072969 + 3 ^ 40 * 1203175 * 2
def baseEnd_1203175 : Nat := 617807086473435305979205

theorem tailTrace_1203175 : CollatzResearch.WordTrace tailWord_1203175 prefixEnd_1203175 617807086473435305979205 := by
  unfold tailWord_1203175
  simp only [CollatzResearch.WordTrace]
  refine ⟨43883397416109935775538979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29255598277406623850359319 43883397416109935775538979)
  ·
    refine ⟨65825096124164903663308469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43883397416109935775538979 65825096124164903663308469)
    ·
      refine ⟨6171102761640459718435169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65825096124164903663308469 6171102761640459718435169)
      ·
        refine ⟨4628327071230344788826377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6171102761640459718435169 4628327071230344788826377)
        ·
          refine ⟨3471245303422758591619783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4628327071230344788826377 3471245303422758591619783)
          ·
            refine ⟨5206867955134137887429675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471245303422758591619783 5206867955134137887429675)
            ·
              refine ⟨7810301932701206831144513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5206867955134137887429675 7810301932701206831144513)
              ·
                refine ⟨5857726449525905123358385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810301932701206831144513 5857726449525905123358385)
                ·
                  refine ⟨4393294837144428842518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5857726449525905123358385 4393294837144428842518789)
                  ·
                    refine ⟨823742781964580407972273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4393294837144428842518789 823742781964580407972273)
                    ·
                      refine ⟨617807086473435305979205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823742781964580407972273 617807086473435305979205)
                      ·
                        rfl

theorem cell23_1203175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1203175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203175 prefixEnd_1203175 := by exact prefixLift 1203175
  have htrace : WordTrace (prefixWord ++ tailWord_1203175) baseStart_1203175 baseEnd_1203175 := by
    simpa [prefixWord, tailWord_1203175, baseEnd_1203175] using wordTrace_append hprefix tailTrace_1203175
  have hstable : (prefixWord ++ tailWord_1203175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203175).length < 2 ^ (prefixWord ++ tailWord_1203175).sum := by decide
  have hdescent : baseEnd_1203175 < baseStart_1203175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203185 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_1203185 : Nat := 118140960795 + 1203185 * 2 ^ 59
def prefixEnd_1203185 : Nat := 4983230072969 + 3 ^ 40 * 1203185 * 2
def baseEnd_1203185 : Nat := 205937407093326755618053

theorem tailTrace_1203185 : CollatzResearch.WordTrace tailWord_1203185 prefixEnd_1203185 205937407093326755618053 := by
  unfold tailWord_1203185
  simp only [CollatzResearch.WordTrace]
  refine ⟨43883762146073707483403009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29255841430715804988935339 43883762146073707483403009)
  ·
    refine ⟨32912821609555280612552257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43883762146073707483403009 32912821609555280612552257)
    ·
      refine ⟨24684616207166460459414193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32912821609555280612552257 24684616207166460459414193)
      ·
        refine ⟨18513462155374845344560645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24684616207166460459414193 18513462155374845344560645)
        ·
          refine ⟨3471274154132783502105121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18513462155374845344560645 3471274154132783502105121)
          ·
            refine ⟨2603455615599587626578841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471274154132783502105121 2603455615599587626578841)
            ·
              refine ⟨1952591711699690719934131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603455615599587626578841 1952591711699690719934131)
              ·
                refine ⟨2928887567549536079901197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952591711699690719934131 2928887567549536079901197)
                ·
                  refine ⟨1098332837831076029962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2928887567549536079901197 1098332837831076029962949)
                  ·
                    refine ⟨205937407093326755618053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1098332837831076029962949 205937407093326755618053)
                    ·
                      rfl

theorem cell23_1203185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_1203185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203185 prefixEnd_1203185 := by exact prefixLift 1203185
  have htrace : WordTrace (prefixWord ++ tailWord_1203185) baseStart_1203185 baseEnd_1203185 := by
    simpa [prefixWord, tailWord_1203185, baseEnd_1203185] using wordTrace_append hprefix tailTrace_1203185
  have hstable : (prefixWord ++ tailWord_1203185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203185).length < 2 ^ (prefixWord ++ tailWord_1203185).sum := by decide
  have hdescent : baseEnd_1203185 < baseStart_1203185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203235 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 4, 3, 2]
def baseStart_1203235 : Nat := 118140960795 + 1203235 * 2 ^ 59
def prefixEnd_1203235 : Nat := 4983230072969 + 3 ^ 40 * 1203235 * 2
def baseEnd_1203235 : Nat := 617837895312705071228929

theorem tailTrace_1203235 : CollatzResearch.WordTrace tailWord_1203235 prefixEnd_1203235 617837895312705071228929 := by
  unfold tailWord_1203235
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885585795892566022723159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29257057197261710681815439 43885585795892566022723159)
  ·
    refine ⟨65828378693838849034084739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43885585795892566022723159 65828378693838849034084739)
    ·
      refine ⟨98742568040758273551127109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65828378693838849034084739 98742568040758273551127109)
      ·
        refine ⟨18514231507642176290836333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98742568040758273551127109 18514231507642176290836333)
        ·
          refine ⟨6942836815365816109063625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18514231507642176290836333 6942836815365816109063625)
          ·
            refine ⟨5207127611524362081797719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6942836815365816109063625 5207127611524362081797719)
            ·
              refine ⟨7810691417286543122696579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5207127611524362081797719 7810691417286543122696579)
              ·
                refine ⟨11716037125929814684044869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7810691417286543122696579 11716037125929814684044869)
                ·
                  refine ⟨2196756961111840253258413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11716037125929814684044869 2196756961111840253258413)
                  ·
                    refine ⟨823783860416940094971905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2196756961111840253258413 823783860416940094971905)
                    ·
                      refine ⟨617837895312705071228929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 823783860416940094971905 617837895312705071228929)
                      ·
                        rfl

theorem cell23_1203235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_1203235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203235 prefixEnd_1203235 := by exact prefixLift 1203235
  have htrace : WordTrace (prefixWord ++ tailWord_1203235) baseStart_1203235 baseEnd_1203235 := by
    simpa [prefixWord, tailWord_1203235, baseEnd_1203235] using wordTrace_append hprefix tailTrace_1203235
  have hstable : (prefixWord ++ tailWord_1203235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203235).length < 2 ^ (prefixWord ++ tailWord_1203235).sum := by decide
  have hdescent : baseEnd_1203235 < baseStart_1203235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203248 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_1203248 : Nat := 118140960795 + 1203248 * 2 ^ 59
def prefixEnd_1203248 : Nat := 4983230072969 + 3 ^ 40 * 1203248 * 2
def baseEnd_1203248 : Nat := 617844570561213520366369

theorem tailTrace_1203248 : CollatzResearch.WordTrace tailWord_1203248 prefixEnd_1203248 617844570561213520366369 := by
  unfold tailWord_1203248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21943029972422734621473199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29257373296563646161964265 21943029972422734621473199)
  ·
    refine ⟨32914544958634101932209799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21943029972422734621473199 32914544958634101932209799)
    ·
      refine ⟨49371817437951152898314699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32914544958634101932209799 49371817437951152898314699)
      ·
        refine ⟨74057726156926729347472049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49371817437951152898314699 74057726156926729347472049)
        ·
          refine ⟨55543294617695047010604037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74057726156926729347472049 55543294617695047010604037)
          ·
            refine ⟨10414367740817821314488257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55543294617695047010604037 10414367740817821314488257)
            ·
              refine ⟨7810775805613365985866193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10414367740817821314488257 7810775805613365985866193)
              ·
                refine ⟨5858081854210024489399645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7810775805613365985866193 5858081854210024489399645)
                ·
                  refine ⟨2196780695328759183524867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5858081854210024489399645 2196780695328759183524867)
                  ·
                    refine ⟨3295171042993138775287301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2196780695328759183524867 3295171042993138775287301)
                    ·
                      refine ⟨617844570561213520366369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3295171042993138775287301 617844570561213520366369)
                      ·
                        rfl

theorem cell23_1203248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_1203248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203248 prefixEnd_1203248 := by exact prefixLift 1203248
  have htrace : WordTrace (prefixWord ++ tailWord_1203248) baseStart_1203248 baseEnd_1203248 := by
    simpa [prefixWord, tailWord_1203248, baseEnd_1203248] using wordTrace_append hprefix tailTrace_1203248
  have hstable : (prefixWord ++ tailWord_1203248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203248).length < 2 ^ (prefixWord ++ tailWord_1203248).sum := by decide
  have hdescent : baseEnd_1203248 < baseStart_1203248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203262 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1203262 : Nat := 118140960795 + 1203262 * 2 ^ 59
def prefixEnd_1203262 : Nat := 4983230072969 + 3 ^ 40 * 1203262 * 2
def baseEnd_1203262 : Nat := 205950586430125488530435

theorem tailTrace_1203262 : CollatzResearch.WordTrace tailWord_1203262 prefixEnd_1203262 205950586430125488530435 := by
  unfold tailWord_1203262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485821320849343704244505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29257713711196499755970693 5485821320849343704244505)
  ·
    refine ⟨4114365990637007778183379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5485821320849343704244505 4114365990637007778183379)
    ·
      refine ⟨6171548985955511667275069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4114365990637007778183379 6171548985955511667275069)
      ·
        refine ⟨2314330869733316875228151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6171548985955511667275069 2314330869733316875228151)
        ·
          refine ⟨3471496304599975312842227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314330869733316875228151 3471496304599975312842227)
          ·
            refine ⟨5207244456899962969263341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471496304599975312842227 5207244456899962969263341)
            ·
              refine ⟨1952716671337486113473753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5207244456899962969263341 1952716671337486113473753)
              ·
                refine ⟨1464537503503114585105315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952716671337486113473753 1464537503503114585105315)
                ·
                  refine ⟨2196806255254671877657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464537503503114585105315 2196806255254671877657973)
                  ·
                    refine ⟨205950586430125488530435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2196806255254671877657973 205950586430125488530435)
                    ·
                      rfl

theorem cell23_1203262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1203262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203262 prefixEnd_1203262 := by exact prefixLift 1203262
  have htrace : WordTrace (prefixWord ++ tailWord_1203262) baseStart_1203262 baseEnd_1203262 := by
    simpa [prefixWord, tailWord_1203262, baseEnd_1203262] using wordTrace_append hprefix tailTrace_1203262
  have hstable : (prefixWord ++ tailWord_1203262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203262).length < 2 ^ (prefixWord ++ tailWord_1203262).sum := by decide
  have hdescent : baseEnd_1203262 < baseStart_1203262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203292 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1203292 : Nat := 118140960795 + 1203292 * 2 ^ 59
def prefixEnd_1203292 : Nat := 4983230072969 + 3 ^ 40 * 1203292 * 2
def baseEnd_1203292 : Nat := 205955721236670449405389

theorem tailTrace_1203292 : CollatzResearch.WordTrace tailWord_1203292 prefixEnd_1203292 205955721236670449405389 := by
  unfold tailWord_1203292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21943832378343032378774065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29258443171124043171698753 21943832378343032378774065)
  ·
    refine ⟨16457874283757274284080549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21943832378343032378774065 16457874283757274284080549)
    ·
      refine ⟨3085851428204488928265103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16457874283757274284080549 3085851428204488928265103)
      ·
        refine ⟨4628777142306733392397655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085851428204488928265103 4628777142306733392397655)
        ·
          refine ⟨6943165713460100088596483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4628777142306733392397655 6943165713460100088596483)
          ·
            refine ⟨10414748570190150132894725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6943165713460100088596483 10414748570190150132894725)
            ·
              refine ⟨1952765356910653149917761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10414748570190150132894725 1952765356910653149917761)
              ·
                refine ⟨1464574017682989862438321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952765356910653149917761 1464574017682989862438321)
                ·
                  refine ⟨1098430513262242396828741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1464574017682989862438321 1098430513262242396828741)
                  ·
                    refine ⟨205955721236670449405389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1098430513262242396828741 205955721236670449405389)
                    ·
                      rfl

theorem cell23_1203292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1203292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203292 prefixEnd_1203292 := by exact prefixLift 1203292
  have htrace : WordTrace (prefixWord ++ tailWord_1203292) baseStart_1203292 baseEnd_1203292 := by
    simpa [prefixWord, tailWord_1203292, baseEnd_1203292] using wordTrace_append hprefix tailTrace_1203292
  have hstable : (prefixWord ++ tailWord_1203292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203292).length < 2 ^ (prefixWord ++ tailWord_1203292).sum := by decide
  have hdescent : baseEnd_1203292 < baseStart_1203292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203336 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1203336 : Nat := 118140960795 + 1203336 * 2 ^ 59
def prefixEnd_1203336 : Nat := 4983230072969 + 3 ^ 40 * 1203336 * 2
def baseEnd_1203336 : Nat := 617889756858809176065965

theorem tailTrace_1203336 : CollatzResearch.WordTrace tailWord_1203336 prefixEnd_1203336 617889756858809176065965 := by
  unfold tailWord_1203336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944634784263330136074931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29259513045684440181433241 21944634784263330136074931)
  ·
    refine ⟨32916952176394995204112397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21944634784263330136074931 32916952176394995204112397)
    ·
      refine ⟨12343857066148123201542149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32916952176394995204112397 12343857066148123201542149)
      ·
        refine ⟨2314473199902773100289153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12343857066148123201542149 2314473199902773100289153)
        ·
          refine ⟨1735854899927079825216865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314473199902773100289153 1735854899927079825216865)
          ·
            refine ⟨1301891174945309868912649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735854899927079825216865 1301891174945309868912649)
            ·
              refine ⟨976418381208982401684487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301891174945309868912649 976418381208982401684487)
              ·
                refine ⟨1464627571813473602526731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976418381208982401684487 1464627571813473602526731)
                ·
                  refine ⟨2196941357720210403790097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464627571813473602526731 2196941357720210403790097)
                  ·
                    refine ⟨1647706018290157802842573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196941357720210403790097 1647706018290157802842573)
                    ·
                      refine ⟨617889756858809176065965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1647706018290157802842573 617889756858809176065965)
                      ·
                        rfl

theorem cell23_1203336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1203336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203336 prefixEnd_1203336 := by exact prefixLift 1203336
  have htrace : WordTrace (prefixWord ++ tailWord_1203336) baseStart_1203336 baseEnd_1203336 := by
    simpa [prefixWord, tailWord_1203336, baseEnd_1203336] using wordTrace_append hprefix tailTrace_1203336
  have hstable : (prefixWord ++ tailWord_1203336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203336).length < 2 ^ (prefixWord ++ tailWord_1203336).sum := by decide
  have hdescent : baseEnd_1203336 < baseStart_1203336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203395 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 5]
def baseStart_1203395 : Nat := 118140960795 + 1203395 * 2 ^ 59
def prefixEnd_1203395 : Nat := 4983230072969 + 3 ^ 40 * 1203395 * 2
def baseEnd_1203395 : Nat := 68657783579713827247577

theorem tailTrace_1203395 : CollatzResearch.WordTrace tailWord_1203395 prefixEnd_1203395 68657783579713827247577 := by
  unfold tailWord_1203395
  simp only [CollatzResearch.WordTrace]
  refine ⟨43891421475312913348547639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29260947650208608899031759 43891421475312913348547639)
  ·
    refine ⟨65837132212969370022821459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43891421475312913348547639 65837132212969370022821459)
    ·
      refine ⟨98755698319454055034232189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65837132212969370022821459 98755698319454055034232189)
      ·
        refine ⟨37033386869795270637837071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98755698319454055034232189 37033386869795270637837071)
        ·
          refine ⟨55550080304692905956755607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37033386869795270637837071 55550080304692905956755607)
          ·
            refine ⟨83325120457039358935133411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55550080304692905956755607 83325120457039358935133411)
            ·
              refine ⟨124987680685559038402700117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83325120457039358935133411 124987680685559038402700117)
              ·
                refine ⟨732349691516947490640821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 124987680685559038402700117 732349691516947490640821)
                ·
                  refine ⟨68657783579713827247577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732349691516947490640821 68657783579713827247577)
                  ·
                    rfl

theorem cell23_1203395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 5].length) (baseStart_1203395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203395 prefixEnd_1203395 := by exact prefixLift 1203395
  have htrace : WordTrace (prefixWord ++ tailWord_1203395) baseStart_1203395 baseEnd_1203395 := by
    simpa [prefixWord, tailWord_1203395, baseEnd_1203395] using wordTrace_append hprefix tailTrace_1203395
  have hstable : (prefixWord ++ tailWord_1203395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203395).length < 2 ^ (prefixWord ++ tailWord_1203395).sum := by decide
  have hdescent : baseEnd_1203395 < baseStart_1203395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203448 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1203448 : Nat := 118140960795 + 1203448 * 2 ^ 59
def prefixEnd_1203448 : Nat := 4983230072969 + 3 ^ 40 * 1203448 * 2
def baseEnd_1203448 : Nat := 617947266692112737865449

theorem tailTrace_1203448 : CollatzResearch.WordTrace tailWord_1203448 prefixEnd_1203448 617947266692112737865449 := by
  unfold tailWord_1203448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21946677272060451700113499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29262236362747268933484665 21946677272060451700113499)
  ·
    refine ⟨32920015908090677550170249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21946677272060451700113499 32920015908090677550170249)
    ·
      refine ⟨24690011931068008162627687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32920015908090677550170249 24690011931068008162627687)
      ·
        refine ⟨37035017896602012243941531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24690011931068008162627687 37035017896602012243941531)
        ·
          refine ⟨55552526844903018365912297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37035017896602012243941531 55552526844903018365912297)
          ·
            refine ⟨41664395133677263774434223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55552526844903018365912297 41664395133677263774434223)
            ·
              refine ⟨62496592700515895661651335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41664395133677263774434223 62496592700515895661651335)
              ·
                refine ⟨93744889050773843492477003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62496592700515895661651335 93744889050773843492477003)
                ·
                  refine ⟨140617333576160765238715505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93744889050773843492477003 140617333576160765238715505)
                  ·
                    refine ⟨105463000182120573929036629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 140617333576160765238715505 105463000182120573929036629)
                    ·
                      refine ⟨617947266692112737865449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 105463000182120573929036629 617947266692112737865449)
                      ·
                        rfl

theorem cell23_1203448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1203448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203448 prefixEnd_1203448 := by exact prefixLift 1203448
  have htrace : WordTrace (prefixWord ++ tailWord_1203448) baseStart_1203448 baseEnd_1203448 := by
    simpa [prefixWord, tailWord_1203448, baseEnd_1203448] using wordTrace_append hprefix tailTrace_1203448
  have hstable : (prefixWord ++ tailWord_1203448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203448).length < 2 ^ (prefixWord ++ tailWord_1203448).sum := by decide
  have hdescent : baseEnd_1203448 < baseStart_1203448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203506 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_1203506 : Nat := 118140960795 + 1203506 * 2 ^ 59
def prefixEnd_1203506 : Nat := 4983230072969 + 3 ^ 40 * 1203506 * 2
def baseEnd_1203506 : Nat := 205992349523357836980061

theorem tailTrace_1203506 : CollatzResearch.WordTrace tailWord_1203506 prefixEnd_1203506 205992349523357836980061 := by
  unfold tailWord_1203506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973867494477694826459593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29263646651940519537225581 10973867494477694826459593)
  ·
    refine ⟨8230400620858271119844695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10973867494477694826459593 8230400620858271119844695)
    ·
      refine ⟨12345600931287406679767043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8230400620858271119844695 12345600931287406679767043)
      ·
        refine ⟨18518401396931110019650565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12345600931287406679767043 18518401396931110019650565)
        ·
          refine ⟨3472200261924583128684481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18518401396931110019650565 3472200261924583128684481)
          ·
            refine ⟨2604150196443437346513361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3472200261924583128684481 2604150196443437346513361)
            ·
              refine ⟨1953112647332578009885021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2604150196443437346513361 1953112647332578009885021)
              ·
                refine ⟨732417242749716753706883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1953112647332578009885021 732417242749716753706883)
                ·
                  refine ⟨1098625864124575130560325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732417242749716753706883 1098625864124575130560325)
                  ·
                    refine ⟨205992349523357836980061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1098625864124575130560325 205992349523357836980061)
                    ·
                      rfl

theorem cell23_1203506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_1203506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203506 prefixEnd_1203506 := by exact prefixLift 1203506
  have htrace : WordTrace (prefixWord ++ tailWord_1203506) baseStart_1203506 baseEnd_1203506 := by
    simpa [prefixWord, tailWord_1203506, baseEnd_1203506] using wordTrace_append hprefix tailTrace_1203506
  have hstable : (prefixWord ++ tailWord_1203506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203506).length < 2 ^ (prefixWord ++ tailWord_1203506).sum := by decide
  have hdescent : baseEnd_1203506 < baseStart_1203506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203512 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_1203512 : Nat := 118140960795 + 1203512 * 2 ^ 59
def prefixEnd_1203512 : Nat := 4983230072969 + 3 ^ 40 * 1203512 * 2
def baseEnd_1203512 : Nat := 617980129454000487465155

theorem tailTrace_1203512 : CollatzResearch.WordTrace tailWord_1203512 prefixEnd_1203512 617980129454000487465155 := by
  unfold tailWord_1203512
  simp only [CollatzResearch.WordTrace]
  refine ⟨21947844407944521165278395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29263792543926028220371193 21947844407944521165278395)
  ·
    refine ⟨32921766611916781747917593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21947844407944521165278395 32921766611916781747917593)
    ·
      refine ⟨24691324958937586310938195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32921766611916781747917593 24691324958937586310938195)
      ·
        refine ⟨37036987438406379466407293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24691324958937586310938195 37036987438406379466407293)
        ·
          refine ⟨13888870289402392299902735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37036987438406379466407293 13888870289402392299902735)
          ·
            refine ⟨20833305434103588449854103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13888870289402392299902735 20833305434103588449854103)
            ·
              refine ⟨31249958151155382674781155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20833305434103588449854103 31249958151155382674781155)
              ·
                refine ⟨46874937226733074012171733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31249958151155382674781155 46874937226733074012171733)
                ·
                  refine ⟨1098631341251556422160275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46874937226733074012171733 1098631341251556422160275)
                  ·
                    refine ⟨1647947011877334633240413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098631341251556422160275 1647947011877334633240413)
                    ·
                      refine ⟨617980129454000487465155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1647947011877334633240413 617980129454000487465155)
                      ·
                        rfl

theorem cell23_1203512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_1203512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203512 prefixEnd_1203512 := by exact prefixLift 1203512
  have htrace : WordTrace (prefixWord ++ tailWord_1203512) baseStart_1203512 baseEnd_1203512 := by
    simpa [prefixWord, tailWord_1203512, baseEnd_1203512] using wordTrace_append hprefix tailTrace_1203512
  have hstable : (prefixWord ++ tailWord_1203512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203512).length < 2 ^ (prefixWord ++ tailWord_1203512).sum := by decide
  have hdescent : baseEnd_1203512 < baseStart_1203512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203569 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_1203569 : Nat := 118140960795 + 1203569 * 2 ^ 59
def prefixEnd_1203569 : Nat := 4983230072969 + 3 ^ 40 * 1203569 * 2
def baseEnd_1203569 : Nat := 618009397851306764452393

theorem tailTrace_1203569 : CollatzResearch.WordTrace tailWord_1203569 prefixEnd_1203569 618009397851306764452393 := by
  unfold tailWord_1203569
  simp only [CollatzResearch.WordTrace]
  refine ⟨43897767776682541065381761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29265178517788360710254507 43897767776682541065381761)
  ·
    refine ⟨32923325832511905799036321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43897767776682541065381761 32923325832511905799036321)
    ·
      refine ⟨24692494374383929349277241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32923325832511905799036321 24692494374383929349277241)
      ·
        refine ⟨18519370780787947011957931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24692494374383929349277241 18519370780787947011957931)
        ·
          refine ⟨27779056171181920517936897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18519370780787947011957931 27779056171181920517936897)
          ·
            refine ⟨20834292128386440388452673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27779056171181920517936897 20834292128386440388452673)
            ·
              refine ⟨15625719096289830291339505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20834292128386440388452673 15625719096289830291339505)
              ·
                refine ⟨11719289322217372718504629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15625719096289830291339505 11719289322217372718504629)
                ·
                  refine ⟨1098683373957878692359809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11719289322217372718504629 1098683373957878692359809)
                  ·
                    refine ⟨824012530468409019269857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1098683373957878692359809 824012530468409019269857)
                    ·
                      refine ⟨618009397851306764452393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824012530468409019269857 618009397851306764452393)
                      ·
                        rfl

theorem cell23_1203569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_1203569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203569 prefixEnd_1203569 := by exact prefixLift 1203569
  have htrace : WordTrace (prefixWord ++ tailWord_1203569) baseStart_1203569 baseEnd_1203569 := by
    simpa [prefixWord, tailWord_1203569, baseEnd_1203569] using wordTrace_append hprefix tailTrace_1203569
  have hstable : (prefixWord ++ tailWord_1203569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203569).length < 2 ^ (prefixWord ++ tailWord_1203569).sum := by decide
  have hdescent : baseEnd_1203569 < baseStart_1203569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203592 : List Nat := [2, 1, 3, 3, 1, 3, 2, 8]
def baseStart_1203592 : Nat := 118140960795 + 1203592 * 2 ^ 59
def prefixEnd_1203592 : Nat := 4983230072969 + 3 ^ 40 * 1203592 * 2
def baseEnd_1203592 : Nat := 22889674366902228683881

theorem tailTrace_1203592 : CollatzResearch.WordTrace tailWord_1203592 prefixEnd_1203592 22889674366902228683881 := by
  unfold tailWord_1203592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21949303327799607996734515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29265737770399477328979353 21949303327799607996734515)
  ·
    refine ⟨32923954991699411995101773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21949303327799607996734515 32923954991699411995101773)
    ·
      refine ⟨12346483121887279498163165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32923954991699411995101773 12346483121887279498163165)
      ·
        refine ⟨4629931170707729811811187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12346483121887279498163165 4629931170707729811811187)
        ·
          refine ⟨6944896756061594717716781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629931170707729811811187 6944896756061594717716781)
          ·
            refine ⟨2604336283523098019143793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6944896756061594717716781 2604336283523098019143793)
            ·
              refine ⟨1953252212642323514357845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2604336283523098019143793 1953252212642323514357845)
              ·
                refine ⟨22889674366902228683881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1953252212642323514357845 22889674366902228683881)
                ·
                  rfl

theorem cell23_1203592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 8].length) (baseStart_1203592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203592 prefixEnd_1203592 := by exact prefixLift 1203592
  have htrace : WordTrace (prefixWord ++ tailWord_1203592) baseStart_1203592 baseEnd_1203592 := by
    simpa [prefixWord, tailWord_1203592, baseEnd_1203592] using wordTrace_append hprefix tailTrace_1203592
  have hstable : (prefixWord ++ tailWord_1203592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203592).length < 2 ^ (prefixWord ++ tailWord_1203592).sum := by decide
  have hdescent : baseEnd_1203592 < baseStart_1203592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203595 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_1203595 : Nat := 118140960795 + 1203595 * 2 ^ 59
def prefixEnd_1203595 : Nat := 4983230072969 + 3 ^ 40 * 1203595 * 2
def baseEnd_1203595 : Nat := 618022748348323662727273

theorem tailTrace_1203595 : CollatzResearch.WordTrace tailWord_1203595 prefixEnd_1203595 618022748348323662727273 := by
  unfold tailWord_1203595
  simp only [CollatzResearch.WordTrace]
  refine ⟨43898716074588347505828239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29265810716392231670552159 43898716074588347505828239)
  ·
    refine ⟨65848074111882521258742359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43898716074588347505828239 65848074111882521258742359)
    ·
      refine ⟨98772111167823781888113539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65848074111882521258742359 98772111167823781888113539)
      ·
        refine ⟨148158166751735672832170309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98772111167823781888113539 148158166751735672832170309)
        ·
          refine ⟨27779656265950438656031933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148158166751735672832170309 27779656265950438656031933)
          ·
            refine ⟨10417371099731414496011975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27779656265950438656031933 10417371099731414496011975)
            ·
              refine ⟨15626056649597121744017963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10417371099731414496011975 15626056649597121744017963)
              ·
                refine ⟨23439084974395682616026945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15626056649597121744017963 23439084974395682616026945)
                ·
                  refine ⟨17579313730796761962020209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23439084974395682616026945 17579313730796761962020209)
                  ·
                    refine ⟨13184485298097571471515157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17579313730796761962020209 13184485298097571471515157)
                    ·
                      refine ⟨618022748348323662727273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13184485298097571471515157 618022748348323662727273)
                      ·
                        rfl

theorem cell23_1203595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_1203595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203595 prefixEnd_1203595 := by exact prefixLift 1203595
  have htrace : WordTrace (prefixWord ++ tailWord_1203595) baseStart_1203595 baseEnd_1203595 := by
    simpa [prefixWord, tailWord_1203595, baseEnd_1203595] using wordTrace_append hprefix tailTrace_1203595
  have hstable : (prefixWord ++ tailWord_1203595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203595).length < 2 ^ (prefixWord ++ tailWord_1203595).sum := by decide
  have hdescent : baseEnd_1203595 < baseStart_1203595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203635 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 8]
def baseStart_1203635 : Nat := 118140960795 + 1203635 * 2 ^ 59
def prefixEnd_1203635 : Nat := 4983230072969 + 3 ^ 40 * 1203635 * 2
def baseEnd_1203635 : Nat := 206014429191501168742363

theorem tailTrace_1203635 : CollatzResearch.WordTrace tailWord_1203635 prefixEnd_1203635 206014429191501168742363 := by
  unfold tailWord_1203635
  simp only [CollatzResearch.WordTrace]
  refine ⟨43900174994443434337284359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29266783329628956224856239 43900174994443434337284359)
  ·
    refine ⟨65850262491665151505926539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43900174994443434337284359 65850262491665151505926539)
    ·
      refine ⟨98775393737497727258889809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65850262491665151505926539 98775393737497727258889809)
      ·
        refine ⟨74081545303123295444167357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98775393737497727258889809 74081545303123295444167357)
        ·
          refine ⟨27780579488671235791562759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74081545303123295444167357 27780579488671235791562759)
          ·
            refine ⟨41670869233006853687344139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27780579488671235791562759 41670869233006853687344139)
            ·
              refine ⟨62506303849510280531016209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41670869233006853687344139 62506303849510280531016209)
              ·
                refine ⟨46879727887132710398262157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62506303849510280531016209 46879727887132710398262157)
                ·
                  refine ⟨17579897957674766399348309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46879727887132710398262157 17579897957674766399348309)
                  ·
                    refine ⟨206014429191501168742363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17579897957674766399348309 206014429191501168742363)
                    ·
                      rfl

theorem cell23_1203635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_1203635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203635 prefixEnd_1203635 := by exact prefixLift 1203635
  have htrace : WordTrace (prefixWord ++ tailWord_1203635) baseStart_1203635 baseEnd_1203635 := by
    simpa [prefixWord, tailWord_1203635, baseEnd_1203635] using wordTrace_append hprefix tailTrace_1203635
  have hstable : (prefixWord ++ tailWord_1203635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203635).length < 2 ^ (prefixWord ++ tailWord_1203635).sum := by decide
  have hdescent : baseEnd_1203635 < baseStart_1203635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203637 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_1203637 : Nat := 118140960795 + 1203637 * 2 ^ 59
def prefixEnd_1203637 : Nat := 4983230072969 + 3 ^ 40 * 1203637 * 2
def baseEnd_1203637 : Nat := 618044314535812498402081

theorem tailTrace_1203637 : CollatzResearch.WordTrace tailWord_1203637 prefixEnd_1203637 618044314535812498402081 := by
  unfold tailWord_1203637
  simp only [CollatzResearch.WordTrace]
  refine ⟨43900247940436188678857165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29266831960290792452571443 43900247940436188678857165)
  ·
    refine ⟨16462592977663570754571437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43900247940436188678857165 16462592977663570754571437)
    ·
      refine ⟨6173472366623839032964289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16462592977663570754571437 6173472366623839032964289)
      ·
        refine ⟨4630104274967879274723217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6173472366623839032964289 4630104274967879274723217)
        ·
          refine ⟨3472578206225909456042413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4630104274967879274723217 3472578206225909456042413)
          ·
            refine ⟨1302216827334716046015905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3472578206225909456042413 1302216827334716046015905)
            ·
              refine ⟨976662620501037034511929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302216827334716046015905 976662620501037034511929)
              ·
                refine ⟨732496965375777775883947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976662620501037034511929 732496965375777775883947)
                ·
                  refine ⟨1098745448063666663825921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732496965375777775883947 1098745448063666663825921)
                  ·
                    refine ⟨824059086047749997869441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1098745448063666663825921 824059086047749997869441)
                    ·
                      refine ⟨618044314535812498402081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824059086047749997869441 618044314535812498402081)
                      ·
                        rfl

theorem cell23_1203637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_1203637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203637 prefixEnd_1203637 := by exact prefixLift 1203637
  have htrace : WordTrace (prefixWord ++ tailWord_1203637) baseStart_1203637 baseEnd_1203637 := by
    simpa [prefixWord, tailWord_1203637, baseEnd_1203637] using wordTrace_append hprefix tailTrace_1203637
  have hstable : (prefixWord ++ tailWord_1203637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203637).length < 2 ^ (prefixWord ++ tailWord_1203637).sum := by decide
  have hdescent : baseEnd_1203637 < baseStart_1203637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203659 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 4, 2]
def baseStart_1203659 : Nat := 118140960795 + 1203659 * 2 ^ 59
def prefixEnd_1203659 : Nat := 4983230072969 + 3 ^ 40 * 1203659 * 2
def baseEnd_1203659 : Nat := 618055611110211412326979

theorem tailTrace_1203659 : CollatzResearch.WordTrace tailWord_1203659 prefixEnd_1203659 618055611110211412326979 := by
  unfold tailWord_1203659
  simp only [CollatzResearch.WordTrace]
  refine ⟨43901050346356486436158031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29267366897570990957438687 43901050346356486436158031)
  ·
    refine ⟨65851575519534729654237047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43901050346356486436158031 65851575519534729654237047)
    ·
      refine ⟨98777363279302094481355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65851575519534729654237047 98777363279302094481355571)
      ·
        refine ⟨148166044918953141722033357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98777363279302094481355571 148166044918953141722033357)
        ·
          refine ⟨55562266844607428145762509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148166044918953141722033357 55562266844607428145762509)
          ·
            refine ⟨20835850066727785554660941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55562266844607428145762509 20835850066727785554660941)
            ·
              refine ⟨7813443775022919582997853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20835850066727785554660941 7813443775022919582997853)
              ·
                refine ⟨2930041415633594843624195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7813443775022919582997853 2930041415633594843624195)
                ·
                  refine ⟨4395062123450392265436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930041415633594843624195 4395062123450392265436293)
                  ·
                    refine ⟨824074148146948549769305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395062123450392265436293 824074148146948549769305)
                    ·
                      refine ⟨618055611110211412326979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824074148146948549769305 618055611110211412326979)
                      ·
                        rfl

theorem cell23_1203659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4, 2].length) (baseStart_1203659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203659 prefixEnd_1203659 := by exact prefixLift 1203659
  have htrace : WordTrace (prefixWord ++ tailWord_1203659) baseStart_1203659 baseEnd_1203659 := by
    simpa [prefixWord, tailWord_1203659, baseEnd_1203659] using wordTrace_append hprefix tailTrace_1203659
  have hstable : (prefixWord ++ tailWord_1203659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203659).length < 2 ^ (prefixWord ++ tailWord_1203659).sum := by decide
  have hdescent : baseEnd_1203659 < baseStart_1203659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203662 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1203662 : Nat := 118140960795 + 1203662 * 2 ^ 59
def prefixEnd_1203662 : Nat := 4983230072969 + 3 ^ 40 * 1203662 * 2
def baseEnd_1203662 : Nat := 618057151552174900589465

theorem tailTrace_1203662 : CollatzResearch.WordTrace tailWord_1203662 prefixEnd_1203662 618057151552174900589465 := by
  unfold tailWord_1203662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487644970668202243564655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29267439843563745299011493 5487644970668202243564655)
  ·
    refine ⟨8231467456002303365346983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5487644970668202243564655 8231467456002303365346983)
    ·
      refine ⟨12347201184003455048020475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8231467456002303365346983 12347201184003455048020475)
      ·
        refine ⟨18520801776005182572030713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12347201184003455048020475 18520801776005182572030713)
        ·
          refine ⟨13890601332003886929023035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18520801776005182572030713 13890601332003886929023035)
          ·
            refine ⟨20835901998005830393534553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13890601332003886929023035 20835901998005830393534553)
            ·
              refine ⟨15626926498504372795150915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20835901998005830393534553 15626926498504372795150915)
              ·
                refine ⟨23440389747756559192726373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15626926498504372795150915 23440389747756559192726373)
                ·
                  refine ⟨4395073077704354848636195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23440389747756559192726373 4395073077704354848636195)
                  ·
                    refine ⟨6592609616556532272954293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395073077704354848636195 6592609616556532272954293)
                    ·
                      refine ⟨618057151552174900589465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6592609616556532272954293 618057151552174900589465)
                      ·
                        rfl

theorem cell23_1203662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1203662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203662 prefixEnd_1203662 := by exact prefixLift 1203662
  have htrace : WordTrace (prefixWord ++ tailWord_1203662) baseStart_1203662 baseEnd_1203662 := by
    simpa [prefixWord, tailWord_1203662, baseEnd_1203662] using wordTrace_append hprefix tailTrace_1203662
  have hstable : (prefixWord ++ tailWord_1203662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203662).length < 2 ^ (prefixWord ++ tailWord_1203662).sum := by decide
  have hdescent : baseEnd_1203662 < baseStart_1203662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203709 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_1203709 : Nat := 118140960795 + 1203709 * 2 ^ 59
def prefixEnd_1203709 : Nat := 4983230072969 + 3 ^ 40 * 1203709 * 2
def baseEnd_1203709 : Nat := 618081285142936216701749

theorem tailTrace_1203709 : CollatzResearch.WordTrace tailWord_1203709 prefixEnd_1203709 618081285142936216701749 := by
  unfold tailWord_1203709
  simp only [CollatzResearch.WordTrace]
  refine ⟨43902873996175344975478181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29268582664116896650318787 43902873996175344975478181)
  ·
    refine ⟨8231788874282877182902159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43902873996175344975478181 8231788874282877182902159)
    ·
      refine ⟨12347683311424315774353239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8231788874282877182902159 12347683311424315774353239)
      ·
        refine ⟨18521524967136473661529859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12347683311424315774353239 18521524967136473661529859)
        ·
          refine ⟨27782287450704710492294789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18521524967136473661529859 27782287450704710492294789)
          ·
            refine ⟨5209178897007133217305273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27782287450704710492294789 5209178897007133217305273)
            ·
              refine ⟨3906884172755349912978955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5209178897007133217305273 3906884172755349912978955)
              ·
                refine ⟨5860326259133024869468433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906884172755349912978955 5860326259133024869468433)
                ·
                  refine ⟨4395244694349768652101325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860326259133024869468433 4395244694349768652101325)
                  ·
                    refine ⟨1648216760381163244537997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4395244694349768652101325 1648216760381163244537997)
                    ·
                      refine ⟨618081285142936216701749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1648216760381163244537997 618081285142936216701749)
                      ·
                        rfl

theorem cell23_1203709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_1203709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203709 prefixEnd_1203709 := by exact prefixLift 1203709
  have htrace : WordTrace (prefixWord ++ tailWord_1203709) baseStart_1203709 baseEnd_1203709 := by
    simpa [prefixWord, tailWord_1203709, baseEnd_1203709] using wordTrace_append hprefix tailTrace_1203709
  have hstable : (prefixWord ++ tailWord_1203709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203709).length < 2 ^ (prefixWord ++ tailWord_1203709).sum := by decide
  have hdescent : baseEnd_1203709 < baseStart_1203709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203786 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1203786 : Nat := 118140960795 + 1203786 * 2 ^ 59
def prefixEnd_1203786 : Nat := 4983230072969 + 3 ^ 40 * 1203786 * 2
def baseEnd_1203786 : Nat := 618120823153332415438895

theorem tailTrace_1203786 : CollatzResearch.WordTrace tailWord_1203786 prefixEnd_1203786 618120823153332415438895 := by
  unfold tailWord_1203786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976420604224096781507803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29270454944597591417354141 10976420604224096781507803)
  ·
    refine ⟨16464630906336145172261705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10976420604224096781507803 16464630906336145172261705)
    ·
      refine ⟨12348473179752108879196279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16464630906336145172261705 12348473179752108879196279)
      ·
        refine ⟨18522709769628163318794419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348473179752108879196279 18522709769628163318794419)
        ·
          refine ⟨27784064654442244978191629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18522709769628163318794419 27784064654442244978191629)
          ·
            refine ⟨10419024245415841866821861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27784064654442244978191629 10419024245415841866821861)
            ·
              refine ⟨1953567046015470350029099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10419024245415841866821861 1953567046015470350029099)
              ·
                refine ⟨2930350569023205525043649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953567046015470350029099 2930350569023205525043649)
                ·
                  refine ⟨2197762926767404143782737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2930350569023205525043649 2197762926767404143782737)
                  ·
                    refine ⟨1648322195075553107837053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197762926767404143782737 1648322195075553107837053)
                    ·
                      refine ⟨618120823153332415438895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1648322195075553107837053 618120823153332415438895)
                      ·
                        rfl

theorem cell23_1203786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1203786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203786 prefixEnd_1203786 := by exact prefixLift 1203786
  have htrace : WordTrace (prefixWord ++ tailWord_1203786) baseStart_1203786 baseEnd_1203786 := by
    simpa [prefixWord, tailWord_1203786, baseEnd_1203786] using wordTrace_append hprefix tailTrace_1203786
  have hstable : (prefixWord ++ tailWord_1203786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203786).length < 2 ^ (prefixWord ++ tailWord_1203786).sum := by decide
  have hdescent : baseEnd_1203786 < baseStart_1203786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203849 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_1203849 : Nat := 118140960795 + 1203849 * 2 ^ 59
def prefixEnd_1203849 : Nat := 4983230072969 + 3 ^ 40 * 1203849 * 2
def baseEnd_1203849 : Nat := 206051057478188556317035

theorem tailTrace_1203849 : CollatzResearch.WordTrace tailWord_1203849 prefixEnd_1203849 206051057478188556317035 := by
  unfold tailWord_1203849
  simp only [CollatzResearch.WordTrace]
  refine ⟨43907980215668148885574601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29271986810445432590383067 43907980215668148885574601)
  ·
    refine ⟨32930985161751111664180951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43907980215668148885574601 32930985161751111664180951)
    ·
      refine ⟨49396477742626667496271427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32930985161751111664180951 49396477742626667496271427)
      ·
        refine ⟨74094716613940001244407141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49396477742626667496271427 74094716613940001244407141)
        ·
          refine ⟨13892759365113750233326339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74094716613940001244407141 13892759365113750233326339)
          ·
            refine ⟨20839139047670625349989509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13892759365113750233326339 20839139047670625349989509)
            ·
              refine ⟨3907338571438242253123033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20839139047670625349989509 3907338571438242253123033)
              ·
                refine ⟨2930503928578681689842275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907338571438242253123033 2930503928578681689842275)
                ·
                  refine ⟨4395755892868022534763413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930503928578681689842275 4395755892868022534763413)
                  ·
                    refine ⟨206051057478188556317035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4395755892868022534763413 206051057478188556317035)
                    ·
                      rfl

theorem cell23_1203849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_1203849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203849 prefixEnd_1203849 := by exact prefixLift 1203849
  have htrace : WordTrace (prefixWord ++ tailWord_1203849) baseStart_1203849 baseEnd_1203849 := by
    simpa [prefixWord, tailWord_1203849, baseEnd_1203849] using wordTrace_append hprefix tailTrace_1203849
  have hstable : (prefixWord ++ tailWord_1203849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203849).length < 2 ^ (prefixWord ++ tailWord_1203849).sum := by decide
  have hdescent : baseEnd_1203849 < baseStart_1203849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203850 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1203850 : Nat := 118140960795 + 1203850 * 2 ^ 59
def prefixEnd_1203850 : Nat := 4983230072969 + 3 ^ 40 * 1203850 * 2
def baseEnd_1203850 : Nat := 618153685915220165038601

theorem tailTrace_1203850 : CollatzResearch.WordTrace tailWord_1203850 prefixEnd_1203850 618153685915220165038601 := by
  unfold tailWord_1203850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977004172166131514090251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29272011125776350704240669 10977004172166131514090251)
  ·
    refine ⟨16465506258249197271135377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977004172166131514090251 16465506258249197271135377)
    ·
      refine ⟨12349129693686897953351533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16465506258249197271135377 12349129693686897953351533)
      ·
        refine ⟨4630923635132586732506825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12349129693686897953351533 4630923635132586732506825)
        ·
          refine ⟨3473192726349440049380119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4630923635132586732506825 3473192726349440049380119)
          ·
            refine ⟨5209789089524160074070179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473192726349440049380119 5209789089524160074070179)
            ·
              refine ⟨7814683634286240111105269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209789089524160074070179 7814683634286240111105269)
              ·
                refine ⟨732626590714335010416119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7814683634286240111105269 732626590714335010416119)
                ·
                  refine ⟨1098939886071502515624179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732626590714335010416119 1098939886071502515624179)
                  ·
                    refine ⟨1648409829107253773436269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098939886071502515624179 1648409829107253773436269)
                    ·
                      refine ⟨618153685915220165038601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1648409829107253773436269 618153685915220165038601)
                      ·
                        rfl

theorem cell23_1203850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1203850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203850 prefixEnd_1203850 := by exact prefixLift 1203850
  have htrace : WordTrace (prefixWord ++ tailWord_1203850) baseStart_1203850 baseEnd_1203850 := by
    simpa [prefixWord, tailWord_1203850, baseEnd_1203850] using wordTrace_append hprefix tailTrace_1203850
  have hstable : (prefixWord ++ tailWord_1203850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203850).length < 2 ^ (prefixWord ++ tailWord_1203850).sum := by decide
  have hdescent : baseEnd_1203850 < baseStart_1203850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203869 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1203869 : Nat := 118140960795 + 1203869 * 2 ^ 59
def prefixEnd_1203869 : Nat := 4983230072969 + 3 ^ 40 * 1203869 * 2
def baseEnd_1203869 : Nat := 618163442047655590701013

theorem tailTrace_1203869 : CollatzResearch.WordTrace tailWord_1203869 prefixEnd_1203869 618163442047655590701013 := by
  unfold tailWord_1203869
  simp only [CollatzResearch.WordTrace]
  refine ⟨43908709675595692301302661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29272473117063794867535107 43908709675595692301302661)
  ·
    refine ⟨8232883064174192306494249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43908709675595692301302661 8232883064174192306494249)
    ·
      refine ⟨6174662298130644229870687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8232883064174192306494249 6174662298130644229870687)
      ·
        refine ⟨9261993447195966344806031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6174662298130644229870687 9261993447195966344806031)
        ·
          refine ⟨13892990170793949517209047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9261993447195966344806031 13892990170793949517209047)
          ·
            refine ⟨20839485256190924275813571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13892990170793949517209047 20839485256190924275813571)
            ·
              refine ⟨31259227884286386413720357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20839485256190924275813571 31259227884286386413720357)
              ·
                refine ⟨5861105228303697452572567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31259227884286386413720357 5861105228303697452572567)
                ·
                  refine ⟨8791657842455546178858851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861105228303697452572567 8791657842455546178858851)
                  ·
                    refine ⟨13187486763683319268288277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8791657842455546178858851 13187486763683319268288277)
                    ·
                      refine ⟨618163442047655590701013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13187486763683319268288277 618163442047655590701013)
                      ·
                        rfl

theorem cell23_1203869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1203869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203869 prefixEnd_1203869 := by exact prefixLift 1203869
  have htrace : WordTrace (prefixWord ++ tailWord_1203869) baseStart_1203869 baseEnd_1203869 := by
    simpa [prefixWord, tailWord_1203869, baseEnd_1203869] using wordTrace_append hprefix tailTrace_1203869
  have hstable : (prefixWord ++ tailWord_1203869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203869).length < 2 ^ (prefixWord ++ tailWord_1203869).sum := by decide
  have hdescent : baseEnd_1203869 < baseStart_1203869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203876 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1203876 : Nat := 118140960795 + 1203876 * 2 ^ 59
def prefixEnd_1203876 : Nat := 4983230072969 + 3 ^ 40 * 1203876 * 2
def baseEnd_1203876 : Nat := 618167036412237063313481

theorem tailTrace_1203876 : CollatzResearch.WordTrace tailWord_1203876 prefixEnd_1203876 618167036412237063313481 := by
  unfold tailWord_1203876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954482493285166248403741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29272643324380221664538321 21954482493285166248403741)
  ·
    refine ⟨8232930934981937343151403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21954482493285166248403741 8232930934981937343151403)
    ·
      refine ⟨12349396402472906014727105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8232930934981937343151403 12349396402472906014727105)
      ·
        refine ⟨9262047301854679511045329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12349396402472906014727105 9262047301854679511045329)
        ·
          refine ⟨6946535476391009633283997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9262047301854679511045329 6946535476391009633283997)
          ·
            refine ⟨2604950803646628612481499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6946535476391009633283997 2604950803646628612481499)
            ·
              refine ⟨3907426205469942918722249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604950803646628612481499 3907426205469942918722249)
              ·
                refine ⟨2930569654102457189041687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907426205469942918722249 2930569654102457189041687)
                ·
                  refine ⟨4395854481153685783562531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930569654102457189041687 4395854481153685783562531)
                  ·
                    refine ⟨6593781721730528675343797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395854481153685783562531 6593781721730528675343797)
                    ·
                      refine ⟨618167036412237063313481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6593781721730528675343797 618167036412237063313481)
                      ·
                        rfl

theorem cell23_1203876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1203876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203876 prefixEnd_1203876 := by exact prefixLift 1203876
  have htrace : WordTrace (prefixWord ++ tailWord_1203876) baseStart_1203876 baseEnd_1203876 := by
    simpa [prefixWord, tailWord_1203876, baseEnd_1203876] using wordTrace_append hprefix tailTrace_1203876
  have hstable : (prefixWord ++ tailWord_1203876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203876).length < 2 ^ (prefixWord ++ tailWord_1203876).sum := by decide
  have hdescent : baseEnd_1203876 < baseStart_1203876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203910 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1203910 : Nat := 118140960795 + 1203910 * 2 ^ 59
def prefixEnd_1203910 : Nat := 4983230072969 + 3 ^ 40 * 1203910 * 2
def baseEnd_1203910 : Nat := 618184494754489930288325

theorem tailTrace_1203910 : CollatzResearch.WordTrace tailWord_1203910 prefixEnd_1203910 618184494754489930288325 := by
  unfold tailWord_1203910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372193908388973634485787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29273470045631437535696789 1372193908388973634485787)
  ·
    refine ⟨2058290862583460451728681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372193908388973634485787 2058290862583460451728681)
    ·
      refine ⟨1543718146937595338796511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058290862583460451728681 1543718146937595338796511)
      ·
        refine ⟨2315577220406393008194767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543718146937595338796511 2315577220406393008194767)
        ·
          refine ⟨3473365830609589512292151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315577220406393008194767 3473365830609589512292151)
          ·
            refine ⟨5210048745914384268438227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473365830609589512292151 5210048745914384268438227)
            ·
              refine ⟨7815073118871576402657341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210048745914384268438227 7815073118871576402657341)
              ·
                refine ⟨2930652419576841150996503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7815073118871576402657341 2930652419576841150996503)
                ·
                  refine ⟨4395978629365261726494755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930652419576841150996503 4395978629365261726494755)
                  ·
                    refine ⟨6593967944047892589742133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395978629365261726494755 6593967944047892589742133)
                    ·
                      refine ⟨618184494754489930288325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6593967944047892589742133 618184494754489930288325)
                      ·
                        rfl

theorem cell23_1203910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1203910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203910 prefixEnd_1203910 := by exact prefixLift 1203910
  have htrace : WordTrace (prefixWord ++ tailWord_1203910) baseStart_1203910 baseEnd_1203910 := by
    simpa [prefixWord, tailWord_1203910, baseEnd_1203910] using wordTrace_append hprefix tailTrace_1203910
  have hstable : (prefixWord ++ tailWord_1203910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203910).length < 2 ^ (prefixWord ++ tailWord_1203910).sum := by decide
  have hdescent : baseEnd_1203910 < baseStart_1203910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 4, 2, 2]
def baseStart_1203963 : Nat := 118140960795 + 1203963 * 2 ^ 59
def prefixEnd_1203963 : Nat := 4983230072969 + 3 ^ 40 * 1203963 * 2
def baseEnd_1203963 : Nat := 618211709229178222925581

theorem tailTrace_1203963 : CollatzResearch.WordTrace tailWord_1203963 prefixEnd_1203963 618211709229178222925581 := by
  unfold tailWord_1203963
  simp only [CollatzResearch.WordTrace]
  refine ⟨43912138137255146355224543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29274758758170097570149695 43912138137255146355224543)
  ·
    refine ⟨65868207205882719532836815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43912138137255146355224543 65868207205882719532836815)
    ·
      refine ⟨98802310808824079299255223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65868207205882719532836815 98802310808824079299255223)
      ·
        refine ⟨148203466213236118948882835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98802310808824079299255223 148203466213236118948882835)
        ·
          refine ⟨222305199319854178423324253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148203466213236118948882835 222305199319854178423324253)
          ·
            refine ⟨83364449744945316908746595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222305199319854178423324253 83364449744945316908746595)
            ·
              refine ⟨125046674617417975363119893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83364449744945316908746595 125046674617417975363119893)
              ·
                refine ⟨5861562872691467595146245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125046674617417975363119893 5861562872691467595146245)
                ·
                  refine ⟨1099043038629650174089921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5861562872691467595146245 1099043038629650174089921)
                  ·
                    refine ⟨824282278972237630567441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099043038629650174089921 824282278972237630567441)
                    ·
                      refine ⟨618211709229178222925581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824282278972237630567441 618211709229178222925581)
                      ·
                        rfl

theorem cell23_1203963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2, 2].length) (baseStart_1203963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203963 prefixEnd_1203963 := by exact prefixLift 1203963
  have htrace : WordTrace (prefixWord ++ tailWord_1203963) baseStart_1203963 baseEnd_1203963 := by
    simpa [prefixWord, tailWord_1203963, baseEnd_1203963] using wordTrace_append hprefix tailTrace_1203963
  have hstable : (prefixWord ++ tailWord_1203963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203963).length < 2 ^ (prefixWord ++ tailWord_1203963).sum := by decide
  have hdescent : baseEnd_1203963 < baseStart_1203963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203976 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1203976 : Nat := 118140960795 + 1203976 * 2 ^ 59
def prefixEnd_1203976 : Nat := 4983230072969 + 3 ^ 40 * 1203976 * 2
def baseEnd_1203976 : Nat := 618218384477686672063021

theorem tailTrace_1203976 : CollatzResearch.WordTrace tailWord_1203976 prefixEnd_1203976 618218384477686672063021 := by
  unfold tailWord_1203976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956306143104024787723891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29275074857472033050298521 21956306143104024787723891)
  ·
    refine ⟨32934459214656037181585837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21956306143104024787723891 32934459214656037181585837)
    ·
      refine ⟨12350422205496013943094689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32934459214656037181585837 12350422205496013943094689)
      ·
        refine ⟨9262816654122010457321017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12350422205496013943094689 9262816654122010457321017)
        ·
          refine ⟨6947112490591507842990763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9262816654122010457321017 6947112490591507842990763)
          ·
            refine ⟨10420668735887261764486145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947112490591507842990763 10420668735887261764486145)
            ·
              refine ⟨7815501551915446323364609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10420668735887261764486145 7815501551915446323364609)
              ·
                refine ⟨5861626163936584742523457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7815501551915446323364609 5861626163936584742523457)
                ·
                  refine ⟨4396219622952438556892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861626163936584742523457 4396219622952438556892593)
                  ·
                    refine ⟨3297164717214328917669445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396219622952438556892593 3297164717214328917669445)
                    ·
                      refine ⟨618218384477686672063021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3297164717214328917669445 618218384477686672063021)
                      ·
                        rfl

theorem cell23_1203976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1203976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203976 prefixEnd_1203976 := by exact prefixLift 1203976
  have htrace : WordTrace (prefixWord ++ tailWord_1203976) baseStart_1203976 baseEnd_1203976 := by
    simpa [prefixWord, tailWord_1203976, baseEnd_1203976] using wordTrace_append hprefix tailTrace_1203976
  have hstable : (prefixWord ++ tailWord_1203976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203976).length < 2 ^ (prefixWord ++ tailWord_1203976).sum := by decide
  have hdescent : baseEnd_1203976 < baseStart_1203976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203979 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_1203979 : Nat := 118140960795 + 1203979 * 2 ^ 59
def prefixEnd_1203979 : Nat := 4983230072969 + 3 ^ 40 * 1203979 * 2
def baseEnd_1203979 : Nat := 618219924919650160325507

theorem tailTrace_1203979 : CollatzResearch.WordTrace tailWord_1203979 prefixEnd_1203979 618219924919650160325507 := by
  unfold tailWord_1203979
  simp only [CollatzResearch.WordTrace]
  refine ⟨43912721705197181087806991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29275147803464787391871327 43912721705197181087806991)
  ·
    refine ⟨65869082557795771631710487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43912721705197181087806991 65869082557795771631710487)
    ·
      refine ⟨98803623836693657447565731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65869082557795771631710487 98803623836693657447565731)
      ·
        refine ⟨148205435755040486171348597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98803623836693657447565731 148205435755040486171348597)
        ·
          refine ⟨13894259602035045578563931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148205435755040486171348597 13894259602035045578563931)
          ·
            refine ⟨20841389403052568367845897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13894259602035045578563931 20841389403052568367845897)
            ·
              refine ⟨15631042052289426275884423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20841389403052568367845897 15631042052289426275884423)
              ·
                refine ⟨23446563078434139413826635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15631042052289426275884423 23446563078434139413826635)
                ·
                  refine ⟨35169844617651209120739953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23446563078434139413826635 35169844617651209120739953)
                  ·
                    refine ⟨26377383463238406840554965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35169844617651209120739953 26377383463238406840554965)
                    ·
                      refine ⟨618219924919650160325507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26377383463238406840554965 618219924919650160325507)
                      ·
                        rfl

theorem cell23_1203979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_1203979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203979 prefixEnd_1203979 := by exact prefixLift 1203979
  have htrace : WordTrace (prefixWord ++ tailWord_1203979) baseStart_1203979 baseEnd_1203979 := by
    simpa [prefixWord, tailWord_1203979, baseEnd_1203979] using wordTrace_append hprefix tailTrace_1203979
  have hstable : (prefixWord ++ tailWord_1203979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203979).length < 2 ^ (prefixWord ++ tailWord_1203979).sum := by decide
  have hdescent : baseEnd_1203979 < baseStart_1203979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203980 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_1203980 : Nat := 118140960795 + 1203980 * 2 ^ 59
def prefixEnd_1203980 : Nat := 4983230072969 + 3 ^ 40 * 1203980 * 2
def baseEnd_1203980 : Nat := 618220438400304656413003

theorem tailTrace_1203980 : CollatzResearch.WordTrace tailWord_1203980 prefixEnd_1203980 618220438400304656413003 := by
  unfold tailWord_1203980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956379089096779129296697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29275172118795705505728929 21956379089096779129296697)
  ·
    refine ⟨16467284316822584346972523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21956379089096779129296697 16467284316822584346972523)
    ·
      refine ⟨24700926475233876520458785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16467284316822584346972523 24700926475233876520458785)
      ·
        refine ⟨18525694856425407390344089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24700926475233876520458785 18525694856425407390344089)
        ·
          refine ⟨13894271142319055542758067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18525694856425407390344089 13894271142319055542758067)
          ·
            refine ⟨20841406713478583314137101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13894271142319055542758067 20841406713478583314137101)
            ·
              refine ⟨7815527517554468742801413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20841406713478583314137101 7815527517554468742801413)
              ·
                refine ⟨1465411409541462889275265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7815527517554468742801413 1465411409541462889275265)
                ·
                  refine ⟨1099058557156097166956449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465411409541462889275265 1099058557156097166956449)
                  ·
                    refine ⟨824293917867072875217337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099058557156097166956449 824293917867072875217337)
                    ·
                      refine ⟨618220438400304656413003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824293917867072875217337 618220438400304656413003)
                      ·
                        rfl

theorem cell23_1203980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_1203980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1203980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1203980 prefixEnd_1203980 := by exact prefixLift 1203980
  have htrace : WordTrace (prefixWord ++ tailWord_1203980) baseStart_1203980 baseEnd_1203980 := by
    simpa [prefixWord, tailWord_1203980, baseEnd_1203980] using wordTrace_append hprefix tailTrace_1203980
  have hstable : (prefixWord ++ tailWord_1203980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203980).length < 2 ^ (prefixWord ++ tailWord_1203980).sum := by decide
  have hdescent : baseEnd_1203980 < baseStart_1203980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204020 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1204020 : Nat := 118140960795 + 1204020 * 2 ^ 59
def prefixEnd_1204020 : Nat := 4983230072969 + 3 ^ 40 * 1204020 * 2
def baseEnd_1204020 : Nat := 68693441958498277768091

theorem tailTrace_1204020 : CollatzResearch.WordTrace tailWord_1204020 prefixEnd_1204020 68693441958498277768091 := by
  unfold tailWord_1204020
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957108549024322545024757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29276144732032430060033009 21957108549024322545024757)
  ·
    refine ⟨2058478926471030238596071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21957108549024322545024757 2058478926471030238596071)
    ·
      refine ⟨3087718389706545357894107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058478926471030238596071 3087718389706545357894107)
      ·
        refine ⟨4631577584559818036841161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087718389706545357894107 4631577584559818036841161)
        ·
          refine ⟨3473683188419863527630871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631577584559818036841161 3473683188419863527630871)
          ·
            refine ⟨5210524782629795291446307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473683188419863527630871 5210524782629795291446307)
            ·
              refine ⟨7815787173944692937169461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210524782629795291446307 7815787173944692937169461)
              ·
                refine ⟨732730047557314962859637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7815787173944692937169461 732730047557314962859637)
                ·
                  refine ⟨68693441958498277768091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732730047557314962859637 68693441958498277768091)
                  ·
                    rfl

theorem cell23_1204020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1204020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204020 prefixEnd_1204020 := by exact prefixLift 1204020
  have htrace : WordTrace (prefixWord ++ tailWord_1204020) baseStart_1204020 baseEnd_1204020 := by
    simpa [prefixWord, tailWord_1204020, baseEnd_1204020] using wordTrace_append hprefix tailTrace_1204020
  have hstable : (prefixWord ++ tailWord_1204020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204020).length < 2 ^ (prefixWord ++ tailWord_1204020).sum := by decide
  have hdescent : baseEnd_1204020 < baseStart_1204020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204063 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 3, 4]
def baseStart_1204063 : Nat := 118140960795 + 1204063 * 2 ^ 59
def prefixEnd_1204063 : Nat := 4983230072969 + 3 ^ 40 * 1204063 * 2
def baseEnd_1204063 : Nat := 206087685764875943891707

theorem tailTrace_1204063 : CollatzResearch.WordTrace tailWord_1204063 prefixEnd_1204063 206087685764875943891707 := by
  unfold tailWord_1204063
  simp only [CollatzResearch.WordTrace]
  refine ⟨43915785436892863433864843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29277190291261908955909895 43915785436892863433864843)
  ·
    refine ⟨65873678155339295150797265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43915785436892863433864843 65873678155339295150797265)
    ·
      refine ⟨49405258616504471363097949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65873678155339295150797265 49405258616504471363097949)
      ·
        refine ⟨18526971981189176761161731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49405258616504471363097949 18526971981189176761161731)
        ·
          refine ⟨27790457971783765141742597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18526971981189176761161731 27790457971783765141742597)
          ·
            refine ⟨5210710869709455964076737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27790457971783765141742597 5210710869709455964076737)
            ·
              refine ⟨3908033152282091973057553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210710869709455964076737 3908033152282091973057553)
              ·
                refine ⟨2931024864211568979793165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908033152282091973057553 2931024864211568979793165)
                ·
                  refine ⟨1099134324079338367422437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2931024864211568979793165 1099134324079338367422437)
                  ·
                    refine ⟨206087685764875943891707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099134324079338367422437 206087685764875943891707)
                    ·
                      rfl

theorem cell23_1204063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_1204063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204063 prefixEnd_1204063 := by exact prefixLift 1204063
  have htrace : WordTrace (prefixWord ++ tailWord_1204063) baseStart_1204063 baseEnd_1204063 := by
    simpa [prefixWord, tailWord_1204063, baseEnd_1204063] using wordTrace_append hprefix tailTrace_1204063
  have hstable : (prefixWord ++ tailWord_1204063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204063).length < 2 ^ (prefixWord ++ tailWord_1204063).sum := by decide
  have hdescent : baseEnd_1204063 < baseStart_1204063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204076 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 8]
def baseStart_1204076 : Nat := 118140960795 + 1204076 * 2 ^ 59
def prefixEnd_1204076 : Nat := 4983230072969 + 3 ^ 40 * 1204076 * 2
def baseEnd_1204076 : Nat := 68696636949237364534729

theorem tailTrace_1204076 : CollatzResearch.WordTrace tailWord_1204076 prefixEnd_1204076 68696636949237364534729 := by
  unfold tailWord_1204076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21958129792922883327044041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29277506390563844436058721 21958129792922883327044041)
  ·
    refine ⟨16468597344692162495283031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21958129792922883327044041 16468597344692162495283031)
    ·
      refine ⟨24702896017038243742924547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16468597344692162495283031 24702896017038243742924547)
      ·
        refine ⟨37054344025557365614386821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24702896017038243742924547 37054344025557365614386821)
        ·
          refine ⟨6947689504792006052697529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37054344025557365614386821 6947689504792006052697529)
          ·
            refine ⟨5210767128594004539523147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6947689504792006052697529 5210767128594004539523147)
            ·
              refine ⟨7816150692891006809284721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210767128594004539523147 7816150692891006809284721)
              ·
                refine ⟨5862113019668255106963541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7816150692891006809284721 5862113019668255106963541)
                ·
                  refine ⟨68696636949237364534729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5862113019668255106963541 68696636949237364534729)
                  ·
                    rfl

theorem cell23_1204076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_1204076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204076 prefixEnd_1204076 := by exact prefixLift 1204076
  have htrace : WordTrace (prefixWord ++ tailWord_1204076) baseStart_1204076 baseEnd_1204076 := by
    simpa [prefixWord, tailWord_1204076, baseEnd_1204076] using wordTrace_append hprefix tailTrace_1204076
  have hstable : (prefixWord ++ tailWord_1204076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204076).length < 2 ^ (prefixWord ++ tailWord_1204076).sum := by decide
  have hdescent : baseEnd_1204076 < baseStart_1204076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204113 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_1204113 : Nat := 118140960795 + 1204113 * 2 ^ 59
def prefixEnd_1204113 : Nat := 4983230072969 + 3 ^ 40 * 1204113 * 2
def baseEnd_1204113 : Nat := 618288731327352636049891

theorem tailTrace_1204113 : CollatzResearch.WordTrace tailWord_1204113 prefixEnd_1204113 618288731327352636049891 := by
  unfold tailWord_1204113
  simp only [CollatzResearch.WordTrace]
  refine ⟨43917609086711721973184993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29278406057807814648789995 43917609086711721973184993)
  ·
    refine ⟨32938206815033791479888745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43917609086711721973184993 32938206815033791479888745)
    ·
      refine ⟨24703655111275343609916559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32938206815033791479888745 24703655111275343609916559)
      ·
        refine ⟨37055482666913015414874839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24703655111275343609916559 37055482666913015414874839)
        ·
          refine ⟨55583224000369523122312259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37055482666913015414874839 55583224000369523122312259)
          ·
            refine ⟨83374836000554284683468389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55583224000369523122312259 83374836000554284683468389)
            ·
              refine ⟨15632781750103928378150323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83374836000554284683468389 15632781750103928378150323)
              ·
                refine ⟨23449172625155892567225485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15632781750103928378150323 23449172625155892567225485)
                ·
                  refine ⟨8793439734433459712709557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23449172625155892567225485 8793439734433459712709557)
                  ·
                    refine ⟨824384975103136848066521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8793439734433459712709557 824384975103136848066521)
                    ·
                      refine ⟨618288731327352636049891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824384975103136848066521 618288731327352636049891)
                      ·
                        rfl

theorem cell23_1204113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_1204113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204113 prefixEnd_1204113 := by exact prefixLift 1204113
  have htrace : WordTrace (prefixWord ++ tailWord_1204113) baseStart_1204113 baseEnd_1204113 := by
    simpa [prefixWord, tailWord_1204113, baseEnd_1204113] using wordTrace_append hprefix tailTrace_1204113
  have hstable : (prefixWord ++ tailWord_1204113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204113).length < 2 ^ (prefixWord ++ tailWord_1204113).sum := by decide
  have hdescent : baseEnd_1204113 < baseStart_1204113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204148 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1204148 : Nat := 118140960795 + 1204148 * 2 ^ 59
def prefixEnd_1204148 : Nat := 4983230072969 + 3 ^ 40 * 1204148 * 2
def baseEnd_1204148 : Nat := 206102234383419999704077

theorem tailTrace_1204148 : CollatzResearch.WordTrace tailWord_1204148 prefixEnd_1204148 206102234383419999704077 := by
  unfold tailWord_1204148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959442820792461475354549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29279257094389948633806065 21959442820792461475354549)
  ·
    refine ⟨2058697764449293263314489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21959442820792461475354549 2058697764449293263314489)
    ·
      refine ⟨1544023323336969947485867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058697764449293263314489 1544023323336969947485867)
      ·
        refine ⟨2316034985005454921228801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544023323336969947485867 2316034985005454921228801)
        ·
          refine ⟨1737026238754091190921601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316034985005454921228801 1737026238754091190921601)
          ·
            refine ⟨1302769679065568393191201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737026238754091190921601 1302769679065568393191201)
            ·
              refine ⟨977077259299176294893401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302769679065568393191201 977077259299176294893401)
              ·
                refine ⟨732807944474382221170051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977077259299176294893401 732807944474382221170051)
                ·
                  refine ⟨1099211916711573331755077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732807944474382221170051 1099211916711573331755077)
                  ·
                    refine ⟨206102234383419999704077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099211916711573331755077 206102234383419999704077)
                    ·
                      rfl

theorem cell23_1204148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1204148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204148 prefixEnd_1204148 := by exact prefixLift 1204148
  have htrace : WordTrace (prefixWord ++ tailWord_1204148) baseStart_1204148 baseEnd_1204148 := by
    simpa [prefixWord, tailWord_1204148, baseEnd_1204148] using wordTrace_append hprefix tailTrace_1204148
  have hstable : (prefixWord ++ tailWord_1204148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204148).length < 2 ^ (prefixWord ++ tailWord_1204148).sum := by decide
  have hdescent : baseEnd_1204148 < baseStart_1204148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204170 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1204170 : Nat := 118140960795 + 1204170 * 2 ^ 59
def prefixEnd_1204170 : Nat := 4983230072969 + 3 ^ 40 * 1204170 * 2
def baseEnd_1204170 : Nat := 206105999908219637679043

theorem tailTrace_1204170 : CollatzResearch.WordTrace tailWord_1204170 prefixEnd_1204170 206105999908219637679043 := by
  unfold tailWord_1204170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10979922011876305177002491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29279792031670147138673309 10979922011876305177002491)
  ·
    refine ⟨16469883017814457765503737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10979922011876305177002491 16469883017814457765503737)
    ·
      refine ⟨12352412263360843324127803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16469883017814457765503737 12352412263360843324127803)
      ·
        refine ⟨18528618395041264986191705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12352412263360843324127803 18528618395041264986191705)
        ·
          refine ⟨13896463796280948739643779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18528618395041264986191705 13896463796280948739643779)
          ·
            refine ⟨20844695694421423109465669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13896463796280948739643779 20844695694421423109465669)
            ·
              refine ⟨3908380442704016833024813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20844695694421423109465669 3908380442704016833024813)
              ·
                refine ⟨1465642666014006312384305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908380442704016833024813 1465642666014006312384305)
                ·
                  refine ⟨1099231999510504734288229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465642666014006312384305 1099231999510504734288229)
                  ·
                    refine ⟨206105999908219637679043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099231999510504734288229 206105999908219637679043)
                    ·
                      rfl

theorem cell23_1204170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1204170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204170 prefixEnd_1204170 := by exact prefixLift 1204170
  have htrace : WordTrace (prefixWord ++ tailWord_1204170) baseStart_1204170 baseEnd_1204170 := by
    simpa [prefixWord, tailWord_1204170, baseEnd_1204170] using wordTrace_append hprefix tailTrace_1204170
  have hstable : (prefixWord ++ tailWord_1204170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204170).length < 2 ^ (prefixWord ++ tailWord_1204170).sum := by decide
  have hdescent : baseEnd_1204170 < baseStart_1204170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204180 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1204180 : Nat := 118140960795 + 1204180 * 2 ^ 59
def prefixEnd_1204180 : Nat := 4983230072969 + 3 ^ 40 * 1204180 * 2
def baseEnd_1204180 : Nat := 618323134531203873912083

theorem tailTrace_1204180 : CollatzResearch.WordTrace tailWord_1204180 prefixEnd_1204180 618323134531203873912083 := by
  unfold tailWord_1204180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21960026388734496207936997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29280035184979328277249329 21960026388734496207936997)
  ·
    refine ⟨4117504947887718038988187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21960026388734496207936997 4117504947887718038988187)
    ·
      refine ⟨6176257421831577058482281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117504947887718038988187 6176257421831577058482281)
      ·
        refine ⟨4632193066373682793861711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6176257421831577058482281 4632193066373682793861711)
        ·
          refine ⟨6948289599560524190792567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632193066373682793861711 6948289599560524190792567)
          ·
            refine ⟨10422434399340786286188851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948289599560524190792567 10422434399340786286188851)
            ·
              refine ⟨15633651599011179429283277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10422434399340786286188851 15633651599011179429283277)
              ·
                refine ⟨5862619349629192285981229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15633651599011179429283277 5862619349629192285981229)
                ·
                  refine ⟨2198482256110947107242961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5862619349629192285981229 2198482256110947107242961)
                  ·
                    refine ⟨1648861692083210330432221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2198482256110947107242961 1648861692083210330432221)
                    ·
                      refine ⟨618323134531203873912083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1648861692083210330432221 618323134531203873912083)
                      ·
                        rfl

theorem cell23_1204180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1204180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204180 prefixEnd_1204180 := by exact prefixLift 1204180
  have htrace : WordTrace (prefixWord ++ tailWord_1204180) baseStart_1204180 baseEnd_1204180 := by
    simpa [prefixWord, tailWord_1204180, baseEnd_1204180] using wordTrace_append hprefix tailTrace_1204180
  have hstable : (prefixWord ++ tailWord_1204180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204180).length < 2 ^ (prefixWord ++ tailWord_1204180).sum := by decide
  have hdescent : baseEnd_1204180 < baseStart_1204180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204183 : List Nat := [1, 1, 3, 2, 1, 1, 7, 7]
def baseStart_1204183 : Nat := 118140960795 + 1204183 * 2 ^ 59
def prefixEnd_1204183 : Nat := 4983230072969 + 3 ^ 40 * 1204183 * 2
def baseEnd_1204183 : Nat := 22900913887895087487947

theorem tailTrace_1204183 : CollatzResearch.WordTrace tailWord_1204183 prefixEnd_1204183 22900913887895087487947 := by
  unfold tailWord_1204183
  simp only [CollatzResearch.WordTrace]
  refine ⟨43920162196458123928233203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29280108130972082618822135 43920162196458123928233203)
  ·
    refine ⟨65880243294687185892349805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43920162196458123928233203 65880243294687185892349805)
    ·
      refine ⟨24705091235507694709631177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65880243294687185892349805 24705091235507694709631177)
      ·
        refine ⟨18528818426630771032223383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24705091235507694709631177 18528818426630771032223383)
        ·
          refine ⟨27793227639946156548335075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18528818426630771032223383 27793227639946156548335075)
          ·
            refine ⟨41689841459919234822502613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27793227639946156548335075 41689841459919234822502613)
            ·
              refine ⟨977105659216857066152405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41689841459919234822502613 977105659216857066152405)
              ·
                refine ⟨22900913887895087487947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 977105659216857066152405 22900913887895087487947)
                ·
                  rfl

theorem cell23_1204183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 7].length) (baseStart_1204183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204183 prefixEnd_1204183 := by exact prefixLift 1204183
  have htrace : WordTrace (prefixWord ++ tailWord_1204183) baseStart_1204183 baseEnd_1204183 := by
    simpa [prefixWord, tailWord_1204183, baseEnd_1204183] using wordTrace_append hprefix tailTrace_1204183
  have hstable : (prefixWord ++ tailWord_1204183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204183).length < 2 ^ (prefixWord ++ tailWord_1204183).sum := by decide
  have hdescent : baseEnd_1204183 < baseStart_1204183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204194 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1204194 : Nat := 118140960795 + 1204194 * 2 ^ 59
def prefixEnd_1204194 : Nat := 4983230072969 + 3 ^ 40 * 1204194 * 2
def baseEnd_1204194 : Nat := 618330323260366819137019

theorem tailTrace_1204194 : CollatzResearch.WordTrace tailWord_1204194 prefixEnd_1204194 618330323260366819137019 := by
  unfold tailWord_1204194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980140849854568201720909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29280375599612181871255757 10980140849854568201720909)
  ·
    refine ⟨4117552818695463075645341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10980140849854568201720909 4117552818695463075645341)
    ·
      refine ⟨1544082307010798653367003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4117552818695463075645341 1544082307010798653367003)
      ·
        refine ⟨2316123460516197980050505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544082307010798653367003 2316123460516197980050505)
        ·
          refine ⟨1737092595387148485037879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316123460516197980050505 1737092595387148485037879)
          ·
            refine ⟨2605638893080722727556819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737092595387148485037879 2605638893080722727556819)
            ·
              refine ⟨3908458339621084091335229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605638893080722727556819 3908458339621084091335229)
              ·
                refine ⟨1465671877357906534250711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908458339621084091335229 1465671877357906534250711)
                ·
                  refine ⟨2198507816036859801376067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465671877357906534250711 2198507816036859801376067)
                  ·
                    refine ⟨3297761724055289702064101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2198507816036859801376067 3297761724055289702064101)
                    ·
                      refine ⟨618330323260366819137019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3297761724055289702064101 618330323260366819137019)
                      ·
                        rfl

theorem cell23_1204194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1204194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204194 prefixEnd_1204194 := by exact prefixLift 1204194
  have htrace : WordTrace (prefixWord ++ tailWord_1204194) baseStart_1204194 baseEnd_1204194 := by
    simpa [prefixWord, tailWord_1204194, baseEnd_1204194] using wordTrace_append hprefix tailTrace_1204194
  have hstable : (prefixWord ++ tailWord_1204194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204194).length < 2 ^ (prefixWord ++ tailWord_1204194).sum := by decide
  have hdescent : baseEnd_1204194 < baseStart_1204194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204284 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_1204284 : Nat := 118140960795 + 1204284 * 2 ^ 59
def prefixEnd_1204284 : Nat := 4983230072969 + 3 ^ 40 * 1204284 * 2
def baseEnd_1204284 : Nat := 618376536519271467011605

theorem tailTrace_1204284 : CollatzResearch.WordTrace tailWord_1204284 prefixEnd_1204284 618376536519271467011605 := by
  unfold tailWord_1204284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961922984546109088829953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29282563979394812118439937 21961922984546109088829953)
  ·
    refine ⟨16471442238409581816622465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21961922984546109088829953 16471442238409581816622465)
    ·
      refine ⟨12353581678807186362466849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16471442238409581816622465 12353581678807186362466849)
      ·
        refine ⟨9265186259105389771850137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12353581678807186362466849 9265186259105389771850137)
        ·
          refine ⟨6948889694329042328887603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9265186259105389771850137 6948889694329042328887603)
          ·
            refine ⟨10423334541493563493331405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948889694329042328887603 10423334541493563493331405)
            ·
              refine ⟨3908750453060086309999277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10423334541493563493331405 3908750453060086309999277)
              ·
                refine ⟨1465781419897532366249729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908750453060086309999277 1465781419897532366249729)
                ·
                  refine ⟨1099336064923149274687297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465781419897532366249729 1099336064923149274687297)
                  ·
                    refine ⟨824502048692361956015473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099336064923149274687297 824502048692361956015473)
                    ·
                      refine ⟨618376536519271467011605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824502048692361956015473 618376536519271467011605)
                      ·
                        rfl

theorem cell23_1204284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_1204284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204284 prefixEnd_1204284 := by exact prefixLift 1204284
  have htrace : WordTrace (prefixWord ++ tailWord_1204284) baseStart_1204284 baseEnd_1204284 := by
    simpa [prefixWord, tailWord_1204284, baseEnd_1204284] using wordTrace_append hprefix tailTrace_1204284
  have hstable : (prefixWord ++ tailWord_1204284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204284).length < 2 ^ (prefixWord ++ tailWord_1204284).sum := by decide
  have hdescent : baseEnd_1204284 < baseStart_1204284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204303 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 6, 5]
def baseStart_1204303 : Nat := 118140960795 + 1204303 * 2 ^ 59
def prefixEnd_1204303 : Nat := 4983230072969 + 3 ^ 40 * 1204303 * 2
def baseEnd_1204303 : Nat := 206128764217235630891339

theorem tailTrace_1204303 : CollatzResearch.WordTrace tailWord_1204303 prefixEnd_1204303 206128764217235630891339 := by
  unfold tailWord_1204303
  simp only [CollatzResearch.WordTrace]
  refine ⟨43924538956023384422601563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29283025970682256281734375 43924538956023384422601563)
  ·
    refine ⟨65886808434035076633902345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43924538956023384422601563 65886808434035076633902345)
    ·
      refine ⟨49415106325526307475426759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65886808434035076633902345 49415106325526307475426759)
      ·
        refine ⟨74122659488289461213140139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49415106325526307475426759 74122659488289461213140139)
        ·
          refine ⟨111183989232434191819710209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74122659488289461213140139 111183989232434191819710209)
          ·
            refine ⟨83387991924325643864782657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111183989232434191819710209 83387991924325643864782657)
            ·
              refine ⟨62540993943244232898586993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83387991924325643864782657 62540993943244232898586993)
              ·
                refine ⟨46905745457433174673940245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62540993943244232898586993 46905745457433174673940245)
                ·
                  refine ⟨2198706818317180062840949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46905745457433174673940245 2198706818317180062840949)
                  ·
                    refine ⟨206128764217235630891339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2198706818317180062840949 206128764217235630891339)
                    ·
                      rfl

theorem cell23_1204303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_1204303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204303 prefixEnd_1204303 := by exact prefixLift 1204303
  have htrace : WordTrace (prefixWord ++ tailWord_1204303) baseStart_1204303 baseEnd_1204303 := by
    simpa [prefixWord, tailWord_1204303, baseEnd_1204303] using wordTrace_append hprefix tailTrace_1204303
  have hstable : (prefixWord ++ tailWord_1204303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204303).length < 2 ^ (prefixWord ++ tailWord_1204303).sum := by decide
  have hdescent : baseEnd_1204303 < baseStart_1204303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204313 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1204313 : Nat := 118140960795 + 1204313 * 2 ^ 59
def prefixEnd_1204313 : Nat := 4983230072969 + 3 ^ 40 * 1204313 * 2
def baseEnd_1204313 : Nat := 618391427458251853548971

theorem tailTrace_1204313 : CollatzResearch.WordTrace tailWord_1204313 prefixEnd_1204313 618391427458251853548971 := by
  unfold tailWord_1204313
  simp only [CollatzResearch.WordTrace]
  refine ⟨43924903685987156130465593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29283269123991437420310395 43924903685987156130465593)
  ·
    refine ⟨32943677764490367097849195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43924903685987156130465593 32943677764490367097849195)
    ·
      refine ⟨49415516646735550646773793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32943677764490367097849195 49415516646735550646773793)
      ·
        refine ⟨37061637485051662985080345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49415516646735550646773793 37061637485051662985080345)
        ·
          refine ⟨27796228113788747238810259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37061637485051662985080345 27796228113788747238810259)
          ·
            refine ⟨41694342170683120858215389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27796228113788747238810259 41694342170683120858215389)
            ·
              refine ⟨15635378314006170321830771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41694342170683120858215389 15635378314006170321830771)
              ·
                refine ⟨23453067471009255482746157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635378314006170321830771 23453067471009255482746157)
                ·
                  refine ⟨8794900301628470806029809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23453067471009255482746157 8794900301628470806029809)
                  ·
                    refine ⟨6596175226221353104522357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8794900301628470806029809 6596175226221353104522357)
                    ·
                      refine ⟨618391427458251853548971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6596175226221353104522357 618391427458251853548971)
                      ·
                        rfl

theorem cell23_1204313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1204313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204313 prefixEnd_1204313 := by exact prefixLift 1204313
  have htrace : WordTrace (prefixWord ++ tailWord_1204313) baseStart_1204313 baseEnd_1204313 := by
    simpa [prefixWord, tailWord_1204313, baseEnd_1204313] using wordTrace_append hprefix tailTrace_1204313
  have hstable : (prefixWord ++ tailWord_1204313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204313).length < 2 ^ (prefixWord ++ tailWord_1204313).sum := by decide
  have hdescent : baseEnd_1204313 < baseStart_1204313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204320 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_1204320 : Nat := 118140960795 + 1204320 * 2 ^ 59
def prefixEnd_1204320 : Nat := 4983230072969 + 3 ^ 40 * 1204320 * 2
def baseEnd_1204320 : Nat := 206131673940944442053813

theorem tailTrace_1204320 : CollatzResearch.WordTrace tailWord_1204320 prefixEnd_1204320 206131673940944442053813 := by
  unfold tailWord_1204320
  simp only [CollatzResearch.WordTrace]
  refine ⟨21962579498480898162985207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29283439331307864217313609 21962579498480898162985207)
  ·
    refine ⟨32943869247721347244477811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21962579498480898162985207 32943869247721347244477811)
    ·
      refine ⟨49415803871582020866716717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32943869247721347244477811 49415803871582020866716717)
      ·
        refine ⟨18530926451843257825018769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49415803871582020866716717 18530926451843257825018769)
        ·
          refine ⟨13898194838882443368764077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18530926451843257825018769 13898194838882443368764077)
          ·
            refine ⟨5211823064580916263286529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13898194838882443368764077 5211823064580916263286529)
            ·
              refine ⟨3908867298435687197464897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211823064580916263286529 3908867298435687197464897)
              ·
                refine ⟨2931650473826765398098673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908867298435687197464897 2931650473826765398098673)
                ·
                  refine ⟨2198737855370074048574005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2931650473826765398098673 2198737855370074048574005)
                  ·
                    refine ⟨206131673940944442053813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2198737855370074048574005 206131673940944442053813)
                    ·
                      rfl

theorem cell23_1204320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_1204320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204320 prefixEnd_1204320 := by exact prefixLift 1204320
  have htrace : WordTrace (prefixWord ++ tailWord_1204320) baseStart_1204320 baseEnd_1204320 := by
    simpa [prefixWord, tailWord_1204320, baseEnd_1204320] using wordTrace_append hprefix tailTrace_1204320
  have hstable : (prefixWord ++ tailWord_1204320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204320).length < 2 ^ (prefixWord ++ tailWord_1204320).sum := by decide
  have hdescent : baseEnd_1204320 < baseStart_1204320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204357 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_1204357 : Nat := 118140960795 + 1204357 * 2 ^ 59
def prefixEnd_1204357 : Nat := 4983230072969 + 3 ^ 40 * 1204357 * 2
def baseEnd_1204357 : Nat := 618414020607049681398769

theorem tailTrace_1204357 : CollatzResearch.WordTrace tailWord_1204357 prefixEnd_1204357 618414020607049681398769 := by
  unfold tailWord_1204357
  simp only [CollatzResearch.WordTrace]
  refine ⟨43926508497827751645067325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29284338998551834430044883 43926508497827751645067325)
  ·
    refine ⟨16472440686685406866900247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43926508497827751645067325 16472440686685406866900247)
    ·
      refine ⟨24708661030028110300350371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16472440686685406866900247 24708661030028110300350371)
      ·
        refine ⟨37062991545042165450525557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24708661030028110300350371 37062991545042165450525557)
        ·
          refine ⟨3474655457347703010986771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37062991545042165450525557 3474655457347703010986771)
          ·
            refine ⟨5211983186021554516480157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474655457347703010986771 5211983186021554516480157)
            ·
              refine ⟨1954493694758082943680059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5211983186021554516480157 1954493694758082943680059)
              ·
                refine ⟨2931740542137124415520089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954493694758082943680059 2931740542137124415520089)
                ·
                  refine ⟨2198805406602843311640067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2931740542137124415520089 2198805406602843311640067)
                  ·
                    refine ⟨3298208109904264967460101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2198805406602843311640067 3298208109904264967460101)
                    ·
                      refine ⟨618414020607049681398769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3298208109904264967460101 618414020607049681398769)
                      ·
                        rfl

theorem cell23_1204357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_1204357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204357 prefixEnd_1204357 := by exact prefixLift 1204357
  have htrace : WordTrace (prefixWord ++ tailWord_1204357) baseStart_1204357 baseEnd_1204357 := by
    simpa [prefixWord, tailWord_1204357, baseEnd_1204357] using wordTrace_append hprefix tailTrace_1204357
  have hstable : (prefixWord ++ tailWord_1204357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204357).length < 2 ^ (prefixWord ++ tailWord_1204357).sum := by decide
  have hdescent : baseEnd_1204357 < baseStart_1204357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204370 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1204370 : Nat := 118140960795 + 1204370 * 2 ^ 59
def prefixEnd_1204370 : Nat := 4983230072969 + 3 ^ 40 * 1204370 * 2
def baseEnd_1204370 : Nat := 618420695855558130536209

theorem tailTrace_1204370 : CollatzResearch.WordTrace tailWord_1204370 prefixEnd_1204370 618420695855558130536209 := by
  unfold tailWord_1204370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981745661695163716322641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29284655097853769910193709 10981745661695163716322641)
  ·
    refine ⟨8236309246271372787241981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10981745661695163716322641 8236309246271372787241981)
    ·
      refine ⟨3088615967351764795215743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8236309246271372787241981 3088615967351764795215743)
      ·
        refine ⟨4632923951027647192823615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088615967351764795215743 4632923951027647192823615)
        ·
          refine ⟨6949385926541470789235423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632923951027647192823615 6949385926541470789235423)
          ·
            refine ⟨10424078889812206183853135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949385926541470789235423 10424078889812206183853135)
            ·
              refine ⟨15636118334718309275779703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10424078889812206183853135 15636118334718309275779703)
              ·
                refine ⟨23454177502077463913669555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15636118334718309275779703 23454177502077463913669555)
                ·
                  refine ⟨35181266253116195870504333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23454177502077463913669555 35181266253116195870504333)
                  ·
                    refine ⟨13192974844918573451439125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35181266253116195870504333 13192974844918573451439125)
                    ·
                      refine ⟨618420695855558130536209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13192974844918573451439125 618420695855558130536209)
                      ·
                        rfl

theorem cell23_1204370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1204370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204370 prefixEnd_1204370 := by exact prefixLift 1204370
  have htrace : WordTrace (prefixWord ++ tailWord_1204370) baseStart_1204370 baseEnd_1204370 := by
    simpa [prefixWord, tailWord_1204370, baseEnd_1204370] using wordTrace_append hprefix tailTrace_1204370
  have hstable : (prefixWord ++ tailWord_1204370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204370).length < 2 ^ (prefixWord ++ tailWord_1204370).sum := by decide
  have hdescent : baseEnd_1204370 < baseStart_1204370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204380 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 8]
def baseStart_1204380 : Nat := 118140960795 + 1204380 * 2 ^ 59
def prefixEnd_1204380 : Nat := 4983230072969 + 3 ^ 40 * 1204380 * 2
def baseEnd_1204380 : Nat := 68713981184678121267907

theorem tailTrace_1204380 : CollatzResearch.WordTrace tailWord_1204380 prefixEnd_1204380 68713981184678121267907 := by
  unfold tailWord_1204380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963673688372213286577297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29284898251162951048769729 21963673688372213286577297)
  ·
    refine ⟨16472755266279159964932973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21963673688372213286577297 16472755266279159964932973)
    ·
      refine ⟨6177283224854684986849865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16472755266279159964932973 6177283224854684986849865)
      ·
        refine ⟨4632962418641013740137399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177283224854684986849865 4632962418641013740137399)
        ·
          refine ⟨6949443627961520610206099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632962418641013740137399 6949443627961520610206099)
          ·
            refine ⟨10424165441942280915309149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949443627961520610206099 10424165441942280915309149)
            ·
              refine ⟨3909062040728355343240931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10424165441942280915309149 3909062040728355343240931)
              ·
                refine ⟨5863593061092533014861397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909062040728355343240931 5863593061092533014861397)
                ·
                  refine ⟨68713981184678121267907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5863593061092533014861397 68713981184678121267907)
                  ·
                    rfl

theorem cell23_1204380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_1204380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204380 prefixEnd_1204380 := by exact prefixLift 1204380
  have htrace : WordTrace (prefixWord ++ tailWord_1204380) baseStart_1204380 baseEnd_1204380 := by
    simpa [prefixWord, tailWord_1204380, baseEnd_1204380] using wordTrace_append hprefix tailTrace_1204380
  have hstable : (prefixWord ++ tailWord_1204380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204380).length < 2 ^ (prefixWord ++ tailWord_1204380).sum := by decide
  have hdescent : baseEnd_1204380 < baseStart_1204380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204384 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 1, 4]
def baseStart_1204384 : Nat := 118140960795 + 1204384 * 2 ^ 59
def prefixEnd_1204384 : Nat := 4983230072969 + 3 ^ 40 * 1204384 * 2
def baseEnd_1204384 : Nat := 206142628194907025253715

theorem tailTrace_1204384 : CollatzResearch.WordTrace tailWord_1204384 prefixEnd_1204384 206142628194907025253715 := by
  unfold tailWord_1204384
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963746634364967628150103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29284995512486623504200137 21963746634364967628150103)
  ·
    refine ⟨32945619951547451442225155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21963746634364967628150103 32945619951547451442225155)
    ·
      refine ⟨49418429927321177163337733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32945619951547451442225155 49418429927321177163337733)
      ·
        refine ⟨9265955611372720718125825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49418429927321177163337733 9265955611372720718125825)
        ·
          refine ⟨6949466708529540538594369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9265955611372720718125825 6949466708529540538594369)
          ·
            refine ⟨5212100031397155403945777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949466708529540538594369 5212100031397155403945777)
            ·
              refine ⟨3909075023547866552959333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212100031397155403945777 3909075023547866552959333)
              ·
                refine ⟨732951566915224978679875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3909075023547866552959333 732951566915224978679875)
                ·
                  refine ⟨1099427350372837468019813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732951566915224978679875 1099427350372837468019813)
                  ·
                    refine ⟨206142628194907025253715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099427350372837468019813 206142628194907025253715)
                    ·
                      rfl

theorem cell23_1204384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_1204384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204384 prefixEnd_1204384 := by exact prefixLift 1204384
  have htrace : WordTrace (prefixWord ++ tailWord_1204384) baseStart_1204384 baseEnd_1204384 := by
    simpa [prefixWord, tailWord_1204384, baseEnd_1204384] using wordTrace_append hprefix tailTrace_1204384
  have hstable : (prefixWord ++ tailWord_1204384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204384).length < 2 ^ (prefixWord ++ tailWord_1204384).sum := by decide
  have hdescent : baseEnd_1204384 < baseStart_1204384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204410 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_1204410 : Nat := 118140960795 + 1204410 * 2 ^ 59
def prefixEnd_1204410 : Nat := 4983230072969 + 3 ^ 40 * 1204410 * 2
def baseEnd_1204410 : Nat := 206147078360579324678675

theorem tailTrace_1204410 : CollatzResearch.WordTrace tailWord_1204410 prefixEnd_1204410 206147078360579324678675 := by
  unfold tailWord_1204410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10982110391658935424186671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29285627711090494464497789 10982110391658935424186671)
  ·
    refine ⟨16473165587488403136280007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10982110391658935424186671 16473165587488403136280007)
    ·
      refine ⟨24709748381232604704420011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16473165587488403136280007 24709748381232604704420011)
      ·
        refine ⟨37064622571848907056630017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24709748381232604704420011 37064622571848907056630017)
        ·
          refine ⟨27798466928886680292472513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37064622571848907056630017 27798466928886680292472513)
          ·
            refine ⟨20848850196665010219354385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27798466928886680292472513 20848850196665010219354385)
            ·
              refine ⟨15636637647498757664515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20848850196665010219354385 15636637647498757664515789)
              ·
                refine ⟨5863739117812034124193421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15636637647498757664515789 5863739117812034124193421)
                ·
                  refine ⟨2198902169179512796572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5863739117812034124193421 2198902169179512796572533)
                  ·
                    refine ⟨206147078360579324678675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2198902169179512796572533 206147078360579324678675)
                    ·
                      rfl

theorem cell23_1204410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_1204410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204410 prefixEnd_1204410 := by exact prefixLift 1204410
  have htrace : WordTrace (prefixWord ++ tailWord_1204410) baseStart_1204410 baseEnd_1204410 := by
    simpa [prefixWord, tailWord_1204410, baseEnd_1204410] using wordTrace_append hprefix tailTrace_1204410
  have hstable : (prefixWord ++ tailWord_1204410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204410).length < 2 ^ (prefixWord ++ tailWord_1204410).sum := by decide
  have hdescent : baseEnd_1204410 < baseStart_1204410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204434 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1204434 : Nat := 118140960795 + 1204434 * 2 ^ 59
def prefixEnd_1204434 : Nat := 4983230072969 + 3 ^ 40 * 1204434 * 2
def baseEnd_1204434 : Nat := 618453558617445880135915

theorem tailTrace_1204434 : CollatzResearch.WordTrace tailWord_1204434 prefixEnd_1204434 618453558617445880135915 := by
  unfold tailWord_1204434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10982329229637198448905089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29286211279032529197080237 10982329229637198448905089)
  ·
    refine ⟨8236746922227898836678817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10982329229637198448905089 8236746922227898836678817)
    ·
      refine ⟨6177560191670924127509113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8236746922227898836678817 6177560191670924127509113)
      ·
        refine ⟨4633170143753193095631835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177560191670924127509113 4633170143753193095631835)
        ·
          refine ⟨6949755215629789643447753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633170143753193095631835 6949755215629789643447753)
          ·
            refine ⟨5212316411722342232585815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6949755215629789643447753 5212316411722342232585815)
            ·
              refine ⟨7818474617583513348878723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212316411722342232585815 7818474617583513348878723)
              ·
                refine ⟨11727711926375270023318085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7818474617583513348878723 11727711926375270023318085)
                ·
                  refine ⟨2198945986195363129372141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11727711926375270023318085 2198945986195363129372141)
                  ·
                    refine ⟨824604744823261173514553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2198945986195363129372141 824604744823261173514553)
                    ·
                      refine ⟨618453558617445880135915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824604744823261173514553 618453558617445880135915)
                      ·
                        rfl

theorem cell23_1204434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1204434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204434 prefixEnd_1204434 := by exact prefixLift 1204434
  have htrace : WordTrace (prefixWord ++ tailWord_1204434) baseStart_1204434 baseEnd_1204434 := by
    simpa [prefixWord, tailWord_1204434, baseEnd_1204434] using wordTrace_append hprefix tailTrace_1204434
  have hstable : (prefixWord ++ tailWord_1204434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204434).length < 2 ^ (prefixWord ++ tailWord_1204434).sum := by decide
  have hdescent : baseEnd_1204434 < baseStart_1204434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204457 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 2, 4]
def baseStart_1204457 : Nat := 118140960795 + 1204457 * 2 ^ 59
def prefixEnd_1204457 : Nat := 4983230072969 + 3 ^ 40 * 1204457 * 2
def baseEnd_1204457 : Nat := 206155122890833096716103

theorem tailTrace_1204457 : CollatzResearch.WordTrace tailWord_1204457 prefixEnd_1204457 206155122890833096716103 := by
  unfold tailWord_1204457
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930155797465468723707625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29286770531643645815805083 43930155797465468723707625)
  ·
    refine ⟨32947616848099101542780719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43930155797465468723707625 32947616848099101542780719)
    ·
      refine ⟨49421425272148652314171079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32947616848099101542780719 49421425272148652314171079)
      ·
        refine ⟨74132137908222978471256619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49421425272148652314171079 74132137908222978471256619)
        ·
          refine ⟨111198206862334467706884929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74132137908222978471256619 111198206862334467706884929)
          ·
            refine ⟨83398655146750850780163697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111198206862334467706884929 83398655146750850780163697)
            ·
              refine ⟨62548991360063138085122773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83398655146750850780163697 62548991360063138085122773)
              ·
                refine ⟨1465991985001479798870065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62548991360063138085122773 1465991985001479798870065)
                ·
                  refine ⟨1099493988751109849152549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465991985001479798870065 1099493988751109849152549)
                  ·
                    refine ⟨206155122890833096716103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1099493988751109849152549 206155122890833096716103)
                    ·
                      rfl

theorem cell23_1204457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 4].length) (baseStart_1204457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204457 prefixEnd_1204457 := by exact prefixLift 1204457
  have htrace : WordTrace (prefixWord ++ tailWord_1204457) baseStart_1204457 baseEnd_1204457 := by
    simpa [prefixWord, tailWord_1204457, baseEnd_1204457] using wordTrace_append hprefix tailTrace_1204457
  have hstable : (prefixWord ++ tailWord_1204457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204457).length < 2 ^ (prefixWord ++ tailWord_1204457).sum := by decide
  have hdescent : baseEnd_1204457 < baseStart_1204457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204460 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1204460 : Nat := 118140960795 + 1204460 * 2 ^ 59
def prefixEnd_1204460 : Nat := 4983230072969 + 3 ^ 40 * 1204460 * 2
def baseEnd_1204460 : Nat := 618466909114462778410795

theorem tailTrace_1204460 : CollatzResearch.WordTrace tailWord_1204460 prefixEnd_1204460 618466909114462778410795 := by
  unfold tailWord_1204460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21965132608227300118033417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29286843477636400157377889 21965132608227300118033417)
  ·
    refine ⟨16473849456170475088525063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21965132608227300118033417 16473849456170475088525063)
    ·
      refine ⟨24710774184255712632787595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16473849456170475088525063 24710774184255712632787595)
      ·
        refine ⟨37066161276383568949181393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24710774184255712632787595 37066161276383568949181393)
        ·
          refine ⟨27799620957287676711886045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37066161276383568949181393 27799620957287676711886045)
          ·
            refine ⟨10424857858982878766957267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27799620957287676711886045 10424857858982878766957267)
            ·
              refine ⟨15637286788474318150435901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10424857858982878766957267 15637286788474318150435901)
              ·
                refine ⟨5863982545677869306413463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15637286788474318150435901 5863982545677869306413463)
                ·
                  refine ⟨8795973818516803959620195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5863982545677869306413463 8795973818516803959620195)
                  ·
                    refine ⟨13193960727775205939430293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795973818516803959620195 13193960727775205939430293)
                    ·
                      refine ⟨618466909114462778410795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13193960727775205939430293 618466909114462778410795)
                      ·
                        rfl

theorem cell23_1204460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1204460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204460 prefixEnd_1204460 := by exact prefixLift 1204460
  have htrace : WordTrace (prefixWord ++ tailWord_1204460) baseStart_1204460 baseEnd_1204460 := by
    simpa [prefixWord, tailWord_1204460, baseEnd_1204460] using wordTrace_append hprefix tailTrace_1204460
  have hstable : (prefixWord ++ tailWord_1204460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204460).length < 2 ^ (prefixWord ++ tailWord_1204460).sum := by decide
  have hdescent : baseEnd_1204460 < baseStart_1204460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204461 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1204461 : Nat := 118140960795 + 1204461 * 2 ^ 59
def prefixEnd_1204461 : Nat := 4983230072969 + 3 ^ 40 * 1204461 * 2
def baseEnd_1204461 : Nat := 206155807531705758166097

theorem tailTrace_1204461 : CollatzResearch.WordTrace tailWord_1204461 prefixEnd_1204461 206155807531705758166097 := by
  unfold tailWord_1204461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930301689450977406853237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29286867792967318271235491 43930301689450977406853237)
  ·
    refine ⟨4118465783386029131892491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43930301689450977406853237 4118465783386029131892491)
    ·
      refine ⟨6177698675079043697838737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118465783386029131892491 6177698675079043697838737)
      ·
        refine ⟨4633274006309282773379053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177698675079043697838737 4633274006309282773379053)
        ·
          refine ⟨1737477752365981040017145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4633274006309282773379053 1737477752365981040017145)
          ·
            refine ⟨1303108314274485780012859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737477752365981040017145 1303108314274485780012859)
            ·
              refine ⟨1954662471411728670019289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303108314274485780012859 1954662471411728670019289)
              ·
                refine ⟨1465996853558796502514467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954662471411728670019289 1465996853558796502514467)
                ·
                  refine ⟨2198995280338194753771701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465996853558796502514467 2198995280338194753771701)
                  ·
                    refine ⟨206155807531705758166097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2198995280338194753771701 206155807531705758166097)
                    ·
                      rfl

theorem cell23_1204461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1204461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204461 prefixEnd_1204461 := by exact prefixLift 1204461
  have htrace : WordTrace (prefixWord ++ tailWord_1204461) baseStart_1204461 baseEnd_1204461 := by
    simpa [prefixWord, tailWord_1204461, baseEnd_1204461] using wordTrace_append hprefix tailTrace_1204461
  have hstable : (prefixWord ++ tailWord_1204461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204461).length < 2 ^ (prefixWord ++ tailWord_1204461).sum := by decide
  have hdescent : baseEnd_1204461 < baseStart_1204461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204464 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2]
def baseStart_1204464 : Nat := 118140960795 + 1204464 * 2 ^ 59
def prefixEnd_1204464 : Nat := 4983230072969 + 3 ^ 40 * 1204464 * 2
def baseEnd_1204464 : Nat := 618468963037080762760777

theorem tailTrace_1204464 : CollatzResearch.WordTrace tailWord_1204464 prefixEnd_1204464 618468963037080762760777 := by
  unfold tailWord_1204464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21965205554220054459606223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29286940738960072612808297 21965205554220054459606223)
  ·
    refine ⟨32947808331330081689409335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21965205554220054459606223 32947808331330081689409335)
    ·
      refine ⟨49421712496995122534114003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32947808331330081689409335 49421712496995122534114003)
      ·
        refine ⟨74132568745492683801171005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49421712496995122534114003 74132568745492683801171005)
        ·
          refine ⟨27799713279559756425439127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74132568745492683801171005 27799713279559756425439127)
          ·
            refine ⟨41699569919339634638158691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27799713279559756425439127 41699569919339634638158691)
            ·
              refine ⟨62549354879009451957238037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41699569919339634638158691 62549354879009451957238037)
              ·
                refine ⟨2932001009953568060495533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62549354879009451957238037 2932001009953568060495533)
                ·
                  refine ⟨1099500378732588022685825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2932001009953568060495533 1099500378732588022685825)
                  ·
                    refine ⟨824625284049441017014369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099500378732588022685825 824625284049441017014369)
                    ·
                      refine ⟨618468963037080762760777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824625284049441017014369 618468963037080762760777)
                      ·
                        rfl

theorem cell23_1204464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 2, 2].length) (baseStart_1204464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204464 prefixEnd_1204464 := by exact prefixLift 1204464
  have htrace : WordTrace (prefixWord ++ tailWord_1204464) baseStart_1204464 baseEnd_1204464 := by
    simpa [prefixWord, tailWord_1204464, baseEnd_1204464] using wordTrace_append hprefix tailTrace_1204464
  have hstable : (prefixWord ++ tailWord_1204464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204464).length < 2 ^ (prefixWord ++ tailWord_1204464).sum := by decide
  have hdescent : baseEnd_1204464 < baseStart_1204464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204467 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3]
def baseStart_1204467 : Nat := 118140960795 + 1204467 * 2 ^ 59
def prefixEnd_1204467 : Nat := 4983230072969 + 3 ^ 40 * 1204467 * 2
def baseEnd_1204467 : Nat := 618470503479044251023263

theorem tailTrace_1204467 : CollatzResearch.WordTrace tailWord_1204467 prefixEnd_1204467 618470503479044251023263 := by
  unfold tailWord_1204467
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930520527429240431571655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29287013684952826954381103 43930520527429240431571655)
  ·
    refine ⟨65895780791143860647357483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43930520527429240431571655 65895780791143860647357483)
    ·
      refine ⟨98843671186715790971036225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65895780791143860647357483 98843671186715790971036225)
      ·
        refine ⟨74132753390036843228277169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98843671186715790971036225 74132753390036843228277169)
        ·
          refine ⟨55599565042527632421207877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74132753390036843228277169 55599565042527632421207877)
          ·
            refine ⟨10424918445473931078976477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55599565042527632421207877 10424918445473931078976477)
            ·
              refine ⟨3909344417052724154616179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10424918445473931078976477 3909344417052724154616179)
              ·
                refine ⟨5864016625579086231924269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909344417052724154616179 5864016625579086231924269)
                ·
                  refine ⟨2199006234592157336971601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5864016625579086231924269 2199006234592157336971601)
                  ·
                    refine ⟨1649254675944118002728701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199006234592157336971601 1649254675944118002728701)
                    ·
                      refine ⟨618470503479044251023263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649254675944118002728701 618470503479044251023263)
                      ·
                        rfl

theorem cell23_1204467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_1204467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204467 prefixEnd_1204467 := by exact prefixLift 1204467
  have htrace : WordTrace (prefixWord ++ tailWord_1204467) baseStart_1204467 baseEnd_1204467 := by
    simpa [prefixWord, tailWord_1204467, baseEnd_1204467] using wordTrace_append hprefix tailTrace_1204467
  have hstable : (prefixWord ++ tailWord_1204467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204467).length < 2 ^ (prefixWord ++ tailWord_1204467).sum := by decide
  have hdescent : baseEnd_1204467 < baseStart_1204467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204487 : List Nat := [1, 1, 4, 5, 1, 11]
def baseStart_1204487 : Nat := 118140960795 + 1204487 * 2 ^ 59
def prefixEnd_1204487 : Nat := 4983230072969 + 3 ^ 40 * 1204487 * 2
def baseEnd_1204487 : Nat := 2545188366634297007297

theorem tailTrace_1204487 : CollatzResearch.WordTrace tailWord_1204487 prefixEnd_1204487 2545188366634297007297 := by
  unfold tailWord_1204487
  simp only [CollatzResearch.WordTrace]
  refine ⟨43931249987356783847299715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29287499991571189231533143 43931249987356783847299715)
  ·
    refine ⟨65896874981035175770949573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43931249987356783847299715 65896874981035175770949573)
    ·
      refine ⟨12355664058944095457053045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65896874981035175770949573 12355664058944095457053045)
      ·
        refine ⟨1158343505526008949098723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12355664058944095457053045 1158343505526008949098723)
        ·
          refine ⟨1737515258289013423648085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158343505526008949098723 1737515258289013423648085)
          ·
            refine ⟨2545188366634297007297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1737515258289013423648085 2545188366634297007297)
            ·
              rfl

theorem cell23_1204487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 11].length) (baseStart_1204487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204487 prefixEnd_1204487 := by exact prefixLift 1204487
  have htrace : WordTrace (prefixWord ++ tailWord_1204487) baseStart_1204487 baseEnd_1204487 := by
    simpa [prefixWord, tailWord_1204487, baseEnd_1204487] using wordTrace_append hprefix tailTrace_1204487
  have hstable : (prefixWord ++ tailWord_1204487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204487).length < 2 ^ (prefixWord ++ tailWord_1204487).sum := by decide
  have hdescent : baseEnd_1204487 < baseStart_1204487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204514 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1204514 : Nat := 118140960795 + 1204514 * 2 ^ 59
def prefixEnd_1204514 : Nat := 4983230072969 + 3 ^ 40 * 1204514 * 2
def baseEnd_1204514 : Nat := 618494637069805567135547

theorem tailTrace_1204514 : CollatzResearch.WordTrace tailWord_1204514 prefixEnd_1204514 618494637069805567135547 := by
  unfold tailWord_1204514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10983058689564741864633149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29288156505505978305688397 10983058689564741864633149)
  ·
    refine ⟨4118647008586778199237431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10983058689564741864633149 4118647008586778199237431)
    ·
      refine ⟨6177970512880167298856147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118647008586778199237431 6177970512880167298856147)
      ·
        refine ⟨9266955769320250948284221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6177970512880167298856147 9266955769320250948284221)
        ·
          refine ⟨3475108413495094105606583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9266955769320250948284221 3475108413495094105606583)
          ·
            refine ⟨5212662620242641158409875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475108413495094105606583 5212662620242641158409875)
            ·
              refine ⟨7818993930363961737614813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5212662620242641158409875 7818993930363961737614813)
              ·
                refine ⟨2932122723886485651605555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7818993930363961737614813 2932122723886485651605555)
                ·
                  refine ⟨4398184085829728477408333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932122723886485651605555 4398184085829728477408333)
                  ·
                    refine ⟨1649319032186148179028125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4398184085829728477408333 1649319032186148179028125)
                    ·
                      refine ⟨618494637069805567135547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649319032186148179028125 618494637069805567135547)
                      ·
                        rfl

theorem cell23_1204514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1204514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204514 prefixEnd_1204514 := by exact prefixLift 1204514
  have htrace : WordTrace (prefixWord ++ tailWord_1204514) baseStart_1204514 baseEnd_1204514 := by
    simpa [prefixWord, tailWord_1204514, baseEnd_1204514] using wordTrace_append hprefix tailTrace_1204514
  have hstable : (prefixWord ++ tailWord_1204514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204514).length < 2 ^ (prefixWord ++ tailWord_1204514).sum := by decide
  have hdescent : baseEnd_1204514 < baseStart_1204514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204524 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_1204524 : Nat := 118140960795 + 1204524 * 2 ^ 59
def prefixEnd_1204524 : Nat := 4983230072969 + 3 ^ 40 * 1204524 * 2
def baseEnd_1204524 : Nat := 618499771876350528010501

theorem tailTrace_1204524 : CollatzResearch.WordTrace tailWord_1204524 prefixEnd_1204524 618499771876350528010501 := by
  unfold tailWord_1204524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21966299744111369583198313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29288399658815159444264417 21966299744111369583198313)
  ·
    refine ⟨16474724808083527187398735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21966299744111369583198313 16474724808083527187398735)
    ·
      refine ⟨24712087212125290781098103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16474724808083527187398735 24712087212125290781098103)
      ·
        refine ⟨37068130818187936171647155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24712087212125290781098103 37068130818187936171647155)
        ·
          refine ⟨55602196227281904257470733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37068130818187936171647155 55602196227281904257470733)
          ·
            refine ⟨20850823585230714096551525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55602196227281904257470733 20850823585230714096551525)
            ·
              refine ⟨3909529422230758893103411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20850823585230714096551525 3909529422230758893103411)
              ·
                refine ⟨5864294133346138339655117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909529422230758893103411 5864294133346138339655117)
                ·
                  refine ⟨2199110300004801877370669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5864294133346138339655117 2199110300004801877370669)
                  ·
                    refine ⟨824666362501800704014001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199110300004801877370669 824666362501800704014001)
                    ·
                      refine ⟨618499771876350528010501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824666362501800704014001 618499771876350528010501)
                      ·
                        rfl

theorem cell23_1204524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_1204524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204524 prefixEnd_1204524 := by exact prefixLift 1204524
  have htrace : WordTrace (prefixWord ++ tailWord_1204524) baseStart_1204524 baseEnd_1204524 := by
    simpa [prefixWord, tailWord_1204524, baseEnd_1204524] using wordTrace_append hprefix tailTrace_1204524
  have hstable : (prefixWord ++ tailWord_1204524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204524).length < 2 ^ (prefixWord ++ tailWord_1204524).sum := by decide
  have hdescent : baseEnd_1204524 < baseStart_1204524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204548 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1204548 : Nat := 118140960795 + 1204548 * 2 ^ 59
def prefixEnd_1204548 : Nat := 4983230072969 + 3 ^ 40 * 1204548 * 2
def baseEnd_1204548 : Nat := 618512095412058434110391

theorem tailTrace_1204548 : CollatzResearch.WordTrace tailWord_1204548 prefixEnd_1204548 618512095412058434110391 := by
  unfold tailWord_1204548
  simp only [CollatzResearch.WordTrace]
  refine ⟨21966737420067895632635149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29288983226757194176846865 21966737420067895632635149)
  ·
    refine ⟨8237526532525460862238181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21966737420067895632635149 8237526532525460862238181)
    ·
      refine ⟨1544536224848523911669659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8237526532525460862238181 1544536224848523911669659)
      ·
        refine ⟨2316804337272785867504489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544536224848523911669659 2316804337272785867504489)
        ·
          refine ⟨1737603252954589400628367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316804337272785867504489 1737603252954589400628367)
          ·
            refine ⟨2606404879431884100942551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737603252954589400628367 2606404879431884100942551)
            ·
              refine ⟨3909607319147826151413827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606404879431884100942551 3909607319147826151413827)
              ·
                refine ⟨5864410978721739227120741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909607319147826151413827 5864410978721739227120741)
                ·
                  refine ⟨1099577058510326105085139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5864410978721739227120741 1099577058510326105085139)
                  ·
                    refine ⟨1649365587765489157627709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099577058510326105085139 1649365587765489157627709)
                    ·
                      refine ⟨618512095412058434110391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649365587765489157627709 618512095412058434110391)
                      ·
                        rfl

theorem cell23_1204548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1204548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204548 prefixEnd_1204548 := by exact prefixLift 1204548
  have htrace : WordTrace (prefixWord ++ tailWord_1204548) baseStart_1204548 baseEnd_1204548 := by
    simpa [prefixWord, tailWord_1204548, baseEnd_1204548] using wordTrace_append hprefix tailTrace_1204548
  have hstable : (prefixWord ++ tailWord_1204548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204548).length < 2 ^ (prefixWord ++ tailWord_1204548).sum := by decide
  have hdescent : baseEnd_1204548 < baseStart_1204548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204567 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1204567 : Nat := 118140960795 + 1204567 * 2 ^ 59
def prefixEnd_1204567 : Nat := 4983230072969 + 3 ^ 40 * 1204567 * 2
def baseEnd_1204567 : Nat := 618521851544493859772803

theorem tailTrace_1204567 : CollatzResearch.WordTrace tailWord_1204567 prefixEnd_1204567 618521851544493859772803 := by
  unfold tailWord_1204567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43934167827066957510211955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29289445218044638340141303 43934167827066957510211955)
  ·
    refine ⟨65901251740600436265317933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43934167827066957510211955 65901251740600436265317933)
    ·
      refine ⟨24712969402725163599494225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65901251740600436265317933 24712969402725163599494225)
      ·
        refine ⟨18534727052043872699620669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24712969402725163599494225 18534727052043872699620669)
        ·
          refine ⟨6950522644516452262357751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18534727052043872699620669 6950522644516452262357751)
          ·
            refine ⟨10425783966774678393536627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950522644516452262357751 10425783966774678393536627)
            ·
              refine ⟨15638675950162017590304941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10425783966774678393536627 15638675950162017590304941)
              ·
                refine ⟨5864503481310756596364353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15638675950162017590304941 5864503481310756596364353)
                ·
                  refine ⟨4398377610983067447273265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5864503481310756596364353 4398377610983067447273265)
                  ·
                    refine ⟨3298783208237300585454949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398377610983067447273265 3298783208237300585454949)
                    ·
                      refine ⟨618521851544493859772803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3298783208237300585454949 618521851544493859772803)
                      ·
                        rfl

theorem cell23_1204567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1204567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204567 prefixEnd_1204567 := by exact prefixLift 1204567
  have htrace : WordTrace (prefixWord ++ tailWord_1204567) baseStart_1204567 baseEnd_1204567 := by
    simpa [prefixWord, tailWord_1204567, baseEnd_1204567] using wordTrace_append hprefix tailTrace_1204567
  have hstable : (prefixWord ++ tailWord_1204567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204567).length < 2 ^ (prefixWord ++ tailWord_1204567).sum := by decide
  have hdescent : baseEnd_1204567 < baseStart_1204567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204607 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 2, 5]
def baseStart_1204607 : Nat := 118140960795 + 1204607 * 2 ^ 59
def prefixEnd_1204607 : Nat := 4983230072969 + 3 ^ 40 * 1204607 * 2
def baseEnd_1204607 : Nat := 206180796923557901090873

theorem tailTrace_1204607 : CollatzResearch.WordTrace tailWord_1204607 prefixEnd_1204607 206180796923557901090873 := by
  unfold tailWord_1204607
  simp only [CollatzResearch.WordTrace]
  refine ⟨43935626746922044341668075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29290417831281362894445383 43935626746922044341668075)
  ·
    refine ⟨65903440120383066512502113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43935626746922044341668075 65903440120383066512502113)
    ·
      refine ⟨49427580090287299884376585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65903440120383066512502113 49427580090287299884376585)
      ·
        refine ⟨37070685067715474913282439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49427580090287299884376585 37070685067715474913282439)
        ·
          refine ⟨55606027601573212369923659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37070685067715474913282439 55606027601573212369923659)
          ·
            refine ⟨83409041402359818554885489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55606027601573212369923659 83409041402359818554885489)
            ·
              refine ⟨62556781051769863916164117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83409041402359818554885489 62556781051769863916164117)
              ·
                refine ⟨2932349111801712371070193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62556781051769863916164117 2932349111801712371070193)
                ·
                  refine ⟨2199261833851284278302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932349111801712371070193 2199261833851284278302645)
                  ·
                    refine ⟨206180796923557901090873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2199261833851284278302645 206180796923557901090873)
                    ·
                      rfl

theorem cell23_1204607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_1204607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204607 prefixEnd_1204607 := by exact prefixLift 1204607
  have htrace : WordTrace (prefixWord ++ tailWord_1204607) baseStart_1204607 baseEnd_1204607 := by
    simpa [prefixWord, tailWord_1204607, baseEnd_1204607] using wordTrace_append hprefix tailTrace_1204607
  have hstable : (prefixWord ++ tailWord_1204607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204607).length < 2 ^ (prefixWord ++ tailWord_1204607).sum := by decide
  have hdescent : baseEnd_1204607 < baseStart_1204607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204611 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 7]
def baseStart_1204611 : Nat := 118140960795 + 1204611 * 2 ^ 59
def prefixEnd_1204611 : Nat := 4983230072969 + 3 ^ 40 * 1204611 * 2
def baseEnd_1204611 : Nat := 68727160521476854180289

theorem tailTrace_1204611 : CollatzResearch.WordTrace tailWord_1204611 prefixEnd_1204611 68727160521476854180289 := by
  unfold tailWord_1204611
  simp only [CollatzResearch.WordTrace]
  refine ⟨43935772638907553024813687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29290515092605035349875791 43935772638907553024813687)
  ·
    refine ⟨65903658958361329537220531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43935772638907553024813687 65903658958361329537220531)
    ·
      refine ⟨98855488437541994305830797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65903658958361329537220531 98855488437541994305830797)
      ·
        refine ⟨37070808164078247864686549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98855488437541994305830797 37070808164078247864686549)
        ·
          refine ⟨868847066345583934328591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37070808164078247864686549 868847066345583934328591)
          ·
            refine ⟨1303270599518375901492887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868847066345583934328591 1303270599518375901492887)
            ·
              refine ⟨1954905899277563852239331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303270599518375901492887 1954905899277563852239331)
              ·
                refine ⟨2932358848916345778358997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954905899277563852239331 2932358848916345778358997)
                ·
                  refine ⟨68727160521476854180289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2932358848916345778358997 68727160521476854180289)
                  ·
                    rfl

theorem cell23_1204611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 7].length) (baseStart_1204611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204611 prefixEnd_1204611 := by exact prefixLift 1204611
  have htrace : WordTrace (prefixWord ++ tailWord_1204611) baseStart_1204611 baseEnd_1204611 := by
    simpa [prefixWord, tailWord_1204611, baseEnd_1204611] using wordTrace_append hprefix tailTrace_1204611
  have hstable : (prefixWord ++ tailWord_1204611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204611).length < 2 ^ (prefixWord ++ tailWord_1204611).sum := by decide
  have hdescent : baseEnd_1204611 < baseStart_1204611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204617 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_1204617 : Nat := 118140960795 + 1204617 * 2 ^ 59
def prefixEnd_1204617 : Nat := 4983230072969 + 3 ^ 40 * 1204617 * 2
def baseEnd_1204617 : Nat := 618547525577218664147573

theorem tailTrace_1204617 : CollatzResearch.WordTrace tailWord_1204617 prefixEnd_1204617 618547525577218664147573 := by
  unfold tailWord_1204617
  simp only [CollatzResearch.WordTrace]
  refine ⟨43935991476885816049532105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29290660984590544033021403 43935991476885816049532105)
  ·
    refine ⟨32951993607664362037149079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43935991476885816049532105 32951993607664362037149079)
    ·
      refine ⟨49427990411496543055723619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32951993607664362037149079 49427990411496543055723619)
      ·
        refine ⟨74141985617244814583585429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49427990411496543055723619 74141985617244814583585429)
        ·
          refine ⟨3475405575808350683605567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74141985617244814583585429 3475405575808350683605567)
          ·
            refine ⟨5213108363712526025408351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475405575808350683605567 5213108363712526025408351)
            ·
              refine ⟨7819662545568789038112527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213108363712526025408351 7819662545568789038112527)
              ·
                refine ⟨11729493818353183557168791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819662545568789038112527 11729493818353183557168791)
                ·
                  refine ⟨17594240727529775335753187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11729493818353183557168791 17594240727529775335753187)
                  ·
                    refine ⟨26391361091294663003629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17594240727529775335753187 26391361091294663003629781)
                    ·
                      refine ⟨618547525577218664147573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26391361091294663003629781 618547525577218664147573)
                      ·
                        rfl

theorem cell23_1204617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_1204617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204617 prefixEnd_1204617 := by exact prefixLift 1204617
  have htrace : WordTrace (prefixWord ++ tailWord_1204617) baseStart_1204617 baseEnd_1204617 := by
    simpa [prefixWord, tailWord_1204617, baseEnd_1204617] using wordTrace_append hprefix tailTrace_1204617
  have hstable : (prefixWord ++ tailWord_1204617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204617).length < 2 ^ (prefixWord ++ tailWord_1204617).sum := by decide
  have hdescent : baseEnd_1204617 < baseStart_1204617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204622 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1204622 : Nat := 118140960795 + 1204622 * 2 ^ 59
def prefixEnd_1204622 : Nat := 4983230072969 + 3 ^ 40 * 1204622 * 2
def baseEnd_1204622 : Nat := 618550092980491144585051

theorem tailTrace_1204622 : CollatzResearch.WordTrace tailWord_1204622 prefixEnd_1204622 618550092980491144585051 := by
  unfold tailWord_1204622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492021730233462737933015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29290782561245134602309413 5492021730233462737933015)
  ·
    refine ⟨8238032595350194106899523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5492021730233462737933015 8238032595350194106899523)
    ·
      refine ⟨12357048893025291160349285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238032595350194106899523 12357048893025291160349285)
      ·
        refine ⟨2316946667442242092565491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12357048893025291160349285 2316946667442242092565491)
        ·
          refine ⟨3475420001163363138848237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316946667442242092565491 3475420001163363138848237)
          ·
            refine ⟨1303282500436261177068089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3475420001163363138848237 1303282500436261177068089)
            ·
              refine ⟨977461875327195882801067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303282500436261177068089 977461875327195882801067)
              ·
                refine ⟨1466192812990793824201601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977461875327195882801067 1466192812990793824201601)
                ·
                  refine ⟨1099644609743095368151201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466192812990793824201601 1099644609743095368151201)
                  ·
                    refine ⟨824733457307321526113401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099644609743095368151201 824733457307321526113401)
                    ·
                      refine ⟨618550092980491144585051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824733457307321526113401 618550092980491144585051)
                      ·
                        rfl

theorem cell23_1204622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1204622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204622 prefixEnd_1204622 := by exact prefixLift 1204622
  have htrace : WordTrace (prefixWord ++ tailWord_1204622) baseStart_1204622 baseEnd_1204622 := by
    simpa [prefixWord, tailWord_1204622, baseEnd_1204622] using wordTrace_append hprefix tailTrace_1204622
  have hstable : (prefixWord ++ tailWord_1204622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204622).length < 2 ^ (prefixWord ++ tailWord_1204622).sum := by decide
  have hdescent : baseEnd_1204622 < baseStart_1204622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204644 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1204644 : Nat := 118140960795 + 1204644 * 2 ^ 59
def prefixEnd_1204644 : Nat := 4983230072969 + 3 ^ 40 * 1204644 * 2
def baseEnd_1204644 : Nat := 618561389554890058509949

theorem tailTrace_1204644 : CollatzResearch.WordTrace tailWord_1204644 prefixEnd_1204644 618561389554890058509949 := by
  unfold tailWord_1204644
  simp only [CollatzResearch.WordTrace]
  refine ⟨21968488123893999830382493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29291317498525333107176657 21968488123893999830382493)
  ·
    refine ⟨8238183046460249936393435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21968488123893999830382493 8238183046460249936393435)
    ·
      refine ⟨12357274569690374904590153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238183046460249936393435 12357274569690374904590153)
      ·
        refine ⟨9267955927267781178442615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12357274569690374904590153 9267955927267781178442615)
        ·
          refine ⟨13901933890901671767663923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9267955927267781178442615 13901933890901671767663923)
          ·
            refine ⟨20852900836352507651495885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13901933890901671767663923 20852900836352507651495885)
            ·
              refine ⟨7819837813632190369310957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20852900836352507651495885 7819837813632190369310957)
              ·
                refine ⟨2932439180112071388491609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7819837813632190369310957 2932439180112071388491609)
                ·
                  refine ⟨2199329385084053541368707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932439180112071388491609 2199329385084053541368707)
                  ·
                    refine ⟨3298994077626080312053061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2199329385084053541368707 3298994077626080312053061)
                    ·
                      refine ⟨618561389554890058509949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3298994077626080312053061 618561389554890058509949)
                      ·
                        rfl

theorem cell23_1204644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1204644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204644 prefixEnd_1204644 := by exact prefixLift 1204644
  have htrace : WordTrace (prefixWord ++ tailWord_1204644) baseStart_1204644 baseEnd_1204644 := by
    simpa [prefixWord, tailWord_1204644, baseEnd_1204644] using wordTrace_append hprefix tailTrace_1204644
  have hstable : (prefixWord ++ tailWord_1204644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204644).length < 2 ^ (prefixWord ++ tailWord_1204644).sum := by decide
  have hdescent : baseEnd_1204644 < baseStart_1204644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204711 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1204711 : Nat := 118140960795 + 1204711 * 2 ^ 59
def prefixEnd_1204711 : Nat := 4983230072969 + 3 ^ 40 * 1204711 * 2
def baseEnd_1204711 : Nat := 618595792758741296372141

theorem tailTrace_1204711 : CollatzResearch.WordTrace tailWord_1204711 prefixEnd_1204711 618595792758741296372141 := by
  unfold tailWord_1204711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43939419938545270103453987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29292946625696846735635991 43939419938545270103453987)
  ·
    refine ⟨65909129907817905155180981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43939419938545270103453987 65909129907817905155180981)
    ·
      refine ⟨6178980928857928608298217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65909129907817905155180981 6178980928857928608298217)
      ·
        refine ⟨4634235696643446456223663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6178980928857928608298217 4634235696643446456223663)
        ·
          refine ⟨6951353544965169684335495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634235696643446456223663 6951353544965169684335495)
          ·
            refine ⟨10427030317447754526503243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951353544965169684335495 10427030317447754526503243)
            ·
              refine ⟨15640545476171631789754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427030317447754526503243 15640545476171631789754865)
              ·
                refine ⟨11730409107128723842316149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15640545476171631789754865 11730409107128723842316149)
                ·
                  refine ⟨1099725853793317860217139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11730409107128723842316149 1099725853793317860217139)
                  ·
                    refine ⟨1649588780689976790325709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099725853793317860217139 1649588780689976790325709)
                    ·
                      refine ⟨618595792758741296372141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649588780689976790325709 618595792758741296372141)
                      ·
                        rfl

theorem cell23_1204711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1204711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204711 prefixEnd_1204711 := by exact prefixLift 1204711
  have htrace : WordTrace (prefixWord ++ tailWord_1204711) baseStart_1204711 baseEnd_1204711 := by
    simpa [prefixWord, tailWord_1204711, baseEnd_1204711] using wordTrace_append hprefix tailTrace_1204711
  have hstable : (prefixWord ++ tailWord_1204711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204711).length < 2 ^ (prefixWord ++ tailWord_1204711).sum := by decide
  have hdescent : baseEnd_1204711 < baseStart_1204711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204721 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_1204721 : Nat := 118140960795 + 1204721 * 2 ^ 59
def prefixEnd_1204721 : Nat := 4983230072969 + 3 ^ 40 * 1204721 * 2
def baseEnd_1204721 : Nat := 618600927565286257247095

theorem tailTrace_1204721 : CollatzResearch.WordTrace tailWord_1204721 prefixEnd_1204721 618600927565286257247095 := by
  unfold tailWord_1204721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43939784668509041811318017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29293189779006027874212011 43939784668509041811318017)
  ·
    refine ⟨32954838501381781358488513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43939784668509041811318017 32954838501381781358488513)
    ·
      refine ⟨24716128876036336018866385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32954838501381781358488513 24716128876036336018866385)
      ·
        refine ⟨18537096657027252014149789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24716128876036336018866385 18537096657027252014149789)
        ·
          refine ⟨6951411246385219505306171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18537096657027252014149789 6951411246385219505306171)
          ·
            refine ⟨10427116869577829257959257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951411246385219505306171 10427116869577829257959257)
            ·
              refine ⟨7820337652183371943469443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10427116869577829257959257 7820337652183371943469443)
              ·
                refine ⟨11730506478275057915204165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7820337652183371943469443 11730506478275057915204165)
                ·
                  refine ⟨2199469964676573359100781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11730506478275057915204165 2199469964676573359100781)
                  ·
                    refine ⟨824801236753715009662793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2199469964676573359100781 824801236753715009662793)
                    ·
                      refine ⟨618600927565286257247095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824801236753715009662793 618600927565286257247095)
                      ·
                        rfl

theorem cell23_1204721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_1204721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204721 prefixEnd_1204721 := by exact prefixLift 1204721
  have htrace : WordTrace (prefixWord ++ tailWord_1204721) baseStart_1204721 baseEnd_1204721 := by
    simpa [prefixWord, tailWord_1204721, baseEnd_1204721] using wordTrace_append hprefix tailTrace_1204721
  have hstable : (prefixWord ++ tailWord_1204721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204721).length < 2 ^ (prefixWord ++ tailWord_1204721).sum := by decide
  have hdescent : baseEnd_1204721 < baseStart_1204721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204728 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_1204728 : Nat := 118140960795 + 1204728 * 2 ^ 59
def prefixEnd_1204728 : Nat := 4983230072969 + 3 ^ 40 * 1204728 * 2
def baseEnd_1204728 : Nat := 618604521929867729859563

theorem tailTrace_1204728 : CollatzResearch.WordTrace tailWord_1204728 prefixEnd_1204728 618604521929867729859563 := by
  unfold tailWord_1204728
  simp only [CollatzResearch.WordTrace]
  refine ⟨21970019989741841003411419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29293359986322454671215225 21970019989741841003411419)
  ·
    refine ⟨32955029984612761505117129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21970019989741841003411419 32955029984612761505117129)
    ·
      refine ⟨24716272488459571128837847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32955029984612761505117129 24716272488459571128837847)
      ·
        refine ⟨37074408732689356693256771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24716272488459571128837847 37074408732689356693256771)
        ·
          refine ⟨55611613099034035039885157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37074408732689356693256771 55611613099034035039885157)
          ·
            refine ⟨10427177456068881569978467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55611613099034035039885157 10427177456068881569978467)
            ·
              refine ⟨15640766184103322354967701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427177456068881569978467 15640766184103322354967701)
              ·
                refine ⟨733160914879843235389111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15640766184103322354967701 733160914879843235389111)
                ·
                  refine ⟨1099741372319764853083667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733160914879843235389111 1099741372319764853083667)
                  ·
                    refine ⟨1649612058479647279625501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099741372319764853083667 1649612058479647279625501)
                    ·
                      refine ⟨618604521929867729859563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649612058479647279625501 618604521929867729859563)
                      ·
                        rfl

theorem cell23_1204728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_1204728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204728 prefixEnd_1204728 := by exact prefixLift 1204728
  have htrace : WordTrace (prefixWord ++ tailWord_1204728) baseStart_1204728 baseEnd_1204728 := by
    simpa [prefixWord, tailWord_1204728, baseEnd_1204728] using wordTrace_append hprefix tailTrace_1204728
  have hstable : (prefixWord ++ tailWord_1204728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204728).length < 2 ^ (prefixWord ++ tailWord_1204728).sum := by decide
  have hdescent : baseEnd_1204728 < baseStart_1204728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204771 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1204771 : Nat := 118140960795 + 1204771 * 2 ^ 59
def prefixEnd_1204771 : Nat := 4983230072969 + 3 ^ 40 * 1204771 * 2
def baseEnd_1204771 : Nat := 618626601598011061621865

theorem tailTrace_1204771 : CollatzResearch.WordTrace tailWord_1204771 prefixEnd_1204771 618626601598011061621865 := by
  unfold tailWord_1204771
  simp only [CollatzResearch.WordTrace]
  refine ⟨43941608318327900350638167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29294405545551933567092111 43941608318327900350638167)
  ·
    refine ⟨65912412477491850525957251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43941608318327900350638167 65912412477491850525957251)
    ·
      refine ⟨98868618716237775788935877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65912412477491850525957251 98868618716237775788935877)
      ·
        refine ⟨18537866009294582960425477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98868618716237775788935877 18537866009294582960425477)
        ·
          refine ⟨3475849876742734305079777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18537866009294582960425477 3475849876742734305079777)
          ·
            refine ⟨2606887407557050728809833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475849876742734305079777 2606887407557050728809833)
            ·
              refine ⟨1955165555667788046607375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606887407557050728809833 1955165555667788046607375)
              ·
                refine ⟨2932748333501682069911063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955165555667788046607375 2932748333501682069911063)
                ·
                  refine ⟨4399122500252523104866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932748333501682069911063 4399122500252523104866595)
                  ·
                    refine ⟨6598683750378784657299893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4399122500252523104866595 6598683750378784657299893)
                    ·
                      refine ⟨618626601598011061621865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6598683750378784657299893 618626601598011061621865)
                      ·
                        rfl

theorem cell23_1204771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1204771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204771 prefixEnd_1204771 := by exact prefixLift 1204771
  have htrace : WordTrace (prefixWord ++ tailWord_1204771) baseStart_1204771 baseEnd_1204771 := by
    simpa [prefixWord, tailWord_1204771, baseEnd_1204771] using wordTrace_append hprefix tailTrace_1204771
  have hstable : (prefixWord ++ tailWord_1204771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204771).length < 2 ^ (prefixWord ++ tailWord_1204771).sum := by decide
  have hdescent : baseEnd_1204771 < baseStart_1204771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204785 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_1204785 : Nat := 118140960795 + 1204785 * 2 ^ 59
def prefixEnd_1204785 : Nat := 4983230072969 + 3 ^ 40 * 1204785 * 2
def baseEnd_1204785 : Nat := 618633790327174006846801

theorem tailTrace_1204785 : CollatzResearch.WordTrace tailWord_1204785 prefixEnd_1204785 618633790327174006846801 := by
  unfold tailWord_1204785
  simp only [CollatzResearch.WordTrace]
  refine ⟨43942118940277180741647809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29294745960184787161098539 43942118940277180741647809)
  ·
    refine ⟨32956589205207885556235857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43942118940277180741647809 32956589205207885556235857)
    ·
      refine ⟨24717441903905914167176893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32956589205207885556235857 24717441903905914167176893)
      ·
        refine ⟨9269040713964717812691335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24717441903905914167176893 9269040713964717812691335)
        ·
          refine ⟨13903561070947076719037003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9269040713964717812691335 13903561070947076719037003)
          ·
            refine ⟨20855341606420615078555505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13903561070947076719037003 20855341606420615078555505)
            ·
              refine ⟨15641506204815461308916629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20855341606420615078555505 15641506204815461308916629)
              ·
                refine ⟨733195603350724748855467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15641506204815461308916629 733195603350724748855467)
                ·
                  refine ⟨1099793405026087123283201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733195603350724748855467 1099793405026087123283201)
                  ·
                    refine ⟨824845053769565342462401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099793405026087123283201 824845053769565342462401)
                    ·
                      refine ⟨618633790327174006846801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824845053769565342462401 618633790327174006846801)
                      ·
                        rfl

theorem cell23_1204785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_1204785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204785 prefixEnd_1204785 := by exact prefixLift 1204785
  have htrace : WordTrace (prefixWord ++ tailWord_1204785) baseStart_1204785 baseEnd_1204785 := by
    simpa [prefixWord, tailWord_1204785, baseEnd_1204785] using wordTrace_append hprefix tailTrace_1204785
  have hstable : (prefixWord ++ tailWord_1204785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204785).length < 2 ^ (prefixWord ++ tailWord_1204785).sum := by decide
  have hdescent : baseEnd_1204785 < baseStart_1204785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204814 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1204814 : Nat := 118140960795 + 1204814 * 2 ^ 59
def prefixEnd_1204814 : Nat := 4983230072969 + 3 ^ 40 * 1204814 * 2
def baseEnd_1204814 : Nat := 618648681266154393384167

theorem tailTrace_1204814 : CollatzResearch.WordTrace tailWord_1204814 prefixEnd_1204814 618648681266154393384167 := by
  unfold tailWord_1204814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492897082146514836806687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29295451104781412462968997 5492897082146514836806687)
  ·
    refine ⟨8239345623219772255210031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5492897082146514836806687 8239345623219772255210031)
    ·
      refine ⟨12359018434829658382815047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8239345623219772255210031 12359018434829658382815047)
      ·
        refine ⟨18538527652244487574222571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12359018434829658382815047 18538527652244487574222571)
        ·
          refine ⟨27807791478366731361333857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18538527652244487574222571 27807791478366731361333857)
          ·
            refine ⟨20855843608775048521000393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27807791478366731361333857 20855843608775048521000393)
            ·
              refine ⟨15641882706581286390750295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20855843608775048521000393 15641882706581286390750295)
              ·
                refine ⟨23462824059871929586125443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15641882706581286390750295 23462824059871929586125443)
                ·
                  refine ⟨35194236089807894379188165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23462824059871929586125443 35194236089807894379188165)
                  ·
                    refine ⟨6598919266838980196097781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35194236089807894379188165 6598919266838980196097781)
                    ·
                      refine ⟨618648681266154393384167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6598919266838980196097781 618648681266154393384167)
                      ·
                        rfl

theorem cell23_1204814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1204814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204814 prefixEnd_1204814 := by exact prefixLift 1204814
  have htrace : WordTrace (prefixWord ++ tailWord_1204814) baseStart_1204814 baseEnd_1204814 := by
    simpa [prefixWord, tailWord_1204814, baseEnd_1204814] using wordTrace_append hprefix tailTrace_1204814
  have hstable : (prefixWord ++ tailWord_1204814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204814).length < 2 ^ (prefixWord ++ tailWord_1204814).sum := by decide
  have hdescent : baseEnd_1204814 < baseStart_1204814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204830 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1204830 : Nat := 118140960795 + 1204830 * 2 ^ 59
def prefixEnd_1204830 : Nat := 4983230072969 + 3 ^ 40 * 1204830 * 2
def baseEnd_1204830 : Nat := 618656896956626330784095

theorem tailTrace_1204830 : CollatzResearch.WordTrace tailWord_1204830 prefixEnd_1204830 618656896956626330784095 := by
  unfold tailWord_1204830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492970028139269178379493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29295840150076102284690629 5492970028139269178379493)
  ·
    refine ⟨1029931880276112970946155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5492970028139269178379493 1029931880276112970946155)
    ·
      refine ⟨1544897820414169456419233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029931880276112970946155 1544897820414169456419233)
      ·
        refine ⟨1158673365310627092314425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544897820414169456419233 1158673365310627092314425)
        ·
          refine ⟨869005023982970319235819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158673365310627092314425 869005023982970319235819)
          ·
            refine ⟨1303507535974455478853729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869005023982970319235819 1303507535974455478853729)
            ·
              refine ⟨977630651980841609140297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303507535974455478853729 977630651980841609140297)
              ·
                refine ⟨733222988985631206855223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977630651980841609140297 733222988985631206855223)
                ·
                  refine ⟨1099834483478446810282835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733222988985631206855223 1099834483478446810282835)
                  ·
                    refine ⟨1649751725217670215424253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099834483478446810282835 1649751725217670215424253)
                    ·
                      refine ⟨618656896956626330784095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1649751725217670215424253 618656896956626330784095)
                      ·
                        rfl

theorem cell23_1204830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1204830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204830 prefixEnd_1204830 := by exact prefixLift 1204830
  have htrace : WordTrace (prefixWord ++ tailWord_1204830) baseStart_1204830 baseEnd_1204830 := by
    simpa [prefixWord, tailWord_1204830, baseEnd_1204830] using wordTrace_append hprefix tailTrace_1204830
  have hstable : (prefixWord ++ tailWord_1204830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204830).length < 2 ^ (prefixWord ++ tailWord_1204830).sum := by decide
  have hdescent : baseEnd_1204830 < baseStart_1204830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204841 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 4, 2]
def baseStart_1204841 : Nat := 118140960795 + 1204841 * 2 ^ 59
def prefixEnd_1204841 : Nat := 4983230072969 + 3 ^ 40 * 1204841 * 2
def baseEnd_1204841 : Nat := 618662545243825787746543

theorem tailTrace_1204841 : CollatzResearch.WordTrace tailWord_1204841 prefixEnd_1204841 618662545243825787746543 := by
  unfold tailWord_1204841
  simp only [CollatzResearch.WordTrace]
  refine ⟨43944161428074302305686377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29296107618716201537124251 43944161428074302305686377)
  ·
    refine ⟨32958121071055726729264783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43944161428074302305686377 32958121071055726729264783)
    ·
      refine ⟨49437181606583590093897175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32958121071055726729264783 49437181606583590093897175)
      ·
        refine ⟨74155772409875385140845763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49437181606583590093897175 74155772409875385140845763)
        ·
          refine ⟨111233658614813077711268645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74155772409875385140845763 111233658614813077711268645)
          ·
            refine ⟨20856310990277452070862871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111233658614813077711268645 20856310990277452070862871)
            ·
              refine ⟨31284466485416178106294307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20856310990277452070862871 31284466485416178106294307)
              ·
                refine ⟨46926699728124267159441461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31284466485416178106294307 46926699728124267159441461)
                ·
                  refine ⟨4399378099511650046197637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46926699728124267159441461 4399378099511650046197637)
                  ·
                    refine ⟨824883393658434383662057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4399378099511650046197637 824883393658434383662057)
                    ·
                      refine ⟨618662545243825787746543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824883393658434383662057 618662545243825787746543)
                      ·
                        rfl

theorem cell23_1204841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4, 2].length) (baseStart_1204841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204841 prefixEnd_1204841 := by exact prefixLift 1204841
  have htrace : WordTrace (prefixWord ++ tailWord_1204841) baseStart_1204841 baseEnd_1204841 := by
    simpa [prefixWord, tailWord_1204841, baseEnd_1204841] using wordTrace_append hprefix tailTrace_1204841
  have hstable : (prefixWord ++ tailWord_1204841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204841).length < 2 ^ (prefixWord ++ tailWord_1204841).sum := by decide
  have hdescent : baseEnd_1204841 < baseStart_1204841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204844 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1204844 : Nat := 118140960795 + 1204844 * 2 ^ 59
def prefixEnd_1204844 : Nat := 4983230072969 + 3 ^ 40 * 1204844 * 2
def baseEnd_1204844 : Nat := 618664085685789276009029

theorem tailTrace_1204844 : CollatzResearch.WordTrace tailWord_1204844 prefixEnd_1204844 618664085685789276009029 := by
  unfold tailWord_1204844
  simp only [CollatzResearch.WordTrace]
  refine ⟨21972135423531716909022793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29296180564708955878697057 21972135423531716909022793)
  ·
    refine ⟨16479101567648787681767095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21972135423531716909022793 16479101567648787681767095)
    ·
      refine ⟨24718652351473181522650643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16479101567648787681767095 24718652351473181522650643)
      ·
        refine ⟨37077978527209772283975965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24718652351473181522650643 37077978527209772283975965)
        ·
          refine ⟨13904241947703664606490987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37077978527209772283975965 13904241947703664606490987)
          ·
            refine ⟨20856362921555496909736481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13904241947703664606490987 20856362921555496909736481)
            ·
              refine ⟨15642272191166622682302361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20856362921555496909736481 15642272191166622682302361)
              ·
                refine ⟨11731704143374967011726771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15642272191166622682302361 11731704143374967011726771)
                ·
                  refine ⟨17597556215062450517590157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11731704143374967011726771 17597556215062450517590157)
                  ·
                    refine ⟨6599083580648418944096309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17597556215062450517590157 6599083580648418944096309)
                    ·
                      refine ⟨618664085685789276009029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6599083580648418944096309 618664085685789276009029)
                      ·
                        rfl

theorem cell23_1204844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1204844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204844 prefixEnd_1204844 := by exact prefixLift 1204844
  have htrace : WordTrace (prefixWord ++ tailWord_1204844) baseStart_1204844 baseEnd_1204844 := by
    simpa [prefixWord, tailWord_1204844, baseEnd_1204844] using wordTrace_append hprefix tailTrace_1204844
  have hstable : (prefixWord ++ tailWord_1204844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204844).length < 2 ^ (prefixWord ++ tailWord_1204844).sum := by decide
  have hdescent : baseEnd_1204844 < baseStart_1204844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204864 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 9]
def baseStart_1204864 : Nat := 118140960795 + 1204864 * 2 ^ 59
def prefixEnd_1204864 : Nat := 4983230072969 + 3 ^ 40 * 1204864 * 2
def baseEnd_1204864 : Nat := 68741595033208799750993

theorem tailTrace_1204864 : CollatzResearch.WordTrace tailWord_1204864 prefixEnd_1204864 68741595033208799750993 := by
  unfold tailWord_1204864
  simp only [CollatzResearch.WordTrace]
  refine ⟨21972500153495488616886823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29296666871327318155849097 21972500153495488616886823)
  ·
    refine ⟨32958750230243232925330235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21972500153495488616886823 32958750230243232925330235)
    ·
      refine ⟨49438125345364849387995353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32958750230243232925330235 49438125345364849387995353)
      ·
        refine ⟨37078594009023637040996515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49438125345364849387995353 37078594009023637040996515)
        ·
          refine ⟨55617891013535455561494773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37078594009023637040996515 55617891013535455561494773)
          ·
            refine ⟨5214177282518948958890135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55617891013535455561494773 5214177282518948958890135)
            ·
              refine ⟨7821265923778423438335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214177282518948958890135 7821265923778423438335203)
              ·
                refine ⟨11731898885667635157502805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7821265923778423438335203 11731898885667635157502805)
                ·
                  refine ⟨68741595033208799750993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11731898885667635157502805 68741595033208799750993)
                  ·
                    rfl

theorem cell23_1204864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_1204864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204864 prefixEnd_1204864 := by exact prefixLift 1204864
  have htrace : WordTrace (prefixWord ++ tailWord_1204864) baseStart_1204864 baseEnd_1204864 := by
    simpa [prefixWord, tailWord_1204864, baseEnd_1204864] using wordTrace_append hprefix tailTrace_1204864
  have hstable : (prefixWord ++ tailWord_1204864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204864).length < 2 ^ (prefixWord ++ tailWord_1204864).sum := by decide
  have hdescent : baseEnd_1204864 < baseStart_1204864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204892 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1204892 : Nat := 118140960795 + 1204892 * 2 ^ 59
def prefixEnd_1204892 : Nat := 4983230072969 + 3 ^ 40 * 1204892 * 2
def baseEnd_1204892 : Nat := 618688732757205088208809

theorem tailTrace_1204892 : CollatzResearch.WordTrace tailWord_1204892 prefixEnd_1204892 618688732757205088208809 := by
  unfold tailWord_1204892
  simp only [CollatzResearch.WordTrace]
  refine ⟨21973010775444769007896465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29297347700593025343861953 21973010775444769007896465)
  ·
    refine ⟨16479758081583576755922349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21973010775444769007896465 16479758081583576755922349)
    ·
      refine ⟨6179909280593841283470881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16479758081583576755922349 6179909280593841283470881)
      ·
        refine ⟨4634931960445380962603161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6179909280593841283470881 4634931960445380962603161)
        ·
          refine ⟨3476198970334035721952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4634931960445380962603161 3476198970334035721952371)
          ·
            refine ⟨5214298455501053582928557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476198970334035721952371 5214298455501053582928557)
            ·
              refine ⟨1955361920812895093598209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5214298455501053582928557 1955361920812895093598209)
              ·
                refine ⟨1466521440609671320198657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955361920812895093598209 1466521440609671320198657)
                ·
                  refine ⟨1099891080457253490148993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466521440609671320198657 1099891080457253490148993)
                  ·
                    refine ⟨824918310342940117611745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099891080457253490148993 824918310342940117611745)
                    ·
                      refine ⟨618688732757205088208809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824918310342940117611745 618688732757205088208809)
                      ·
                        rfl

theorem cell23_1204892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1204892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204892 prefixEnd_1204892 := by exact prefixLift 1204892
  have htrace : WordTrace (prefixWord ++ tailWord_1204892) baseStart_1204892 baseEnd_1204892 := by
    simpa [prefixWord, tailWord_1204892, baseEnd_1204892] using wordTrace_append hprefix tailTrace_1204892
  have hstable : (prefixWord ++ tailWord_1204892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204892).length < 2 ^ (prefixWord ++ tailWord_1204892).sum := by decide
  have hdescent : baseEnd_1204892 < baseStart_1204892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204909 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1204909 : Nat := 118140960795 + 1204909 * 2 ^ 59
def prefixEnd_1204909 : Nat := 4983230072969 + 3 ^ 40 * 1204909 * 2
def baseEnd_1204909 : Nat := 618697461928331521696231

theorem tailTrace_1204909 : CollatzResearch.WordTrace tailWord_1204909 prefixEnd_1204909 618697461928331521696231 := by
  unfold tailWord_1204909
  simp only [CollatzResearch.WordTrace]
  refine ⟨43946641591827949919161781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29297761061218633279441187 43946641591827949919161781)
  ·
    refine ⟨4119997649233870304921417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43946641591827949919161781 4119997649233870304921417)
    ·
      refine ⟨3089998236925402728691063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119997649233870304921417 3089998236925402728691063)
      ·
        refine ⟨4634997355388104093036595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089998236925402728691063 4634997355388104093036595)
        ·
          refine ⟨6952496033082156139554893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634997355388104093036595 6952496033082156139554893)
          ·
            refine ⟨2607186012405808552333085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6952496033082156139554893 2607186012405808552333085)
            ·
              refine ⟨977694754652178207124907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607186012405808552333085 977694754652178207124907)
              ·
                refine ⟨1466542131978267310687361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977694754652178207124907 1466542131978267310687361)
                ·
                  refine ⟨1099906598983700483015521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466542131978267310687361 1099906598983700483015521)
                  ·
                    refine ⟨824929949237775362261641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099906598983700483015521 824929949237775362261641)
                    ·
                      refine ⟨618697461928331521696231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 824929949237775362261641 618697461928331521696231)
                      ·
                        rfl

theorem cell23_1204909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1204909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1204909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1204909 prefixEnd_1204909 := by exact prefixLift 1204909
  have htrace : WordTrace (prefixWord ++ tailWord_1204909) baseStart_1204909 baseEnd_1204909 := by
    simpa [prefixWord, tailWord_1204909, baseEnd_1204909] using wordTrace_append hprefix tailTrace_1204909
  have hstable : (prefixWord ++ tailWord_1204909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204909).length < 2 ^ (prefixWord ++ tailWord_1204909).sum := by decide
  have hdescent : baseEnd_1204909 < baseStart_1204909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205048 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_1205048 : Nat := 118140960795 + 1205048 * 2 ^ 59
def prefixEnd_1205048 : Nat := 4983230072969 + 3 ^ 40 * 1205048 * 2
def baseEnd_1205048 : Nat := 206256278579768825952697

theorem tailTrace_1205048 : CollatzResearch.WordTrace tailWord_1205048 prefixEnd_1205048 206256278579768825952697 := by
  unfold tailWord_1205048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21975855669162188329235899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29301140892216251105647865 21975855669162188329235899)
  ·
    refine ⟨32963783503743282493853849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21975855669162188329235899 32963783503743282493853849)
    ·
      refine ⟨24722837627807461870390387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32963783503743282493853849 24722837627807461870390387)
      ·
        refine ⟨37084256441711192805585581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24722837627807461870390387 37084256441711192805585581)
        ·
          refine ⟨13906596165641697302094593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37084256441711192805585581 13906596165641697302094593)
          ·
            refine ⟨10429947124231272976570945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13906596165641697302094593 10429947124231272976570945)
            ·
              refine ⟨7822460343173454732428209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10429947124231272976570945 7822460343173454732428209)
              ·
                refine ⟨5866845257380091049321157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7822460343173454732428209 5866845257380091049321157)
                ·
                  refine ⟨1100033485758767071747717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5866845257380091049321157 1100033485758767071747717)
                  ·
                    refine ⟨206256278579768825952697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100033485758767071747717 206256278579768825952697)
                    ·
                      rfl

theorem cell23_1205048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_1205048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205048 prefixEnd_1205048 := by exact prefixLift 1205048
  have htrace : WordTrace (prefixWord ++ tailWord_1205048) baseStart_1205048 baseEnd_1205048 := by
    simpa [prefixWord, tailWord_1205048, baseEnd_1205048] using wordTrace_append hprefix tailTrace_1205048
  have hstable : (prefixWord ++ tailWord_1205048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205048).length < 2 ^ (prefixWord ++ tailWord_1205048).sum := by decide
  have hdescent : baseEnd_1205048 < baseStart_1205048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205055 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_1205055 : Nat := 118140960795 + 1205055 * 2 ^ 59
def prefixEnd_1205055 : Nat := 4983230072969 + 3 ^ 40 * 1205055 * 2
def baseEnd_1205055 : Nat := 618772430103887950470559

theorem tailTrace_1205055 : CollatzResearch.WordTrace tailWord_1205055 prefixEnd_1205055 618772430103887950470559 := by
  unfold tailWord_1205055
  simp only [CollatzResearch.WordTrace]
  refine ⟨43951966649299016853976619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29301311099532677902651079 43951966649299016853976619)
  ·
    refine ⟨65927949973948525280964929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43951966649299016853976619 65927949973948525280964929)
    ·
      refine ⟨49445962480461393960723697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65927949973948525280964929 49445962480461393960723697)
      ·
        refine ⟨37084471860346045470542773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49445962480461393960723697 37084471860346045470542773)
        ·
          refine ⟨3476669236907441762863385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37084471860346045470542773 3476669236907441762863385)
          ·
            refine ⟨2607501927680581322147539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3476669236907441762863385 2607501927680581322147539)
            ·
              refine ⟨3911252891520871983221309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607501927680581322147539 3911252891520871983221309)
              ·
                refine ⟨1466719834320326993707991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911252891520871983221309 1466719834320326993707991)
                ·
                  refine ⟨2200079751480490490561987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466719834320326993707991 2200079751480490490561987)
                  ·
                    refine ⟨3300119627220735735842981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200079751480490490561987 3300119627220735735842981)
                    ·
                      refine ⟨618772430103887950470559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3300119627220735735842981 618772430103887950470559)
                      ·
                        rfl

theorem cell23_1205055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_1205055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205055 prefixEnd_1205055 := by exact prefixLift 1205055
  have htrace : WordTrace (prefixWord ++ tailWord_1205055) baseStart_1205055 baseEnd_1205055 := by
    simpa [prefixWord, tailWord_1205055, baseEnd_1205055] using wordTrace_append hprefix tailTrace_1205055
  have hstable : (prefixWord ++ tailWord_1205055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205055).length < 2 ^ (prefixWord ++ tailWord_1205055).sum := by decide
  have hdescent : baseEnd_1205055 < baseStart_1205055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205065 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 2, 4]
def baseStart_1205065 : Nat := 118140960795 + 1205065 * 2 ^ 59
def prefixEnd_1205065 : Nat := 4983230072969 + 3 ^ 40 * 1205065 * 2
def baseEnd_1205065 : Nat := 206259188303477637115171

theorem tailTrace_1205065 : CollatzResearch.WordTrace tailWord_1205065 prefixEnd_1205065 206259188303477637115171 := by
  unfold tailWord_1205065
  simp only [CollatzResearch.WordTrace]
  refine ⟨43952331379262788561840649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29301554252841859041227099 43952331379262788561840649)
  ·
    refine ⟨32964248534447091421380487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43952331379262788561840649 32964248534447091421380487)
    ·
      refine ⟨49446372801670637132070731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32964248534447091421380487 49446372801670637132070731)
      ·
        refine ⟨74169559202505955698106097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49446372801670637132070731 74169559202505955698106097)
        ·
          refine ⟨55627169401879466773579573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74169559202505955698106097 55627169401879466773579573)
          ·
            refine ⟨5215047131426200010023085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55627169401879466773579573 5215047131426200010023085)
            ·
              refine ⟨1955642674284825003758657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5215047131426200010023085 1955642674284825003758657)
              ·
                refine ⟨1466732005713618752818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955642674284825003758657 1466732005713618752818993)
                ·
                  refine ⟨1100049004285214064614245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466732005713618752818993 1100049004285214064614245)
                  ·
                    refine ⟨206259188303477637115171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100049004285214064614245 206259188303477637115171)
                    ·
                      rfl

theorem cell23_1205065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 4].length) (baseStart_1205065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205065 prefixEnd_1205065 := by exact prefixLift 1205065
  have htrace : WordTrace (prefixWord ++ tailWord_1205065) baseStart_1205065 baseEnd_1205065 := by
    simpa [prefixWord, tailWord_1205065, baseEnd_1205065] using wordTrace_append hprefix tailTrace_1205065
  have hstable : (prefixWord ++ tailWord_1205065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205065).length < 2 ^ (prefixWord ++ tailWord_1205065).sum := by decide
  have hdescent : baseEnd_1205065 < baseStart_1205065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205082 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_1205082 : Nat := 118140960795 + 1205082 * 2 ^ 59
def prefixEnd_1205082 : Nat := 4983230072969 + 3 ^ 40 * 1205082 * 2
def baseEnd_1205082 : Nat := 206262098027186448277645

theorem tailTrace_1205082 : CollatzResearch.WordTrace tailWord_1205082 prefixEnd_1205082 206262098027186448277645 := by
  unfold tailWord_1205082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988237855050300116302375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29301967613467466976806333 10988237855050300116302375)
  ·
    refine ⟨16482356782575450174453563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10988237855050300116302375 16482356782575450174453563)
    ·
      refine ⟨24723535173863175261680345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16482356782575450174453563 24723535173863175261680345)
      ·
        refine ⟨18542651380397381446260259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24723535173863175261680345 18542651380397381446260259)
        ·
          refine ⟨27813977070596072169390389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18542651380397381446260259 27813977070596072169390389)
          ·
            refine ⟨2607560350368381765880349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27813977070596072169390389 2607560350368381765880349)
            ·
              refine ⟨977835131388143162205131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607560350368381765880349 977835131388143162205131)
              ·
                refine ⟨1466752697082214743307697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977835131388143162205131 1466752697082214743307697)
                ·
                  refine ⟨1100064522811661057480773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1466752697082214743307697 1100064522811661057480773)
                  ·
                    refine ⟨206262098027186448277645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100064522811661057480773 206262098027186448277645)
                    ·
                      rfl

theorem cell23_1205082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_1205082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205082 prefixEnd_1205082 := by exact prefixLift 1205082
  have htrace : WordTrace (prefixWord ++ tailWord_1205082) baseStart_1205082 baseEnd_1205082 := by
    simpa [prefixWord, tailWord_1205082, baseEnd_1205082] using wordTrace_append hprefix tailTrace_1205082
  have hstable : (prefixWord ++ tailWord_1205082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205082).length < 2 ^ (prefixWord ++ tailWord_1205082).sum := by decide
  have hdescent : baseEnd_1205082 < baseStart_1205082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205092 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_1205092 : Nat := 118140960795 + 1205092 * 2 ^ 59
def prefixEnd_1205092 : Nat := 4983230072969 + 3 ^ 40 * 1205092 * 2
def baseEnd_1205092 : Nat := 618791428888104305707889

theorem tailTrace_1205092 : CollatzResearch.WordTrace tailWord_1205092 prefixEnd_1205092 618791428888104305707889 := by
  unfold tailWord_1205092
  simp only [CollatzResearch.WordTrace]
  refine ⟨21976658075082486086536765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29302210766776648115382353 21976658075082486086536765)
  ·
    refine ⟨8241246778155932282451287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21976658075082486086536765 8241246778155932282451287)
    ·
      refine ⟨12361870167233898423676931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8241246778155932282451287 12361870167233898423676931)
      ·
        refine ⟨18542805250850847635515397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12361870167233898423676931 18542805250850847635515397)
        ·
          refine ⟨3476775984534533931659137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18542805250850847635515397 3476775984534533931659137)
          ·
            refine ⟨2607581988400900448744353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3476775984534533931659137 2607581988400900448744353)
            ·
              refine ⟨1955686491300675336558265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607581988400900448744353 1955686491300675336558265)
              ·
                refine ⟨1466764868475506502418699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955686491300675336558265 1466764868475506502418699)
                ·
                  refine ⟨2200147302713259753628049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466764868475506502418699 2200147302713259753628049)
                  ·
                    refine ⟨1650110477034944815221037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200147302713259753628049 1650110477034944815221037)
                    ·
                      refine ⟨618791428888104305707889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650110477034944815221037 618791428888104305707889)
                      ·
                        rfl

theorem cell23_1205092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_1205092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205092 prefixEnd_1205092 := by exact prefixLift 1205092
  have htrace : WordTrace (prefixWord ++ tailWord_1205092) baseStart_1205092 baseEnd_1205092 := by
    simpa [prefixWord, tailWord_1205092, baseEnd_1205092] using wordTrace_append hprefix tailTrace_1205092
  have hstable : (prefixWord ++ tailWord_1205092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205092).length < 2 ^ (prefixWord ++ tailWord_1205092).sum := by decide
  have hdescent : baseEnd_1205092 < baseStart_1205092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205095 : List Nat := [1, 1, 5, 1, 2, 4, 2, 7]
def baseStart_1205095 : Nat := 118140960795 + 1205095 * 2 ^ 59
def prefixEnd_1205095 : Nat := 4983230072969 + 3 ^ 40 * 1205095 * 2
def baseEnd_1205095 : Nat := 22918258123335844221125

theorem tailTrace_1205095 : CollatzResearch.WordTrace tailWord_1205095 prefixEnd_1205095 22918258123335844221125 := by
  unfold tailWord_1205095
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953425569154103685432739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29302283712769402456955159 43953425569154103685432739)
  ·
    refine ⟨65930138353731155528149109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43953425569154103685432739 65930138353731155528149109)
    ·
      refine ⟨6180950470662295830763979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65930138353731155528149109 6180950470662295830763979)
      ·
        refine ⟨9271425705993443746145969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180950470662295830763979 9271425705993443746145969)
        ·
          refine ⟨6953569279495082809609477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9271425705993443746145969 6953569279495082809609477)
          ·
            refine ⟨1303794239905328026801777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6953569279495082809609477 1303794239905328026801777)
            ·
              refine ⟨977845679928996020101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303794239905328026801777 977845679928996020101333)
              ·
                refine ⟨22918258123335844221125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 977845679928996020101333 22918258123335844221125)
                ·
                  rfl

theorem cell23_1205095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 7].length) (baseStart_1205095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205095 prefixEnd_1205095 := by exact prefixLift 1205095
  have htrace : WordTrace (prefixWord ++ tailWord_1205095) baseStart_1205095 baseEnd_1205095 := by
    simpa [prefixWord, tailWord_1205095, baseEnd_1205095] using wordTrace_append hprefix tailTrace_1205095
  have hstable : (prefixWord ++ tailWord_1205095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205095).length < 2 ^ (prefixWord ++ tailWord_1205095).sum := by decide
  have hdescent : baseEnd_1205095 < baseStart_1205095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205105 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_1205105 : Nat := 118140960795 + 1205105 * 2 ^ 59
def prefixEnd_1205105 : Nat := 4983230072969 + 3 ^ 40 * 1205105 * 2
def baseEnd_1205105 : Nat := 618798104136612754845329

theorem tailTrace_1205105 : CollatzResearch.WordTrace tailWord_1205105 prefixEnd_1205105 618798104136612754845329 := by
  unfold tailWord_1205105
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953790299117875393296769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29302526866078583595531179 43953790299117875393296769)
  ·
    refine ⟨32965342724338406544972577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43953790299117875393296769 32965342724338406544972577)
    ·
      refine ⟨24724007043253804908729433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32965342724338406544972577 24724007043253804908729433)
      ·
        refine ⟨18543005282440353681547075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24724007043253804908729433 18543005282440353681547075)
        ·
          refine ⟨27814507923660530522320613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18543005282440353681547075 27814507923660530522320613)
          ·
            refine ⟨5215220235686349472935115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27814507923660530522320613 5215220235686349472935115)
            ·
              refine ⟨7822830353529524209402673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5215220235686349472935115 7822830353529524209402673)
              ·
                refine ⟨5867122765147143157052005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7822830353529524209402673 5867122765147143157052005)
                ·
                  refine ⟨1100085518465089341947251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5867122765147143157052005 1100085518465089341947251)
                  ·
                    refine ⟨1650128277697634012920877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100085518465089341947251 1650128277697634012920877)
                    ·
                      refine ⟨618798104136612754845329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650128277697634012920877 618798104136612754845329)
                      ·
                        rfl

theorem cell23_1205105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_1205105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205105 prefixEnd_1205105 := by exact prefixLift 1205105
  have htrace : WordTrace (prefixWord ++ tailWord_1205105) baseStart_1205105 baseEnd_1205105 := by
    simpa [prefixWord, tailWord_1205105, baseEnd_1205105] using wordTrace_append hprefix tailTrace_1205105
  have hstable : (prefixWord ++ tailWord_1205105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205105).length < 2 ^ (prefixWord ++ tailWord_1205105).sum := by decide
  have hdescent : baseEnd_1205105 < baseStart_1205105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205111 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1205111 : Nat := 118140960795 + 1205111 * 2 ^ 59
def prefixEnd_1205111 : Nat := 4983230072969 + 3 ^ 40 * 1205111 * 2
def baseEnd_1205111 : Nat := 618801185020539731370301

theorem tailTrace_1205111 : CollatzResearch.WordTrace tailWord_1205111 prefixEnd_1205111 618801185020539731370301 := by
  unfold tailWord_1205111
  simp only [CollatzResearch.WordTrace]
  refine ⟨43954009137096138418015187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29302672758064092278676791 43954009137096138418015187)
  ·
    refine ⟨65931013705644207627022781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43954009137096138418015187 65931013705644207627022781)
    ·
      refine ⟨24724130139616577860133543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65931013705644207627022781 24724130139616577860133543)
      ·
        refine ⟨37086195209424866790200315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24724130139616577860133543 37086195209424866790200315)
        ·
          refine ⟨55629292814137300185300473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37086195209424866790200315 55629292814137300185300473)
          ·
            refine ⟨41721969610602975138975355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55629292814137300185300473 41721969610602975138975355)
            ·
              refine ⟨62582954415904462708463033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41721969610602975138975355 62582954415904462708463033)
              ·
                refine ⟨46937215811928347031347275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62582954415904462708463033 46937215811928347031347275)
                ·
                  refine ⟨70405823717892520547020913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46937215811928347031347275 70405823717892520547020913)
                  ·
                    refine ⟨52804367788419390410265685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70405823717892520547020913 52804367788419390410265685)
                    ·
                      refine ⟨618801185020539731370301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52804367788419390410265685 618801185020539731370301)
                      ·
                        rfl

theorem cell23_1205111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1205111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205111 prefixEnd_1205111 := by exact prefixLift 1205111
  have htrace : WordTrace (prefixWord ++ tailWord_1205111) baseStart_1205111 baseEnd_1205111 := by
    simpa [prefixWord, tailWord_1205111, baseEnd_1205111] using wordTrace_append hprefix tailTrace_1205111
  have hstable : (prefixWord ++ tailWord_1205111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205111).length < 2 ^ (prefixWord ++ tailWord_1205111).sum := by decide
  have hdescent : baseEnd_1205111 < baseStart_1205111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205145 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 4, 2]
def baseStart_1205145 : Nat := 118140960795 + 1205145 * 2 ^ 59
def prefixEnd_1205145 : Nat := 4983230072969 + 3 ^ 40 * 1205145 * 2
def baseEnd_1205145 : Nat := 618818643362792598345145

theorem tailTrace_1205145 : CollatzResearch.WordTrace tailWord_1205145 prefixEnd_1205145 618818643362792598345145 := by
  unfold tailWord_1205145
  simp only [CollatzResearch.WordTrace]
  refine ⟨43955249218972962224752889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29303499479315308149835259 43955249218972962224752889)
  ·
    refine ⟨32966436914229721668564667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43955249218972962224752889 32966436914229721668564667)
    ·
      refine ⟨49449655371344582502847001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32966436914229721668564667 49449655371344582502847001)
      ·
        refine ⟨37087241528508436877135251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49449655371344582502847001 37087241528508436877135251)
        ·
          refine ⟨55630862292762655315702877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37087241528508436877135251 55630862292762655315702877)
          ·
            refine ⟨20861573359785995743388579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55630862292762655315702877 20861573359785995743388579)
            ·
              refine ⟨31292360039678993615082869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20861573359785995743388579 31292360039678993615082869)
              ·
                refine ⟨2933658753719905651414019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31292360039678993615082869 2933658753719905651414019)
                ·
                  refine ⟨4400488130579858477121029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933658753719905651414019 4400488130579858477121029)
                  ·
                    refine ⟨825091524483723464460193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4400488130579858477121029 825091524483723464460193)
                    ·
                      refine ⟨618818643362792598345145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825091524483723464460193 618818643362792598345145)
                      ·
                        rfl

theorem cell23_1205145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_1205145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205145 prefixEnd_1205145 := by exact prefixLift 1205145
  have htrace : WordTrace (prefixWord ++ tailWord_1205145) baseStart_1205145 baseEnd_1205145 := by
    simpa [prefixWord, tailWord_1205145, baseEnd_1205145] using wordTrace_append hprefix tailTrace_1205145
  have hstable : (prefixWord ++ tailWord_1205145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205145).length < 2 ^ (prefixWord ++ tailWord_1205145).sum := by decide
  have hdescent : baseEnd_1205145 < baseStart_1205145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205174 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1205174 : Nat := 118140960795 + 1205174 * 2 ^ 59
def prefixEnd_1205174 : Nat := 4983230072969 + 3 ^ 40 * 1205174 * 2
def baseEnd_1205174 : Nat := 618833534301772984882513

theorem tailTrace_1205174 : CollatzResearch.WordTrace tailWord_1205174 prefixEnd_1205174 618833534301772984882513 := by
  unfold tailWord_1205174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747269183491743761097411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29304204623911933451705717 2747269183491743761097411)
  ·
    refine ⟨4120903775237615641646117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747269183491743761097411 4120903775237615641646117)
    ·
      refine ⟨772669457857052932808647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4120903775237615641646117 772669457857052932808647)
      ·
        refine ⟨1159004186785579399212971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772669457857052932808647 1159004186785579399212971)
        ·
          refine ⟨1738506280178369098819457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159004186785579399212971 1738506280178369098819457)
          ·
            refine ⟨1303879710133776824114593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738506280178369098819457 1303879710133776824114593)
            ·
              refine ⟨977909782600332618085945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303879710133776824114593 977909782600332618085945)
              ·
                refine ⟨733432336950249463564459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977909782600332618085945 733432336950249463564459)
                ·
                  refine ⟨1100148505425374195346689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733432336950249463564459 1100148505425374195346689)
                  ·
                    refine ⟨825111379069030646510017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100148505425374195346689 825111379069030646510017)
                    ·
                      refine ⟨618833534301772984882513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825111379069030646510017 618833534301772984882513)
                      ·
                        rfl

theorem cell23_1205174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1205174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205174 prefixEnd_1205174 := by exact prefixLift 1205174
  have htrace : WordTrace (prefixWord ++ tailWord_1205174) baseStart_1205174 baseEnd_1205174 := by
    simpa [prefixWord, tailWord_1205174, baseEnd_1205174] using wordTrace_append hprefix tailTrace_1205174
  have hstable : (prefixWord ++ tailWord_1205174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205174).length < 2 ^ (prefixWord ++ tailWord_1205174).sum := by decide
  have hdescent : baseEnd_1205174 < baseStart_1205174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205195 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3]
def baseStart_1205195 : Nat := 118140960795 + 1205195 * 2 ^ 59
def prefixEnd_1205195 : Nat := 4983230072969 + 3 ^ 40 * 1205195 * 2
def baseEnd_1205195 : Nat := 618844317395517402719915

theorem tailTrace_1205195 : CollatzResearch.WordTrace tailWord_1205195 prefixEnd_1205195 618844317395517402719915 := by
  unfold tailWord_1205195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43957072868791820764073039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29304715245861213842715359 43957072868791820764073039)
  ·
    refine ⟨65935609303187731146109559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43957072868791820764073039 65935609303187731146109559)
    ·
      refine ⟨98903413954781596719164339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65935609303187731146109559 98903413954781596719164339)
      ·
        refine ⟨148355120932172395078746509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98903413954781596719164339 148355120932172395078746509)
        ·
          refine ⟨55633170349564648154529941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148355120932172395078746509 55633170349564648154529941)
          ·
            refine ⟨2607804860135842882243591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55633170349564648154529941 2607804860135842882243591)
            ·
              refine ⟨3911707290203764323365387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607804860135842882243591 3911707290203764323365387)
              ·
                refine ⟨5867560935305646485048081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911707290203764323365387 5867560935305646485048081)
                ·
                  refine ⟨4400670701479234863786061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5867560935305646485048081 4400670701479234863786061)
                  ·
                    refine ⟨1650251513054713073919773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4400670701479234863786061 1650251513054713073919773)
                    ·
                      refine ⟨618844317395517402719915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650251513054713073919773 618844317395517402719915)
                      ·
                        rfl

theorem cell23_1205195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 3].length) (baseStart_1205195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205195 prefixEnd_1205195 := by exact prefixLift 1205195
  have htrace : WordTrace (prefixWord ++ tailWord_1205195) baseStart_1205195 baseEnd_1205195 := by
    simpa [prefixWord, tailWord_1205195, baseEnd_1205195] using wordTrace_append hprefix tailTrace_1205195
  have hstable : (prefixWord ++ tailWord_1205195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205195).length < 2 ^ (prefixWord ++ tailWord_1205195).sum := by decide
  have hdescent : baseEnd_1205195 < baseStart_1205195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205215 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 7]
def baseStart_1205215 : Nat := 118140960795 + 1205215 * 2 ^ 59
def prefixEnd_1205215 : Nat := 4983230072969 + 3 ^ 40 * 1205215 * 2
def baseEnd_1205215 : Nat := 206284862336202441489941

theorem tailTrace_1205215 : CollatzResearch.WordTrace tailWord_1205215 prefixEnd_1205215 206284862336202441489941 := by
  unfold tailWord_1205215
  simp only [CollatzResearch.WordTrace]
  refine ⟨43957802328719364179801099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29305201552479576119867399 43957802328719364179801099)
  ·
    refine ⟨65936703493079046269701649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43957802328719364179801099 65936703493079046269701649)
    ·
      refine ⟨49452527619809284702276237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65936703493079046269701649 49452527619809284702276237)
      ·
        refine ⟨18544697857428481763353589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49452527619809284702276237 18544697857428481763353589)
        ·
          refine ⟨1738565424133920165314399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18544697857428481763353589 1738565424133920165314399)
          ·
            refine ⟨2607848136200880247971599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738565424133920165314399 2607848136200880247971599)
            ·
              refine ⟨3911772204301320371957399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607848136200880247971599 3911772204301320371957399)
              ·
                refine ⟨5867658306451980557936099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911772204301320371957399 5867658306451980557936099)
                ·
                  refine ⟨8801487459677970836904149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867658306451980557936099 8801487459677970836904149)
                  ·
                    refine ⟨206284862336202441489941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8801487459677970836904149 206284862336202441489941)
                    ·
                      rfl

theorem cell23_1205215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_1205215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205215 prefixEnd_1205215 := by exact prefixLift 1205215
  have htrace : WordTrace (prefixWord ++ tailWord_1205215) baseStart_1205215 baseEnd_1205215 := by
    simpa [prefixWord, tailWord_1205215, baseEnd_1205215] using wordTrace_append hprefix tailTrace_1205215
  have hstable : (prefixWord ++ tailWord_1205215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205215).length < 2 ^ (prefixWord ++ tailWord_1205215).sum := by decide
  have hdescent : baseEnd_1205215 < baseStart_1205215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205255 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1205255 : Nat := 118140960795 + 1205255 * 2 ^ 59
def prefixEnd_1205255 : Nat := 4983230072969 + 3 ^ 40 * 1205255 * 2
def baseEnd_1205255 : Nat := 618875126234787167969639

theorem tailTrace_1205255 : CollatzResearch.WordTrace tailWord_1205255 prefixEnd_1205255 618875126234787167969639 := by
  unfold tailWord_1205255
  simp only [CollatzResearch.WordTrace]
  refine ⟨43959261248574451011257219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29306174165716300674171479 43959261248574451011257219)
  ·
    refine ⟨65938891872861676516885829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43959261248574451011257219 65938891872861676516885829)
    ·
      refine ⟨12363542226161564346916093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65938891872861676516885829 12363542226161564346916093)
      ·
        refine ⟨4636328334810586630093535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12363542226161564346916093 4636328334810586630093535)
        ·
          refine ⟨6954492502215879945140303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636328334810586630093535 6954492502215879945140303)
          ·
            refine ⟨10431738753323819917710455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954492502215879945140303 10431738753323819917710455)
            ·
              refine ⟨15647608129985729876565683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10431738753323819917710455 15647608129985729876565683)
              ·
                refine ⟨23471412194978594814848525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15647608129985729876565683 23471412194978594814848525)
                ·
                  refine ⟨8801779573116973055568197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23471412194978594814848525 8801779573116973055568197)
                  ·
                    refine ⟨1650333669959432447919037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8801779573116973055568197 1650333669959432447919037)
                    ·
                      refine ⟨618875126234787167969639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650333669959432447919037 618875126234787167969639)
                      ·
                        rfl

theorem cell23_1205255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1205255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205255 prefixEnd_1205255 := by exact prefixLift 1205255
  have htrace : WordTrace (prefixWord ++ tailWord_1205255) baseStart_1205255 baseEnd_1205255 := by
    simpa [prefixWord, tailWord_1205255, baseEnd_1205255] using wordTrace_append hprefix tailTrace_1205255
  have hstable : (prefixWord ++ tailWord_1205255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205255).length < 2 ^ (prefixWord ++ tailWord_1205255).sum := by decide
  have hdescent : baseEnd_1205255 < baseStart_1205255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205262 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_1205262 : Nat := 118140960795 + 1205262 * 2 ^ 59
def prefixEnd_1205262 : Nat := 4983230072969 + 3 ^ 40 * 1205262 * 2
def baseEnd_1205262 : Nat := 206292906866456213527369

theorem tailTrace_1205262 : CollatzResearch.WordTrace tailWord_1205262 prefixEnd_1205262 206292906866456213527369 := by
  unfold tailWord_1205262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494939569943636400845255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29306344373032727471174693 5494939569943636400845255)
  ·
    refine ⟨8242409354915454601267883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494939569943636400845255 8242409354915454601267883)
    ·
      refine ⟨12363614032373181901901825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242409354915454601267883 12363614032373181901901825)
      ·
        refine ⟨9272710524279886426426369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12363614032373181901901825 9272710524279886426426369)
        ·
          refine ⟨6954532893209914819819777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9272710524279886426426369 6954532893209914819819777)
          ·
            refine ⟨5215899669907436114864833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6954532893209914819819777 5215899669907436114864833)
            ·
              refine ⟨3911924752430577086148625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215899669907436114864833 3911924752430577086148625)
              ·
                refine ⟨2933943564322932814611469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911924752430577086148625 2933943564322932814611469)
                ·
                  refine ⟨1100228836621099805479301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2933943564322932814611469 1100228836621099805479301)
                  ·
                    refine ⟨206292906866456213527369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100228836621099805479301 206292906866456213527369)
                    ·
                      rfl

theorem cell23_1205262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_1205262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205262 prefixEnd_1205262 := by exact prefixLift 1205262
  have htrace : WordTrace (prefixWord ++ tailWord_1205262) baseStart_1205262 baseEnd_1205262 := by
    simpa [prefixWord, tailWord_1205262, baseEnd_1205262] using wordTrace_append hprefix tailTrace_1205262
  have hstable : (prefixWord ++ tailWord_1205262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205262).length < 2 ^ (prefixWord ++ tailWord_1205262).sum := by decide
  have hdescent : baseEnd_1205262 < baseStart_1205262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205279 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 1, 4]
def baseStart_1205279 : Nat := 118140960795 + 1205279 * 2 ^ 59
def prefixEnd_1205279 : Nat := 4983230072969 + 3 ^ 40 * 1205279 * 2
def baseEnd_1205279 : Nat := 206295816590165024689843

theorem tailTrace_1205279 : CollatzResearch.WordTrace tailWord_1205279 prefixEnd_1205279 206295816590165024689843 := by
  unfold tailWord_1205279
  simp only [CollatzResearch.WordTrace]
  refine ⟨43960136600487503110130891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29306757733658335406753927 43960136600487503110130891)
  ·
    refine ⟨65940204900731254665196337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43960136600487503110130891 65940204900731254665196337)
    ·
      refine ⟨49455153675548440998897253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65940204900731254665196337 49455153675548440998897253)
      ·
        refine ⟨9272841314165332687293235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49455153675548440998897253 9272841314165332687293235)
        ·
          refine ⟨13909261971247999030939853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272841314165332687293235 13909261971247999030939853)
          ·
            refine ⟨5215973239217999636602445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13909261971247999030939853 5215973239217999636602445)
            ·
              refine ⟨1955989964706749863725917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5215973239217999636602445 1955989964706749863725917)
              ·
                refine ⟨733496236765031198897219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955989964706749863725917 733496236765031198897219)
                ·
                  refine ⟨1100244355147546798345829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733496236765031198897219 1100244355147546798345829)
                  ·
                    refine ⟨206295816590165024689843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1100244355147546798345829 206295816590165024689843)
                    ·
                      rfl

theorem cell23_1205279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_1205279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205279 prefixEnd_1205279 := by exact prefixLift 1205279
  have htrace : WordTrace (prefixWord ++ tailWord_1205279) baseStart_1205279 baseEnd_1205279 := by
    simpa [prefixWord, tailWord_1205279, baseEnd_1205279] using wordTrace_append hprefix tailTrace_1205279
  have hstable : (prefixWord ++ tailWord_1205279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205279).length < 2 ^ (prefixWord ++ tailWord_1205279).sum := by decide
  have hdescent : baseEnd_1205279 < baseStart_1205279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205309 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1205309 : Nat := 118140960795 + 1205309 * 2 ^ 59
def prefixEnd_1205309 : Nat := 4983230072969 + 3 ^ 40 * 1205309 * 2
def baseEnd_1205309 : Nat := 68766983798903328521599

theorem tailTrace_1205309 : CollatzResearch.WordTrace tailWord_1205309 prefixEnd_1205309 68766983798903328521599 := by
  unfold tailWord_1205309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961230790378818233722981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29307487193585878822481987 43961230790378818233722981)
  ·
    refine ⟨8242730773196028418823059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43961230790378818233722981 8242730773196028418823059)
    ·
      refine ⟨12364096159794042628234589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242730773196028418823059 12364096159794042628234589)
      ·
        refine ⟨4636536059922765985587971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12364096159794042628234589 4636536059922765985587971)
        ·
          refine ⟨6954804089884148978381957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636536059922765985587971 6954804089884148978381957)
          ·
            refine ⟨1304025766853277933446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6954804089884148978381957 1304025766853277933446617)
            ·
              refine ⟨978019325139958450084963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304025766853277933446617 978019325139958450084963)
              ·
                refine ⟨1467028987709937675127445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978019325139958450084963 1467028987709937675127445)
                ·
                  refine ⟨68766983798903328521599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1467028987709937675127445 68766983798903328521599)
                  ·
                    rfl

theorem cell23_1205309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1205309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205309 prefixEnd_1205309 := by exact prefixLift 1205309
  have htrace : WordTrace (prefixWord ++ tailWord_1205309) baseStart_1205309 baseEnd_1205309 := by
    simpa [prefixWord, tailWord_1205309, baseEnd_1205309] using wordTrace_append hprefix tailTrace_1205309
  have hstable : (prefixWord ++ tailWord_1205309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205309).length < 2 ^ (prefixWord ++ tailWord_1205309).sum := by decide
  have hdescent : baseEnd_1205309 < baseStart_1205309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205312 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2]
def baseStart_1205312 : Nat := 118140960795 + 1205312 * 2 ^ 59
def prefixEnd_1205312 : Nat := 4983230072969 + 3 ^ 40 * 1205312 * 2
def baseEnd_1205312 : Nat := 618904394632093444956877

theorem tailTrace_1205312 : CollatzResearch.WordTrace tailWord_1205312 prefixEnd_1205312 618904394632093444956877 := by
  unfold tailWord_1205312
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980670104683974873041095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29307560139578633164054793 21980670104683974873041095)
  ·
    refine ⟨32971005157025962309561643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21980670104683974873041095 32971005157025962309561643)
    ·
      refine ⟨49456507735538943464342465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32971005157025962309561643 49456507735538943464342465)
      ·
        refine ⟨37092380801654207598256849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49456507735538943464342465 37092380801654207598256849)
        ·
          refine ⟨27819285601240655698692637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37092380801654207598256849 27819285601240655698692637)
          ·
            refine ⟨10432232100465245887009739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27819285601240655698692637 10432232100465245887009739)
            ·
              refine ⟨15648348150697868830514609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432232100465245887009739 15648348150697868830514609)
              ·
                refine ⟨11736261113023401622885957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15648348150697868830514609 11736261113023401622885957)
                ·
                  refine ⟨2200548958691887804291117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11736261113023401622885957 2200548958691887804291117)
                  ·
                    refine ⟨825205859509457926609169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200548958691887804291117 825205859509457926609169)
                    ·
                      refine ⟨618904394632093444956877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825205859509457926609169 618904394632093444956877)
                      ·
                        rfl

theorem cell23_1205312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_1205312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205312 prefixEnd_1205312 := by exact prefixLift 1205312
  have htrace : WordTrace (prefixWord ++ tailWord_1205312) baseStart_1205312 baseEnd_1205312 := by
    simpa [prefixWord, tailWord_1205312, baseEnd_1205312] using wordTrace_append hprefix tailTrace_1205312
  have hstable : (prefixWord ++ tailWord_1205312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205312).length < 2 ^ (prefixWord ++ tailWord_1205312).sum := by decide
  have hdescent : baseEnd_1205312 < baseStart_1205312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205322 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1205322 : Nat := 118140960795 + 1205322 * 2 ^ 59
def prefixEnd_1205322 : Nat := 4983230072969 + 3 ^ 40 * 1205322 * 2
def baseEnd_1205322 : Nat := 206303176479546135277277

theorem tailTrace_1205322 : CollatzResearch.WordTrace tailWord_1205322 prefixEnd_1205322 206303176479546135277277 := by
  unfold tailWord_1205322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990426234832930363486555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29307803292887814302630813 10990426234832930363486555)
  ·
    refine ⟨16485639352249395545229833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10990426234832930363486555 16485639352249395545229833)
    ·
      refine ⟨12364229514187046658922375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16485639352249395545229833 12364229514187046658922375)
      ·
        refine ⟨18546344271280569988383563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12364229514187046658922375 18546344271280569988383563)
        ·
          refine ⟨27819516406920854982575345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18546344271280569988383563 27819516406920854982575345)
          ·
            refine ⟨20864637305190641236931509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27819516406920854982575345 20864637305190641236931509)
            ·
              refine ⟨1956059747361622615962329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20864637305190641236931509 1956059747361622615962329)
              ·
                refine ⟨1467044810521216961971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956059747361622615962329 1467044810521216961971747)
                ·
                  refine ⟨2200567215781825442957621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467044810521216961971747 2200567215781825442957621)
                  ·
                    refine ⟨206303176479546135277277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2200567215781825442957621 206303176479546135277277)
                    ·
                      rfl

theorem cell23_1205322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1205322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205322 prefixEnd_1205322 := by exact prefixLift 1205322
  have htrace : WordTrace (prefixWord ++ tailWord_1205322) baseStart_1205322 baseEnd_1205322 := by
    simpa [prefixWord, tailWord_1205322, baseEnd_1205322] using wordTrace_append hprefix tailTrace_1205322
  have hstable : (prefixWord ++ tailWord_1205322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205322).length < 2 ^ (prefixWord ++ tailWord_1205322).sum := by decide
  have hdescent : baseEnd_1205322 < baseStart_1205322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205346 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_1205346 : Nat := 118140960795 + 1205346 * 2 ^ 59
def prefixEnd_1205346 : Nat := 4983230072969 + 3 ^ 40 * 1205346 * 2
def baseEnd_1205346 : Nat := 618921852974346311931721

theorem tailTrace_1205346 : CollatzResearch.WordTrace tailWord_1205346 prefixEnd_1205346 618921852974346311931721 := by
  unfold tailWord_1205346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990645072811193388204973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29308386860829849035213261 10990645072811193388204973)
  ·
    refine ⟨4121491902304197520576865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10990645072811193388204973 4121491902304197520576865)
    ·
      refine ⟨3091118926728148140432649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4121491902304197520576865 3091118926728148140432649)
      ·
        refine ⟨2318339195046111105324487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3091118926728148140432649 2318339195046111105324487)
        ·
          refine ⟨3477508792569166657986731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318339195046111105324487 3477508792569166657986731)
          ·
            refine ⟨5216263188853749986980097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477508792569166657986731 5216263188853749986980097)
            ·
              refine ⟨3912197391640312490235073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216263188853749986980097 3912197391640312490235073)
              ·
                refine ⟨2934148043730234367676305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912197391640312490235073 2934148043730234367676305)
                ·
                  refine ⟨2200611032797675775757229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934148043730234367676305 2200611032797675775757229)
                  ·
                    refine ⟨825229137299128415908961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200611032797675775757229 825229137299128415908961)
                    ·
                      refine ⟨618921852974346311931721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825229137299128415908961 618921852974346311931721)
                      ·
                        rfl

theorem cell23_1205346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_1205346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205346 prefixEnd_1205346 := by exact prefixLift 1205346
  have htrace : WordTrace (prefixWord ++ tailWord_1205346) baseStart_1205346 baseEnd_1205346 := by
    simpa [prefixWord, tailWord_1205346, baseEnd_1205346] using wordTrace_append hprefix tailTrace_1205346
  have hstable : (prefixWord ++ tailWord_1205346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205346).length < 2 ^ (prefixWord ++ tailWord_1205346).sum := by decide
  have hdescent : baseEnd_1205346 < baseStart_1205346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205353 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 1, 1, 3]
def baseStart_1205353 : Nat := 118140960795 + 1205353 * 2 ^ 59
def prefixEnd_1205353 : Nat := 4983230072969 + 3 ^ 40 * 1205353 * 2
def baseEnd_1205353 : Nat := 618925447338927784544189

theorem tailTrace_1205353 : CollatzResearch.WordTrace tailWord_1205353 prefixEnd_1205353 618925447338927784544189 := by
  unfold tailWord_1205353
  simp only [CollatzResearch.WordTrace]
  refine ⟨43962835602219413748324713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29308557068146275832216475 43962835602219413748324713)
  ·
    refine ⟨32972126701664560311243535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43962835602219413748324713 32972126701664560311243535)
    ·
      refine ⟨49458190052496840466865303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32972126701664560311243535 49458190052496840466865303)
      ·
        refine ⟨74187285078745260700297955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49458190052496840466865303 74187285078745260700297955)
        ·
          refine ⟨111280927618117891050446933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74187285078745260700297955 111280927618117891050446933)
          ·
            refine ⟨1304073370524819035747425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 111280927618117891050446933 1304073370524819035747425)
            ·
              refine ⟨978055027893614276810569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304073370524819035747425 978055027893614276810569)
              ·
                refine ⟨733541270920210707607927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978055027893614276810569 733541270920210707607927)
                ·
                  refine ⟨1100311906380316061411891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733541270920210707607927 1100311906380316061411891)
                  ·
                    refine ⟨1650467859570474092117837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100311906380316061411891 1650467859570474092117837)
                    ·
                      refine ⟨618925447338927784544189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650467859570474092117837 618925447338927784544189)
                      ·
                        rfl

theorem cell23_1205353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 1, 3].length) (baseStart_1205353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205353 prefixEnd_1205353 := by exact prefixLift 1205353
  have htrace : WordTrace (prefixWord ++ tailWord_1205353) baseStart_1205353 baseEnd_1205353 := by
    simpa [prefixWord, tailWord_1205353, baseEnd_1205353] using wordTrace_append hprefix tailTrace_1205353
  have hstable : (prefixWord ++ tailWord_1205353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205353).length < 2 ^ (prefixWord ++ tailWord_1205353).sum := by decide
  have hdescent : baseEnd_1205353 < baseStart_1205353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205359 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 3, 2, 2]
def baseStart_1205359 : Nat := 118140960795 + 1205359 * 2 ^ 59
def prefixEnd_1205359 : Nat := 4983230072969 + 3 ^ 40 * 1205359 * 2
def baseEnd_1205359 : Nat := 618928528222854761069161

theorem tailTrace_1205359 : CollatzResearch.WordTrace tailWord_1205359 prefixEnd_1205359 618928528222854761069161 := by
  unfold tailWord_1205359
  simp only [CollatzResearch.WordTrace]
  refine ⟨43963054440197676773043131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29308702960131784515362087 43963054440197676773043131)
  ·
    refine ⟨65944581660296515159564697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43963054440197676773043131 65944581660296515159564697)
    ·
      refine ⟨49458436245222386369673523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65944581660296515159564697 49458436245222386369673523)
      ·
        refine ⟨74187654367833579554510285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49458436245222386369673523 74187654367833579554510285)
        ·
          refine ⟨27820370387937592332941357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74187654367833579554510285 27820370387937592332941357)
          ·
            refine ⟨10432638895476597124853009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27820370387937592332941357 10432638895476597124853009)
            ·
              refine ⟨7824479171607447843639757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10432638895476597124853009 7824479171607447843639757)
              ·
                refine ⟨2934179689352792941364909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7824479171607447843639757 2934179689352792941364909)
                ·
                  refine ⟨1100317383507297353011841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2934179689352792941364909 1100317383507297353011841)
                  ·
                    refine ⟨825238037630473014758881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100317383507297353011841 825238037630473014758881)
                    ·
                      refine ⟨618928528222854761069161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825238037630473014758881 618928528222854761069161)
                      ·
                        rfl

theorem cell23_1205359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2, 2].length) (baseStart_1205359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205359 prefixEnd_1205359 := by exact prefixLift 1205359
  have htrace : WordTrace (prefixWord ++ tailWord_1205359) baseStart_1205359 baseEnd_1205359 := by
    simpa [prefixWord, tailWord_1205359, baseEnd_1205359] using wordTrace_append hprefix tailTrace_1205359
  have hstable : (prefixWord ++ tailWord_1205359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205359).length < 2 ^ (prefixWord ++ tailWord_1205359).sum := by decide
  have hdescent : baseEnd_1205359 < baseStart_1205359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205362 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1205362 : Nat := 118140960795 + 1205362 * 2 ^ 59
def prefixEnd_1205362 : Nat := 4983230072969 + 3 ^ 40 * 1205362 * 2
def baseEnd_1205362 : Nat := 618930068664818249331647

theorem tailTrace_1205362 : CollatzResearch.WordTrace tailWord_1205362 prefixEnd_1205362 618930068664818249331647 := by
  unfold tailWord_1205362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10990790964796702071350585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29308775906124538856934893 10990790964796702071350585)
  ·
    refine ⟨8243093223597526553512939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10990790964796702071350585 8243093223597526553512939)
    ·
      refine ⟨12364639835396289830269409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8243093223597526553512939 12364639835396289830269409)
      ·
        refine ⟨9273479876547217372702057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364639835396289830269409 9273479876547217372702057)
        ·
          refine ⟨6955109907410413029526543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9273479876547217372702057 6955109907410413029526543)
          ·
            refine ⟨10432664861115619544289815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955109907410413029526543 10432664861115619544289815)
            ·
              refine ⟨15648997291673429316434723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432664861115619544289815 15648997291673429316434723)
              ·
                refine ⟨23473495937510143974652085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15648997291673429316434723 23473495937510143974652085)
                ·
                  refine ⟨2200640244141575997623633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23473495937510143974652085 2200640244141575997623633)
                  ·
                    refine ⟨1650480183106181998217725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200640244141575997623633 1650480183106181998217725)
                    ·
                      refine ⟨618930068664818249331647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650480183106181998217725 618930068664818249331647)
                      ·
                        rfl

theorem cell23_1205362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1205362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205362 prefixEnd_1205362 := by exact prefixLift 1205362
  have htrace : WordTrace (prefixWord ++ tailWord_1205362) baseStart_1205362 baseEnd_1205362 := by
    simpa [prefixWord, tailWord_1205362, baseEnd_1205362] using wordTrace_append hprefix tailTrace_1205362
  have hstable : (prefixWord ++ tailWord_1205362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205362).length < 2 ^ (prefixWord ++ tailWord_1205362).sum := by decide
  have hdescent : baseEnd_1205362 < baseStart_1205362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205372 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_1205372 : Nat := 118140960795 + 1205372 * 2 ^ 59
def prefixEnd_1205372 : Nat := 4983230072969 + 3 ^ 40 * 1205372 * 2
def baseEnd_1205372 : Nat := 618935203471363210206601

theorem tailTrace_1205372 : CollatzResearch.WordTrace tailWord_1205372 prefixEnd_1205372 618935203471363210206601 := by
  unfold tailWord_1205372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981764294575289996633185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29309019059433719995510913 21981764294575289996633185)
  ·
    refine ⟨16486323220931467497474889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21981764294575289996633185 16486323220931467497474889)
    ·
      refine ⟨12364742415698600623106167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16486323220931467497474889 12364742415698600623106167)
      ·
        refine ⟨18547113623547900934659251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12364742415698600623106167 18547113623547900934659251)
        ·
          refine ⟨27820670435321851401988877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18547113623547900934659251 27820670435321851401988877)
          ·
            refine ⟨10432751413245694275745829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27820670435321851401988877 10432751413245694275745829)
            ·
              refine ⟨1956140889983567676702343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10432751413245694275745829 1956140889983567676702343)
              ·
                refine ⟨2934211334975351515053515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956140889983567676702343 2934211334975351515053515)
                ·
                  refine ⟨4401317002463027272580273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934211334975351515053515 4401317002463027272580273)
                  ·
                    refine ⟨3300987751847270454435205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401317002463027272580273 3300987751847270454435205)
                    ·
                      refine ⟨618935203471363210206601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3300987751847270454435205 618935203471363210206601)
                      ·
                        rfl

theorem cell23_1205372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_1205372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205372 prefixEnd_1205372 := by exact prefixLift 1205372
  have htrace : WordTrace (prefixWord ++ tailWord_1205372) baseStart_1205372 baseEnd_1205372 := by
    simpa [prefixWord, tailWord_1205372, baseEnd_1205372] using wordTrace_append hprefix tailTrace_1205372
  have hstable : (prefixWord ++ tailWord_1205372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205372).length < 2 ^ (prefixWord ++ tailWord_1205372).sum := by decide
  have hdescent : baseEnd_1205372 < baseStart_1205372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205409 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1205409 : Nat := 118140960795 + 1205409 * 2 ^ 59
def prefixEnd_1205409 : Nat := 4983230072969 + 3 ^ 40 * 1205409 * 2
def baseEnd_1205409 : Nat := 618954202255579565443931

theorem tailTrace_1205409 : CollatzResearch.WordTrace tailWord_1205409 prefixEnd_1205409 618954202255579565443931 := by
  unfold tailWord_1205409
  simp only [CollatzResearch.WordTrace]
  refine ⟨43964878090016535312363281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29309918726677690208242187 43964878090016535312363281)
  ·
    refine ⟨32973658567512401484272461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43964878090016535312363281 32973658567512401484272461)
    ·
      refine ⟨12365121962817150556602173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32973658567512401484272461 12365121962817150556602173)
      ·
        refine ⟨4636920736056431458725815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12365121962817150556602173 4636920736056431458725815)
        ·
          refine ⟨6955381104084647188088723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636920736056431458725815 6955381104084647188088723)
          ·
            refine ⟨10433071656126970782133085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955381104084647188088723 10433071656126970782133085)
            ·
              refine ⟨3912401871047614043299907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10433071656126970782133085 3912401871047614043299907)
              ·
                refine ⟨5868602806571421064949861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912401871047614043299907 5868602806571421064949861)
                ·
                  refine ⟨1100363026232141449678099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5868602806571421064949861 1100363026232141449678099)
                  ·
                    refine ⟨1650544539348212174517149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100363026232141449678099 1650544539348212174517149)
                    ·
                      refine ⟨618954202255579565443931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650544539348212174517149 618954202255579565443931)
                      ·
                        rfl

theorem cell23_1205409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1205409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205409 prefixEnd_1205409 := by exact prefixLift 1205409
  have htrace : WordTrace (prefixWord ++ tailWord_1205409) baseStart_1205409 baseEnd_1205409 := by
    simpa [prefixWord, tailWord_1205409, baseEnd_1205409] using wordTrace_append hprefix tailTrace_1205409
  have hstable : (prefixWord ++ tailWord_1205409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205409).length < 2 ^ (prefixWord ++ tailWord_1205409).sum := by decide
  have hdescent : baseEnd_1205409 < baseStart_1205409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205430 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1205430 : Nat := 118140960795 + 1205430 * 2 ^ 59
def prefixEnd_1205430 : Nat := 4983230072969 + 3 ^ 40 * 1205430 * 2
def baseEnd_1205430 : Nat := 618964985349323983281335

theorem tailTrace_1205430 : CollatzResearch.WordTrace tailWord_1205430 prefixEnd_1205430 618964985349323983281335 := by
  unfold tailWord_1205430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747852751433778493679859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29310429348626970599251829 2747852751433778493679859)
  ·
    refine ⟨4121779127150667740519789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747852751433778493679859 4121779127150667740519789)
    ·
      refine ⟨1545667172681500402694921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4121779127150667740519789 1545667172681500402694921)
      ·
        refine ⟨1159250379511125302021191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545667172681500402694921 1159250379511125302021191)
        ·
          refine ⟨1738875569266687953031787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159250379511125302021191 1738875569266687953031787)
          ·
            refine ⟨2608313353900031929547681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738875569266687953031787 2608313353900031929547681)
            ·
              refine ⟨1956235015425023947160761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608313353900031929547681 1956235015425023947160761)
              ·
                refine ⟨1467176261568767960370571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956235015425023947160761 1467176261568767960370571)
                ·
                  refine ⟨2200764392353151940555857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467176261568767960370571 2200764392353151940555857)
                  ·
                    refine ⟨1650573294264863955416893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200764392353151940555857 1650573294264863955416893)
                    ·
                      refine ⟨618964985349323983281335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650573294264863955416893 618964985349323983281335)
                      ·
                        rfl

theorem cell23_1205430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1205430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205430 prefixEnd_1205430 := by exact prefixLift 1205430
  have htrace : WordTrace (prefixWord ++ tailWord_1205430) baseStart_1205430 baseEnd_1205430 := by
    simpa [prefixWord, tailWord_1205430, baseEnd_1205430] using wordTrace_append hprefix tailTrace_1205430
  have hstable : (prefixWord ++ tailWord_1205430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205430).length < 2 ^ (prefixWord ++ tailWord_1205430).sum := by decide
  have hdescent : baseEnd_1205430 < baseStart_1205430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205436 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_1205436 : Nat := 118140960795 + 1205436 * 2 ^ 59
def prefixEnd_1205436 : Nat := 4983230072969 + 3 ^ 40 * 1205436 * 2
def baseEnd_1205436 : Nat := 618968066233250959806307

theorem tailTrace_1205436 : CollatzResearch.WordTrace tailWord_1205436 prefixEnd_1205436 618968066233250959806307 := by
  unfold tailWord_1205436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21982931430459359461798081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29310575240612479282397441 21982931430459359461798081)
  ·
    refine ⟨16487198572844519596348561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21982931430459359461798081 16487198572844519596348561)
    ·
      refine ⟨12365398929633389697261421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16487198572844519596348561 12365398929633389697261421)
      ·
        refine ⟨4637024598612521136473033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12365398929633389697261421 4637024598612521136473033)
        ·
          refine ⟨3477768448959390852354775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4637024598612521136473033 3477768448959390852354775)
          ·
            refine ⟨5216652673439086278532163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477768448959390852354775 5216652673439086278532163)
            ·
              refine ⟨7824979010158629417798245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216652673439086278532163 7824979010158629417798245)
              ·
                refine ⟨1467183564404743015837171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7824979010158629417798245 1467183564404743015837171)
                ·
                  refine ⟨2200775346607114523755757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467183564404743015837171 2200775346607114523755757)
                  ·
                    refine ⟨825290754977667946408409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2200775346607114523755757 825290754977667946408409)
                    ·
                      refine ⟨618968066233250959806307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825290754977667946408409 618968066233250959806307)
                      ·
                        rfl

theorem cell23_1205436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_1205436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205436 prefixEnd_1205436 := by exact prefixLift 1205436
  have htrace : WordTrace (prefixWord ++ tailWord_1205436) baseStart_1205436 baseEnd_1205436 := by
    simpa [prefixWord, tailWord_1205436, baseEnd_1205436] using wordTrace_append hprefix tailTrace_1205436
  have hstable : (prefixWord ++ tailWord_1205436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205436).length < 2 ^ (prefixWord ++ tailWord_1205436).sum := by decide
  have hdescent : baseEnd_1205436 < baseStart_1205436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205465 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1205465 : Nat := 118140960795 + 1205465 * 2 ^ 59
def prefixEnd_1205465 : Nat := 4983230072969 + 3 ^ 40 * 1205465 * 2
def baseEnd_1205465 : Nat := 618982957172231346343673

theorem tailTrace_1205465 : CollatzResearch.WordTrace tailWord_1205465 prefixEnd_1205465 618982957172231346343673 := by
  unfold tailWord_1205465
  simp only [CollatzResearch.WordTrace]
  refine ⟨43966920577813656876401849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29311280385209104584267899 43966920577813656876401849)
  ·
    refine ⟨32975190433360242657301387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43966920577813656876401849 32975190433360242657301387)
    ·
      refine ⟨49462785650040363985952081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32975190433360242657301387 49462785650040363985952081)
      ·
        refine ⟨37097089237530272989464061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49462785650040363985952081 37097089237530272989464061)
        ·
          refine ⟨13911408464073852371049023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37097089237530272989464061 13911408464073852371049023)
          ·
            refine ⟨20867112696110778556573535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911408464073852371049023 20867112696110778556573535)
            ·
              refine ⟨31300669044166167834860303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20867112696110778556573535 31300669044166167834860303)
              ·
                refine ⟨46951003566249251752290455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31300669044166167834860303 46951003566249251752290455)
                ·
                  refine ⟨70426505349373877628435683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46951003566249251752290455 70426505349373877628435683)
                  ·
                    refine ⟨105639758024060816442653525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70426505349373877628435683 105639758024060816442653525)
                    ·
                      refine ⟨618982957172231346343673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 105639758024060816442653525 618982957172231346343673)
                      ·
                        rfl

theorem cell23_1205465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1205465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205465 prefixEnd_1205465 := by exact prefixLift 1205465
  have htrace : WordTrace (prefixWord ++ tailWord_1205465) baseStart_1205465 baseEnd_1205465 := by
    simpa [prefixWord, tailWord_1205465, baseEnd_1205465] using wordTrace_append hprefix tailTrace_1205465
  have hstable : (prefixWord ++ tailWord_1205465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205465).length < 2 ^ (prefixWord ++ tailWord_1205465).sum := by decide
  have hdescent : baseEnd_1205465 < baseStart_1205465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205466 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_1205466 : Nat := 118140960795 + 1205466 * 2 ^ 59
def prefixEnd_1205466 : Nat := 4983230072969 + 3 ^ 40 * 1205466 * 2
def baseEnd_1205466 : Nat := 618983470652885842431169

theorem tailTrace_1205466 : CollatzResearch.WordTrace tailWord_1205466 prefixEnd_1205466 618983470652885842431169 := by
  unfold tailWord_1205466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991739262702508511797063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29311304700540022698125501 10991739262702508511797063)
  ·
    refine ⟨16487608894053762767695595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10991739262702508511797063 16487608894053762767695595)
    ·
      refine ⟨24731413341080644151543393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16487608894053762767695595 24731413341080644151543393)
      ·
        refine ⟨18548560005810483113657545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24731413341080644151543393 18548560005810483113657545)
        ·
          refine ⟨13911420004357862335243159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18548560005810483113657545 13911420004357862335243159)
          ·
            refine ⟨20867130006536793502864739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911420004357862335243159 20867130006536793502864739)
            ·
              refine ⟨31300695009805190254297109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20867130006536793502864739 31300695009805190254297109)
              ·
                refine ⟨1467220078584618293170177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31300695009805190254297109 1467220078584618293170177)
                ·
                  refine ⟨1100415058938463719877633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467220078584618293170177 1100415058938463719877633)
                  ·
                    refine ⟨825311294203847789908225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100415058938463719877633 825311294203847789908225)
                    ·
                      refine ⟨618983470652885842431169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825311294203847789908225 618983470652885842431169)
                      ·
                        rfl

theorem cell23_1205466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_1205466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205466 prefixEnd_1205466 := by exact prefixLift 1205466
  have htrace : WordTrace (prefixWord ++ tailWord_1205466) baseStart_1205466 baseEnd_1205466 := by
    simpa [prefixWord, tailWord_1205466, baseEnd_1205466] using wordTrace_append hprefix tailTrace_1205466
  have hstable : (prefixWord ++ tailWord_1205466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205466).length < 2 ^ (prefixWord ++ tailWord_1205466).sum := by decide
  have hdescent : baseEnd_1205466 < baseStart_1205466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205472 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 7]
def baseStart_1205472 : Nat := 118140960795 + 1205472 * 2 ^ 59
def prefixEnd_1205472 : Nat := 4983230072969 + 3 ^ 40 * 1205472 * 2
def baseEnd_1205472 : Nat := 68776283504090313217349

theorem tailTrace_1205472 : CollatzResearch.WordTrace tailWord_1205472 prefixEnd_1205472 68776283504090313217349 := by
  unfold tailWord_1205472
  simp only [CollatzResearch.WordTrace]
  refine ⟨21983587944394148535953335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29311450592525531381271113 21983587944394148535953335)
  ·
    refine ⟨32975381916591222803930003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21983587944394148535953335 32975381916591222803930003)
    ·
      refine ⟨49463072874886834205895005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32975381916591222803930003 49463072874886834205895005)
      ·
        refine ⟨18548652328082562827210627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49463072874886834205895005 18548652328082562827210627)
        ·
          refine ⟨27822978492123844240815941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18548652328082562827210627 27822978492123844240815941)
          ·
            refine ⟨5216808467273220795152989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27822978492123844240815941 5216808467273220795152989)
            ·
              refine ⟨1956303175227457798182371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5216808467273220795152989 1956303175227457798182371)
              ·
                refine ⟨2934454762841186697273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956303175227457798182371 2934454762841186697273557)
                ·
                  refine ⟨68776283504090313217349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2934454762841186697273557 68776283504090313217349)
                  ·
                    rfl

theorem cell23_1205472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_1205472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205472 prefixEnd_1205472 := by exact prefixLift 1205472
  have htrace : WordTrace (prefixWord ++ tailWord_1205472) baseStart_1205472 baseEnd_1205472 := by
    simpa [prefixWord, tailWord_1205472, baseEnd_1205472] using wordTrace_append hprefix tailTrace_1205472
  have hstable : (prefixWord ++ tailWord_1205472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205472).length < 2 ^ (prefixWord ++ tailWord_1205472).sum := by decide
  have hdescent : baseEnd_1205472 < baseStart_1205472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205483 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 2, 2, 2]
def baseStart_1205483 : Nat := 118140960795 + 1205483 * 2 ^ 59
def prefixEnd_1205483 : Nat := 4983230072969 + 3 ^ 40 * 1205483 * 2
def baseEnd_1205483 : Nat := 618992199824012275918591

theorem tailTrace_1205483 : CollatzResearch.WordTrace tailWord_1205483 prefixEnd_1205483 618992199824012275918591 := by
  unfold tailWord_1205483
  simp only [CollatzResearch.WordTrace]
  refine ⟨43967577091748445950557103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29311718061165630633704735 43967577091748445950557103)
  ·
    refine ⟨65951365637622668925835655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43967577091748445950557103 65951365637622668925835655)
    ·
      refine ⟨98927048456434003388753483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65951365637622668925835655 98927048456434003388753483)
      ·
        refine ⟨148390572684651005083130225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98927048456434003388753483 148390572684651005083130225)
        ·
          refine ⟨111292929513488253812347669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148390572684651005083130225 111292929513488253812347669)
          ·
            refine ⟨5216856070944761897453797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111292929513488253812347669 5216856070944761897453797)
            ·
              refine ⟨978160513302142855772587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5216856070944761897453797 978160513302142855772587)
              ·
                refine ⟨1467240769953214283658881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978160513302142855772587 1467240769953214283658881)
                ·
                  refine ⟨1100430577464910712744161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467240769953214283658881 1100430577464910712744161)
                  ·
                    refine ⟨825322933098683034558121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100430577464910712744161 825322933098683034558121)
                    ·
                      refine ⟨618992199824012275918591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825322933098683034558121 618992199824012275918591)
                      ·
                        rfl

theorem cell23_1205483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 2, 2].length) (baseStart_1205483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205483 prefixEnd_1205483 := by exact prefixLift 1205483
  have htrace : WordTrace (prefixWord ++ tailWord_1205483) baseStart_1205483 baseEnd_1205483 := by
    simpa [prefixWord, tailWord_1205483, baseEnd_1205483] using wordTrace_append hprefix tailTrace_1205483
  have hstable : (prefixWord ++ tailWord_1205483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205483).length < 2 ^ (prefixWord ++ tailWord_1205483).sum := by decide
  have hdescent : baseEnd_1205483 < baseStart_1205483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205539 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 6, 2]
def baseStart_1205539 : Nat := 118140960795 + 1205539 * 2 ^ 59
def prefixEnd_1205539 : Nat := 4983230072969 + 3 ^ 40 * 1205539 * 2
def baseEnd_1205539 : Nat := 619020954740664056818333

theorem tailTrace_1205539 : CollatzResearch.WordTrace tailWord_1205539 prefixEnd_1205539 619020954740664056818333 := by
  unfold tailWord_1205539
  simp only [CollatzResearch.WordTrace]
  refine ⟨43969619579545567514595671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29313079719697045009730447 43969619579545567514595671)
  ·
    refine ⟨65954429369318351271893507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43969619579545567514595671 65954429369318351271893507)
    ·
      refine ⟨98931644053977526907840261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65954429369318351271893507 98931644053977526907840261)
      ·
        refine ⟨18549683260120786295220049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98931644053977526907840261 18549683260120786295220049)
        ·
          refine ⟨13912262445090589721415037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18549683260120786295220049 13912262445090589721415037)
          ·
            refine ⟨5217098416908971145530639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13912262445090589721415037 5217098416908971145530639)
            ·
              refine ⟨7825647625363456718295959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217098416908971145530639 7825647625363456718295959)
              ·
                refine ⟨11738471438045185077443939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7825647625363456718295959 11738471438045185077443939)
                ·
                  refine ⟨17607707157067777616165909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11738471438045185077443939 17607707157067777616165909)
                  ·
                    refine ⟨825361272987552075757777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17607707157067777616165909 825361272987552075757777)
                    ·
                      refine ⟨619020954740664056818333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825361272987552075757777 619020954740664056818333)
                      ·
                        rfl

theorem cell23_1205539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_1205539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205539 prefixEnd_1205539 := by exact prefixLift 1205539
  have htrace : WordTrace (prefixWord ++ tailWord_1205539) baseStart_1205539 baseEnd_1205539 := by
    simpa [prefixWord, tailWord_1205539, baseEnd_1205539] using wordTrace_append hprefix tailTrace_1205539
  have hstable : (prefixWord ++ tailWord_1205539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205539).length < 2 ^ (prefixWord ++ tailWord_1205539).sum := by decide
  have hdescent : baseEnd_1205539 < baseStart_1205539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205556 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1205556 : Nat := 118140960795 + 1205556 * 2 ^ 59
def prefixEnd_1205556 : Nat := 4983230072969 + 3 ^ 40 * 1205556 * 2
def baseEnd_1205556 : Nat := 619029683911790490305755

theorem tailTrace_1205556 : CollatzResearch.WordTrace tailWord_1205556 prefixEnd_1205556 619029683911790490305755 := by
  unfold tailWord_1205556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985119810241989708982261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29313493080322652945309681 21985119810241989708982261)
  ·
    refine ⟨2061104982210186535217087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21985119810241989708982261 2061104982210186535217087)
    ·
      refine ⟨3091657473315279802825631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061104982210186535217087 3091657473315279802825631)
      ·
        refine ⟨4637486209972919704238447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091657473315279802825631 4637486209972919704238447)
        ·
          refine ⟨6956229314959379556357671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637486209972919704238447 6956229314959379556357671)
          ·
            refine ⟨10434343972439069334536507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956229314959379556357671 10434343972439069334536507)
            ·
              refine ⟨15651515958658604001804761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10434343972439069334536507 15651515958658604001804761)
              ·
                refine ⟨11738636968993953001353571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15651515958658604001804761 11738636968993953001353571)
                ·
                  refine ⟨17607955453490929502030357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11738636968993953001353571 17607955453490929502030357)
                  ·
                    refine ⟨825372911882387320407673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17607955453490929502030357 825372911882387320407673)
                    ·
                      refine ⟨619029683911790490305755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825372911882387320407673 619029683911790490305755)
                      ·
                        rfl

theorem cell23_1205556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1205556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205556 prefixEnd_1205556 := by exact prefixLift 1205556
  have htrace : WordTrace (prefixWord ++ tailWord_1205556) baseStart_1205556 baseEnd_1205556 := by
    simpa [prefixWord, tailWord_1205556, baseEnd_1205556] using wordTrace_append hprefix tailTrace_1205556
  have hstable : (prefixWord ++ tailWord_1205556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205556).length < 2 ^ (prefixWord ++ tailWord_1205556).sum := by decide
  have hdescent : baseEnd_1205556 < baseStart_1205556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205562 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_1205562 : Nat := 118140960795 + 1205562 * 2 ^ 59
def prefixEnd_1205562 : Nat := 4983230072969 + 3 ^ 40 * 1205562 * 2
def baseEnd_1205562 : Nat := 68781418310635274092303

theorem tailTrace_1205562 : CollatzResearch.WordTrace tailWord_1205562 prefixEnd_1205562 68781418310635274092303 := by
  unfold tailWord_1205562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992614614615560610670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29313638972308161628455293 10992614614615560610670735)
  ·
    refine ⟨16488921921923340916006103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992614614615560610670735 16488921921923340916006103)
    ·
      refine ⟨24733382882885011374009155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16488921921923340916006103 24733382882885011374009155)
      ·
        refine ⟨37100074324327517061013733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24733382882885011374009155 37100074324327517061013733)
        ·
          refine ⟨6956263935811409448940075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37100074324327517061013733 6956263935811409448940075)
          ·
            refine ⟨10434395903717114173410113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956263935811409448940075 10434395903717114173410113)
            ·
              refine ⟨7825796927787835630057585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10434395903717114173410113 7825796927787835630057585)
              ·
                refine ⟨5869347695840876722543189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825796927787835630057585 5869347695840876722543189)
                ·
                  refine ⟨68781418310635274092303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5869347695840876722543189 68781418310635274092303)
                  ·
                    rfl

theorem cell23_1205562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_1205562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205562 prefixEnd_1205562 := by exact prefixLift 1205562
  have htrace : WordTrace (prefixWord ++ tailWord_1205562) baseStart_1205562 baseEnd_1205562 := by
    simpa [prefixWord, tailWord_1205562, baseEnd_1205562] using wordTrace_append hprefix tailTrace_1205562
  have hstable : (prefixWord ++ tailWord_1205562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205562).length < 2 ^ (prefixWord ++ tailWord_1205562).sum := by decide
  have hdescent : baseEnd_1205562 < baseStart_1205562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205569 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1205569 : Nat := 118140960795 + 1205569 * 2 ^ 59
def prefixEnd_1205569 : Nat := 4983230072969 + 3 ^ 40 * 1205569 * 2
def baseEnd_1205569 : Nat := 619036359160298939443195

theorem tailTrace_1205569 : CollatzResearch.WordTrace tailWord_1205569 prefixEnd_1205569 619036359160298939443195 := by
  unfold tailWord_1205569
  simp only [CollatzResearch.WordTrace]
  refine ⟨43970713769436882638187761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29313809179624588425458507 43970713769436882638187761)
  ·
    refine ⟨32978035327077661978640821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43970713769436882638187761 32978035327077661978640821)
    ·
      refine ⟨3091690811913530810497577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32978035327077661978640821 3091690811913530810497577)
      ·
        refine ⟨2318768108935148107873183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3091690811913530810497577 2318768108935148107873183)
        ·
          refine ⟨3478152163402722161809775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318768108935148107873183 3478152163402722161809775)
          ·
            refine ⟨5217228245104083242714663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478152163402722161809775 5217228245104083242714663)
            ·
              refine ⟨7825842367656124864071995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217228245104083242714663 7825842367656124864071995)
              ·
                refine ⟨11738763551484187296107993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7825842367656124864071995 11738763551484187296107993)
                ·
                  refine ⟨8804072663613140472080995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11738763551484187296107993 8804072663613140472080995)
                  ·
                    refine ⟨13206108995419710708121493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8804072663613140472080995 13206108995419710708121493)
                    ·
                      refine ⟨619036359160298939443195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13206108995419710708121493 619036359160298939443195)
                      ·
                        rfl

theorem cell23_1205569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1205569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205569 prefixEnd_1205569 := by exact prefixLift 1205569
  have htrace : WordTrace (prefixWord ++ tailWord_1205569) baseStart_1205569 baseEnd_1205569 := by
    simpa [prefixWord, tailWord_1205569, baseEnd_1205569] using wordTrace_append hprefix tailTrace_1205569
  have hstable : (prefixWord ++ tailWord_1205569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205569).length < 2 ^ (prefixWord ++ tailWord_1205569).sum := by decide
  have hdescent : baseEnd_1205569 < baseStart_1205569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205582 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1205582 : Nat := 118140960795 + 1205582 * 2 ^ 59
def prefixEnd_1205582 : Nat := 4983230072969 + 3 ^ 40 * 1205582 * 2
def baseEnd_1205582 : Nat := 619043034408807388580635

theorem tailTrace_1205582 : CollatzResearch.WordTrace tailWord_1205582 prefixEnd_1205582 619043034408807388580635 := by
  unfold tailWord_1205582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496398489798723232301375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29314125278926523905607333 5496398489798723232301375)
  ·
    refine ⟨8244597734698084848452063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496398489798723232301375 8244597734698084848452063)
    ·
      refine ⟨12366896602047127272678095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8244597734698084848452063 12366896602047127272678095)
      ·
        refine ⟨18550344903070690909017143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366896602047127272678095 18550344903070690909017143)
        ·
          refine ⟨27825517354606036363525715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18550344903070690909017143 27825517354606036363525715)
          ·
            refine ⟨41738276031909054545288573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27825517354606036363525715 41738276031909054545288573)
            ·
              refine ⟨15651853511965895454483215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41738276031909054545288573 15651853511965895454483215)
              ·
                refine ⟨23477780267948843181724823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15651853511965895454483215 23477780267948843181724823)
                ·
                  refine ⟨35216670401923264772587235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23477780267948843181724823 35216670401923264772587235)
                  ·
                    refine ⟨52825005602884897158880853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35216670401923264772587235 52825005602884897158880853)
                    ·
                      refine ⟨619043034408807388580635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52825005602884897158880853 619043034408807388580635)
                      ·
                        rfl

theorem cell23_1205582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1205582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205582 prefixEnd_1205582 := by exact prefixLift 1205582
  have htrace : WordTrace (prefixWord ++ tailWord_1205582) baseStart_1205582 baseEnd_1205582 := by
    simpa [prefixWord, tailWord_1205582, baseEnd_1205582] using wordTrace_append hprefix tailTrace_1205582
  have hstable : (prefixWord ++ tailWord_1205582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205582).length < 2 ^ (prefixWord ++ tailWord_1205582).sum := by decide
  have hdescent : baseEnd_1205582 < baseStart_1205582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205616 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2]
def baseStart_1205616 : Nat := 118140960795 + 1205616 * 2 ^ 59
def prefixEnd_1205616 : Nat := 4983230072969 + 3 ^ 40 * 1205616 * 2
def baseEnd_1205616 : Nat := 619060492751060255555479

theorem tailTrace_1205616 : CollatzResearch.WordTrace tailWord_1205616 prefixEnd_1205616 619060492751060255555479 := by
  unfold tailWord_1205616
  simp only [CollatzResearch.WordTrace]
  refine ⟨21986214000133304832574351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29314952000177739776765801 21986214000133304832574351)
  ·
    refine ⟨32979321000199957248861527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21986214000133304832574351 32979321000199957248861527)
    ·
      refine ⟨49468981500299935873292291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32979321000199957248861527 49468981500299935873292291)
      ·
        refine ⟨74203472250449903809938437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49468981500299935873292291 74203472250449903809938437)
        ·
          refine ⟨13913151046959356964363457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74203472250449903809938437 13913151046959356964363457)
          ·
            refine ⟨10434863285219517723272593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13913151046959356964363457 10434863285219517723272593)
            ·
              refine ⟨7826147463914638292454445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10434863285219517723272593 7826147463914638292454445)
              ·
                refine ⟨2934805298967989359670417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7826147463914638292454445 2934805298967989359670417)
                ·
                  refine ⟨2201103974225992019752813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934805298967989359670417 2201103974225992019752813)
                  ·
                    refine ⟨825413990334747007407305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2201103974225992019752813 825413990334747007407305)
                    ·
                      refine ⟨619060492751060255555479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825413990334747007407305 619060492751060255555479)
                      ·
                        rfl

theorem cell23_1205616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 3, 2].length) (baseStart_1205616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205616 prefixEnd_1205616 := by exact prefixLift 1205616
  have htrace : WordTrace (prefixWord ++ tailWord_1205616) baseStart_1205616 baseEnd_1205616 := by
    simpa [prefixWord, tailWord_1205616, baseEnd_1205616] using wordTrace_append hprefix tailTrace_1205616
  have hstable : (prefixWord ++ tailWord_1205616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205616).length < 2 ^ (prefixWord ++ tailWord_1205616).sum := by decide
  have hdescent : baseEnd_1205616 < baseStart_1205616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205649 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_1205649 : Nat := 118140960795 + 1205649 * 2 ^ 59
def prefixEnd_1205649 : Nat := 4983230072969 + 3 ^ 40 * 1205649 * 2
def baseEnd_1205649 : Nat := 619077437612658626442827

theorem tailTrace_1205649 : CollatzResearch.WordTrace tailWord_1205649 prefixEnd_1205649 619077437612658626442827 := by
  unfold tailWord_1205649
  simp only [CollatzResearch.WordTrace]
  refine ⟨43973631609147056301100001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29315754406098037534066667 43973631609147056301100001)
  ·
    refine ⟨32980223706860292225825001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43973631609147056301100001 32980223706860292225825001)
    ·
      refine ⟨24735167780145219169368751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32980223706860292225825001 24735167780145219169368751)
      ·
        refine ⟨37102751670217828754053127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24735167780145219169368751 37102751670217828754053127)
        ·
          refine ⟨55654127505326743131079691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37102751670217828754053127 55654127505326743131079691)
          ·
            refine ⟨83481191257990114696619537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55654127505326743131079691 83481191257990114696619537)
            ·
              refine ⟨62610893443492586022464653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83481191257990114696619537 62610893443492586022464653)
              ·
                refine ⟨23479085041309719758424245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62610893443492586022464653 23479085041309719758424245)
                ·
                  refine ⟨2201164222622786227352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23479085041309719758424245 2201164222622786227352273)
                  ·
                    refine ⟨1650873166967089670514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2201164222622786227352273 1650873166967089670514205)
                    ·
                      refine ⟨619077437612658626442827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650873166967089670514205 619077437612658626442827)
                      ·
                        rfl

theorem cell23_1205649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_1205649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205649 prefixEnd_1205649 := by exact prefixLift 1205649
  have htrace : WordTrace (prefixWord ++ tailWord_1205649) baseStart_1205649 baseEnd_1205649 := by
    simpa [prefixWord, tailWord_1205649, baseEnd_1205649] using wordTrace_append hprefix tailTrace_1205649
  have hstable : (prefixWord ++ tailWord_1205649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205649).length < 2 ^ (prefixWord ++ tailWord_1205649).sum := by decide
  have hdescent : baseEnd_1205649 < baseStart_1205649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205660 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1205660 : Nat := 118140960795 + 1205660 * 2 ^ 59
def prefixEnd_1205660 : Nat := 4983230072969 + 3 ^ 40 * 1205660 * 2
def baseEnd_1205660 : Nat := 206361028633286027801759

theorem tailTrace_1205660 : CollatzResearch.WordTrace tailWord_1205660 prefixEnd_1205660 206361028633286027801759 := by
  unfold tailWord_1205660
  simp only [CollatzResearch.WordTrace]
  refine ⟨21987016406053602589875217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29316021874738136786500289 21987016406053602589875217)
  ·
    refine ⟨16490262304540201942406413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21987016406053602589875217 16490262304540201942406413)
    ·
      refine ⟨6183848364202575728402405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16490262304540201942406413 6183848364202575728402405)
      ·
        refine ⟨1159471568287982949075451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6183848364202575728402405 1159471568287982949075451)
        ·
          refine ⟨1739207352431974423613177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159471568287982949075451 1739207352431974423613177)
          ·
            refine ⟨1304405514323980817709883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739207352431974423613177 1304405514323980817709883)
            ·
              refine ⟨1956608271485971226564825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304405514323980817709883 1956608271485971226564825)
              ·
                refine ⟨1467456203614478419923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956608271485971226564825 1467456203614478419923619)
                ·
                  refine ⟨2201184305421717629885429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467456203614478419923619 2201184305421717629885429)
                  ·
                    refine ⟨206361028633286027801759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2201184305421717629885429 206361028633286027801759)
                    ·
                      rfl

theorem cell23_1205660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1205660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205660 prefixEnd_1205660 := by exact prefixLift 1205660
  have htrace : WordTrace (prefixWord ++ tailWord_1205660) baseStart_1205660 baseEnd_1205660 := by
    simpa [prefixWord, tailWord_1205660, baseEnd_1205660] using wordTrace_append hprefix tailTrace_1205660
  have hstable : (prefixWord ++ tailWord_1205660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205660).length < 2 ^ (prefixWord ++ tailWord_1205660).sum := by decide
  have hdescent : baseEnd_1205660 < baseStart_1205660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205663 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1205663 : Nat := 118140960795 + 1205663 * 2 ^ 59
def prefixEnd_1205663 : Nat := 4983230072969 + 3 ^ 40 * 1205663 * 2
def baseEnd_1205663 : Nat := 619084626341821571667763

theorem tailTrace_1205663 : CollatzResearch.WordTrace tailWord_1205663 prefixEnd_1205663 619084626341821571667763 := by
  unfold tailWord_1205663
  simp only [CollatzResearch.WordTrace]
  refine ⟨43974142231096336692109643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29316094820730891128073095 43974142231096336692109643)
  ·
    refine ⟨65961213346644505038164465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43974142231096336692109643 65961213346644505038164465)
    ·
      refine ⟨49470910009983378778623349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65961213346644505038164465 49470910009983378778623349)
      ·
        refine ⟨4637897813435941760495939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49470910009983378778623349 4637897813435941760495939)
        ·
          refine ⟨6956846720153912640743909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637897813435941760495939 6956846720153912640743909)
          ·
            refine ⟨1304408760028858620139483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6956846720153912640743909 1304408760028858620139483)
            ·
              refine ⟨1956613140043287930209225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304408760028858620139483 1956613140043287930209225)
              ·
                refine ⟨1467459855032465947656919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956613140043287930209225 1467459855032465947656919)
                ·
                  refine ⟨2201189782548698921485379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467459855032465947656919 2201189782548698921485379)
                  ·
                    refine ⟨3301784673823048382228069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2201189782548698921485379 3301784673823048382228069)
                    ·
                      refine ⟨619084626341821571667763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3301784673823048382228069 619084626341821571667763)
                      ·
                        rfl

theorem cell23_1205663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1205663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205663 prefixEnd_1205663 := by exact prefixLift 1205663
  have htrace : WordTrace (prefixWord ++ tailWord_1205663) baseStart_1205663 baseEnd_1205663 := by
    simpa [prefixWord, tailWord_1205663, baseEnd_1205663] using wordTrace_append hprefix tailTrace_1205663
  have hstable : (prefixWord ++ tailWord_1205663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205663).length < 2 ^ (prefixWord ++ tailWord_1205663).sum := by decide
  have hdescent : baseEnd_1205663 < baseStart_1205663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205696 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_1205696 : Nat := 118140960795 + 1205696 * 2 ^ 59
def prefixEnd_1205696 : Nat := 4983230072969 + 3 ^ 40 * 1205696 * 2
def baseEnd_1205696 : Nat := 619101571203419942555111

theorem tailTrace_1205696 : CollatzResearch.WordTrace tailWord_1205696 prefixEnd_1205696 619101571203419942555111 := by
  unfold tailWord_1205696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21987672919988391664030471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29316897226651188885373961 21987672919988391664030471)
  ·
    refine ⟨32981509379982587496045707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21987672919988391664030471 32981509379982587496045707)
    ·
      refine ⟨49472264069973881244068561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32981509379982587496045707 49472264069973881244068561)
      ·
        refine ⟨37104198052480410933051421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49472264069973881244068561 37104198052480410933051421)
        ·
          refine ⟨13914074269680154099894283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37104198052480410933051421 13914074269680154099894283)
          ·
            refine ⟨20871111404520231149841425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13914074269680154099894283 20871111404520231149841425)
            ·
              refine ⟨15653333553390173362381069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20871111404520231149841425 15653333553390173362381069)
              ·
                refine ⟨5870000082521315010892901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15653333553390173362381069 5870000082521315010892901)
                ·
                  refine ⟨1100625015472746564542419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5870000082521315010892901 1100625015472746564542419)
                  ·
                    refine ⟨1650937523209119846813629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100625015472746564542419 1650937523209119846813629)
                    ·
                      refine ⟨619101571203419942555111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650937523209119846813629 619101571203419942555111)
                      ·
                        rfl

theorem cell23_1205696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_1205696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205696 prefixEnd_1205696 := by exact prefixLift 1205696
  have htrace : WordTrace (prefixWord ++ tailWord_1205696) baseStart_1205696 baseEnd_1205696 := by
    simpa [prefixWord, tailWord_1205696, baseEnd_1205696] using wordTrace_append hprefix tailTrace_1205696
  have hstable : (prefixWord ++ tailWord_1205696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205696).length < 2 ^ (prefixWord ++ tailWord_1205696).sum := by decide
  have hdescent : baseEnd_1205696 < baseStart_1205696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205739 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3]
def baseStart_1205739 : Nat := 118140960795 + 1205739 * 2 ^ 59
def prefixEnd_1205739 : Nat := 4983230072969 + 3 ^ 40 * 1205739 * 2
def baseEnd_1205739 : Nat := 619123650871563274317413

theorem tailTrace_1205739 : CollatzResearch.WordTrace tailWord_1205739 prefixEnd_1205739 619123650871563274317413 := by
  unfold tailWord_1205739
  simp only [CollatzResearch.WordTrace]
  refine ⟨43976914178821001671876271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29317942785880667781250847 43976914178821001671876271)
  ·
    refine ⟨65965371268231502507814407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43976914178821001671876271 65965371268231502507814407)
    ·
      refine ⟨98948056902347253761721611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65965371268231502507814407 98948056902347253761721611)
      ·
        refine ⟨148422085353520880642582417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98948056902347253761721611 148422085353520880642582417)
        ·
          refine ⟨111316564015140660481936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148422085353520880642582417 111316564015140660481936813)
          ·
            refine ⟨41743711505677747680726305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111316564015140660481936813 41743711505677747680726305)
            ·
              refine ⟨31307783629258310760544729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41743711505677747680726305 31307783629258310760544729)
              ·
                refine ⟨23480837721943733070408547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31307783629258310760544729 23480837721943733070408547)
                ·
                  refine ⟨35221256582915599605612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23480837721943733070408547 35221256582915599605612821)
                  ·
                    refine ⟨1650996402324168731513101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35221256582915599605612821 1650996402324168731513101)
                    ·
                      refine ⟨619123650871563274317413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1650996402324168731513101 619123650871563274317413)
                      ·
                        rfl

theorem cell23_1205739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 3].length) (baseStart_1205739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205739 prefixEnd_1205739 := by exact prefixLift 1205739
  have htrace : WordTrace (prefixWord ++ tailWord_1205739) baseStart_1205739 baseEnd_1205739 := by
    simpa [prefixWord, tailWord_1205739, baseEnd_1205739] using wordTrace_append hprefix tailTrace_1205739
  have hstable : (prefixWord ++ tailWord_1205739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205739).length < 2 ^ (prefixWord ++ tailWord_1205739).sum := by decide
  have hdescent : baseEnd_1205739 < baseStart_1205739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205746 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1205746 : Nat := 118140960795 + 1205746 * 2 ^ 59
def prefixEnd_1205746 : Nat := 4983230072969 + 3 ^ 40 * 1205746 * 2
def baseEnd_1205746 : Nat := 206375748412048248976627

theorem tailTrace_1205746 : CollatzResearch.WordTrace tailWord_1205746 prefixEnd_1205746 206375748412048248976627 := by
  unfold tailWord_1205746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994292372448910466845273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29318112993197094578254061 10994292372448910466845273)
  ·
    refine ⟨8245719279336682850133955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10994292372448910466845273 8245719279336682850133955)
    ·
      refine ⟨12368578919005024275200933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8245719279336682850133955 12368578919005024275200933)
      ·
        refine ⟨2319108547313442051600175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12368578919005024275200933 2319108547313442051600175)
        ·
          refine ⟨3478662820970163077400263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319108547313442051600175 3478662820970163077400263)
          ·
            refine ⟨5217994231455244616100395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478662820970163077400263 5217994231455244616100395)
            ·
              refine ⟨7826991347182866924150593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217994231455244616100395 7826991347182866924150593)
              ·
                refine ⟨5870243510387150193112945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7826991347182866924150593 5870243510387150193112945)
                ·
                  refine ⟨4402682632790362644834709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870243510387150193112945 4402682632790362644834709)
                  ·
                    refine ⟨206375748412048248976627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4402682632790362644834709 206375748412048248976627)
                    ·
                      rfl

theorem cell23_1205746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1205746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205746 prefixEnd_1205746 := by exact prefixLift 1205746
  have htrace : WordTrace (prefixWord ++ tailWord_1205746) baseStart_1205746 baseEnd_1205746 := by
    simpa [prefixWord, tailWord_1205746, baseEnd_1205746] using wordTrace_append hprefix tailTrace_1205746
  have hstable : (prefixWord ++ tailWord_1205746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205746).length < 2 ^ (prefixWord ++ tailWord_1205746).sum := by decide
  have hdescent : baseEnd_1205746 < baseStart_1205746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205770 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1205770 : Nat := 118140960795 + 1205770 * 2 ^ 59
def prefixEnd_1205770 : Nat := 4983230072969 + 3 ^ 40 * 1205770 * 2
def baseEnd_1205770 : Nat := 619139568771852653029771

theorem tailTrace_1205770 : CollatzResearch.WordTrace tailWord_1205770 prefixEnd_1205770 619139568771852653029771 := by
  unfold tailWord_1205770
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994511210427173491563691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29318696561139129310836509 10994511210427173491563691)
  ·
    refine ⟨16491766815640760237345537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10994511210427173491563691 16491766815640760237345537)
    ·
      refine ⟨12368825111730570178009153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16491766815640760237345537 12368825111730570178009153)
      ·
        refine ⟨9276618833797927633506865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12368825111730570178009153 9276618833797927633506865)
        ·
          refine ⟨6957464125348445725130149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9276618833797927633506865 6957464125348445725130149)
          ·
            refine ⟨1304524523502833573461903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6957464125348445725130149 1304524523502833573461903)
            ·
              refine ⟨1956786785254250360192855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304524523502833573461903 1956786785254250360192855)
              ·
                refine ⟨2935180177881375540289283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956786785254250360192855 2935180177881375540289283)
                ·
                  refine ⟨4402770266822063310433925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935180177881375540289283 4402770266822063310433925)
                  ·
                    refine ⟨825519425029136870706361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402770266822063310433925 825519425029136870706361)
                    ·
                      refine ⟨619139568771852653029771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825519425029136870706361 619139568771852653029771)
                      ·
                        rfl

theorem cell23_1205770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1205770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205770 prefixEnd_1205770 := by exact prefixLift 1205770
  have htrace : WordTrace (prefixWord ++ tailWord_1205770) baseStart_1205770 baseEnd_1205770 := by
    simpa [prefixWord, tailWord_1205770, baseEnd_1205770] using wordTrace_append hprefix tailTrace_1205770
  have hstable : (prefixWord ++ tailWord_1205770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205770).length < 2 ^ (prefixWord ++ tailWord_1205770).sum := by decide
  have hdescent : baseEnd_1205770 < baseStart_1205770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205793 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 5]
def baseStart_1205793 : Nat := 118140960795 + 1205793 * 2 ^ 59
def prefixEnd_1205793 : Nat := 4983230072969 + 3 ^ 40 * 1205793 * 2
def baseEnd_1205793 : Nat := 68794597647434007004685

theorem tailTrace_1205793 : CollatzResearch.WordTrace tailWord_1205793 prefixEnd_1205793 68794597647434007004685 := by
  unfold tailWord_1205793
  simp only [CollatzResearch.WordTrace]
  refine ⟨43978883720625368894342033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29319255813750245929561355 43978883720625368894342033)
  ·
    refine ⟨32984162790469026670756525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43978883720625368894342033 32984162790469026670756525)
    ·
      refine ⟨12369061046425885001533697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32984162790469026670756525 12369061046425885001533697)
      ·
        refine ⟨9276795784819413751150273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12369061046425885001533697 9276795784819413751150273)
        ·
          refine ⟨6957596838614560313362705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9276795784819413751150273 6957596838614560313362705)
          ·
            refine ⟨5218197628960920235022029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957596838614560313362705 5218197628960920235022029)
            ·
              refine ⟨1956824110860345088133261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5218197628960920235022029 1956824110860345088133261)
              ·
                refine ⟨733809041572629408049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1956824110860345088133261 733809041572629408049973)
                ·
                  refine ⟨68794597647434007004685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 733809041572629408049973 68794597647434007004685)
                  ·
                    rfl

theorem cell23_1205793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 5].length) (baseStart_1205793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205793 prefixEnd_1205793 := by exact prefixLift 1205793
  have htrace : WordTrace (prefixWord ++ tailWord_1205793) baseStart_1205793 baseEnd_1205793 := by
    simpa [prefixWord, tailWord_1205793, baseEnd_1205793] using wordTrace_append hprefix tailTrace_1205793
  have hstable : (prefixWord ++ tailWord_1205793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205793).length < 2 ^ (prefixWord ++ tailWord_1205793).sum := by decide
  have hdescent : baseEnd_1205793 < baseStart_1205793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205816 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1205816 : Nat := 118140960795 + 1205816 * 2 ^ 59
def prefixEnd_1205816 : Nat := 4983230072969 + 3 ^ 40 * 1205816 * 2
def baseEnd_1205816 : Nat := 619163188881959473054559

theorem tailTrace_1205816 : CollatzResearch.WordTrace tailWord_1205816 prefixEnd_1205816 619163188881959473054559 := by
  unfold tailWord_1205816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989861299771021911214651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29319815066361362548286201 21989861299771021911214651)
  ·
    refine ⟨32984791949656532866821977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21989861299771021911214651 32984791949656532866821977)
    ·
      refine ⟨24738593962242399650116483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32984791949656532866821977 24738593962242399650116483)
      ·
        refine ⟨37107890943363599475174725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24738593962242399650116483 37107890943363599475174725)
        ·
          refine ⟨6957729551880674901595261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37107890943363599475174725 6957729551880674901595261)
          ·
            refine ⟨2609148581955253088098223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6957729551880674901595261 2609148581955253088098223)
            ·
              refine ⟨3913722872932879632147335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609148581955253088098223 3913722872932879632147335)
              ·
                refine ⟨5870584309399319448221003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913722872932879632147335 5870584309399319448221003)
                ·
                  refine ⟨8805876464098979172331505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870584309399319448221003 8805876464098979172331505)
                  ·
                    refine ⟨6604407348074234379248629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8805876464098979172331505 6604407348074234379248629)
                    ·
                      refine ⟨619163188881959473054559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6604407348074234379248629 619163188881959473054559)
                      ·
                        rfl

theorem cell23_1205816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1205816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205816 prefixEnd_1205816 := by exact prefixLift 1205816
  have htrace : WordTrace (prefixWord ++ tailWord_1205816) baseStart_1205816 baseEnd_1205816 := by
    simpa [prefixWord, tailWord_1205816, baseEnd_1205816] using wordTrace_append hprefix tailTrace_1205816
  have hstable : (prefixWord ++ tailWord_1205816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205816).length < 2 ^ (prefixWord ++ tailWord_1205816).sum := by decide
  have hdescent : baseEnd_1205816 < baseStart_1205816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205821 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1205821 : Nat := 118140960795 + 1205821 * 2 ^ 59
def prefixEnd_1205821 : Nat := 4983230072969 + 3 ^ 40 * 1205821 * 2
def baseEnd_1205821 : Nat := 619165756285231953492037

theorem tailTrace_1205821 : CollatzResearch.WordTrace tailWord_1205821 prefixEnd_1205821 619165756285231953492037 := by
  unfold tailWord_1205821
  simp only [CollatzResearch.WordTrace]
  refine ⟨43979904964523929676361317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29319936643015953117574211 43979904964523929676361317)
  ·
    refine ⟨8246232180848236814317747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43979904964523929676361317 8246232180848236814317747)
    ·
      refine ⟨12369348271272355221476621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8246232180848236814317747 12369348271272355221476621)
      ·
        refine ⟨4638505601727133208053733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12369348271272355221476621 4638505601727133208053733)
        ·
          refine ⟨869719800323837476510075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4638505601727133208053733 869719800323837476510075)
          ·
            refine ⟨1304579700485756214765113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869719800323837476510075 1304579700485756214765113)
            ·
              refine ⟨978434775364317161073835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304579700485756214765113 978434775364317161073835)
              ·
                refine ⟨1467652163046475741610753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978434775364317161073835 1467652163046475741610753)
                ·
                  refine ⟨1100739122284856806208065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467652163046475741610753 1100739122284856806208065)
                  ·
                    refine ⟨825554341713642604656049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100739122284856806208065 825554341713642604656049)
                    ·
                      refine ⟨619165756285231953492037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825554341713642604656049 619165756285231953492037)
                      ·
                        rfl

theorem cell23_1205821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1205821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205821 prefixEnd_1205821 := by exact prefixLift 1205821
  have htrace : WordTrace (prefixWord ++ tailWord_1205821) baseStart_1205821 baseEnd_1205821 := by
    simpa [prefixWord, tailWord_1205821, baseEnd_1205821] using wordTrace_append hprefix tailTrace_1205821
  have hstable : (prefixWord ++ tailWord_1205821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205821).length < 2 ^ (prefixWord ++ tailWord_1205821).sum := by decide
  have hdescent : baseEnd_1205821 < baseStart_1205821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205839 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_1205839 : Nat := 118140960795 + 1205839 * 2 ^ 59
def prefixEnd_1205839 : Nat := 4983230072969 + 3 ^ 40 * 1205839 * 2
def baseEnd_1205839 : Nat := 619174998937012883066953

theorem tailTrace_1205839 : CollatzResearch.WordTrace tailWord_1205839 prefixEnd_1205839 619174998937012883066953 := by
  unfold tailWord_1205839
  simp only [CollatzResearch.WordTrace]
  refine ⟨43980561478458718750516571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29320374318972479167011047 43980561478458718750516571)
  ·
    refine ⟨65970842217688078125774857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43980561478458718750516571 65970842217688078125774857)
    ·
      refine ⟨49478131663266058594331143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65970842217688078125774857 49478131663266058594331143)
      ·
        refine ⟨74217197494899087891496715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49478131663266058594331143 74217197494899087891496715)
        ·
          refine ⟨111325796242348631837245073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74217197494899087891496715 111325796242348631837245073)
          ·
            refine ⟨83494347181761473877933805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111325796242348631837245073 83494347181761473877933805)
            ·
              refine ⟨31310380193160552704225177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83494347181761473877933805 31310380193160552704225177)
              ·
                refine ⟨23482785144870414528168883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31310380193160552704225177 23482785144870414528168883)
                ·
                  refine ⟨35224177717305621792253325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23482785144870414528168883 35224177717305621792253325)
                  ·
                    refine ⟨13209066643989608172094997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35224177717305621792253325 13209066643989608172094997)
                    ·
                      refine ⟨619174998937012883066953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13209066643989608172094997 619174998937012883066953)
                      ·
                        rfl

theorem cell23_1205839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_1205839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205839 prefixEnd_1205839 := by exact prefixLift 1205839
  have htrace : WordTrace (prefixWord ++ tailWord_1205839) baseStart_1205839 baseEnd_1205839 := by
    simpa [prefixWord, tailWord_1205839, baseEnd_1205839] using wordTrace_append hprefix tailTrace_1205839
  have hstable : (prefixWord ++ tailWord_1205839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205839).length < 2 ^ (prefixWord ++ tailWord_1205839).sum := by decide
  have hdescent : baseEnd_1205839 < baseStart_1205839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205849 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 10]
def baseStart_1205849 : Nat := 118140960795 + 1205849 * 2 ^ 59
def prefixEnd_1205849 : Nat := 4983230072969 + 3 ^ 40 * 1205849 * 2
def baseEnd_1205849 : Nat := 68797792638173093771323

theorem tailTrace_1205849 : CollatzResearch.WordTrace tailWord_1205849 prefixEnd_1205849 68797792638173093771323 := by
  unfold tailWord_1205849
  simp only [CollatzResearch.WordTrace]
  refine ⟨43980926208422490458380601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29320617472281660305587067 43980926208422490458380601)
  ·
    refine ⟨32985694656316867843785451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43980926208422490458380601 32985694656316867843785451)
    ·
      refine ⟨49478541984475301765678177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32985694656316867843785451 49478541984475301765678177)
      ·
        refine ⟨37108906488356476324258633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49478541984475301765678177 37108906488356476324258633)
        ·
          refine ⟨27831679866267357243193975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37108906488356476324258633 27831679866267357243193975)
          ·
            refine ⟨41747519799401035864790963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27831679866267357243193975 41747519799401035864790963)
            ·
              refine ⟨62621279699101553797186445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41747519799401035864790963 62621279699101553797186445)
              ·
                refine ⟨23482979887163082673944917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62621279699101553797186445 23482979887163082673944917)
                ·
                  refine ⟨68797792638173093771323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23482979887163082673944917 68797792638173093771323)
                  ·
                    rfl

theorem cell23_1205849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_1205849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205849 prefixEnd_1205849 := by exact prefixLift 1205849
  have htrace : WordTrace (prefixWord ++ tailWord_1205849) baseStart_1205849 baseEnd_1205849 := by
    simpa [prefixWord, tailWord_1205849, baseEnd_1205849] using wordTrace_append hprefix tailTrace_1205849
  have hstable : (prefixWord ++ tailWord_1205849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205849).length < 2 ^ (prefixWord ++ tailWord_1205849).sum := by decide
  have hdescent : baseEnd_1205849 < baseStart_1205849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205863 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1205863 : Nat := 118140960795 + 1205863 * 2 ^ 59
def prefixEnd_1205863 : Nat := 4983230072969 + 3 ^ 40 * 1205863 * 2
def baseEnd_1205863 : Nat := 619187322472720789166843

theorem tailTrace_1205863 : CollatzResearch.WordTrace tailWord_1205863 prefixEnd_1205863 619187322472720789166843 := by
  unfold tailWord_1205863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43981436830371770849390243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29320957886914513899593495 43981436830371770849390243)
  ·
    refine ⟨65972155245557656274085365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43981436830371770849390243 65972155245557656274085365)
    ·
      refine ⟨6184889554271030275695503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65972155245557656274085365 6184889554271030275695503)
      ·
        refine ⟨9277334331406545413543255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6184889554271030275695503 9277334331406545413543255)
        ·
          refine ⟨13916001497109818120314883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9277334331406545413543255 13916001497109818120314883)
          ·
            refine ⟨20874002245664727180472325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13916001497109818120314883 20874002245664727180472325)
            ·
              refine ⟨3913875421062136346338561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20874002245664727180472325 3913875421062136346338561)
              ·
                refine ⟨2935406565796602259753921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3913875421062136346338561 2935406565796602259753921)
                ·
                  refine ⟨2201554924347451694815441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935406565796602259753921 2201554924347451694815441)
                  ·
                    refine ⟨1651166193260588771111581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2201554924347451694815441 1651166193260588771111581)
                    ·
                      refine ⟨619187322472720789166843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1651166193260588771111581 619187322472720789166843)
                      ·
                        rfl

theorem cell23_1205863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1205863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205863 prefixEnd_1205863 := by exact prefixLift 1205863
  have htrace : WordTrace (prefixWord ++ tailWord_1205863) baseStart_1205863 baseEnd_1205863 := by
    simpa [prefixWord, tailWord_1205863, baseEnd_1205863] using wordTrace_append hprefix tailTrace_1205863
  have hstable : (prefixWord ++ tailWord_1205863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205863).length < 2 ^ (prefixWord ++ tailWord_1205863).sum := by decide
  have hdescent : baseEnd_1205863 < baseStart_1205863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205936 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_1205936 : Nat := 118140960795 + 1205936 * 2 ^ 59
def prefixEnd_1205936 : Nat := 4983230072969 + 3 ^ 40 * 1205936 * 2
def baseEnd_1205936 : Nat := 619224806560499003554007

theorem tailTrace_1205936 : CollatzResearch.WordTrace tailWord_1205936 prefixEnd_1205936 619224806560499003554007 := by
  unfold tailWord_1205936
  simp only [CollatzResearch.WordTrace]
  refine ⟨21992049679553652158398831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29322732906071536211198441 21992049679553652158398831)
  ·
    refine ⟨32988074519330478237598247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21992049679553652158398831 32988074519330478237598247)
    ·
      refine ⟨49482111778995717356397371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32988074519330478237598247 49482111778995717356397371)
      ·
        refine ⟨74223167668493576034596057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49482111778995717356397371 74223167668493576034596057)
        ·
          refine ⟨55667375751370182025947043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74223167668493576034596057 55667375751370182025947043)
          ·
            refine ⟨83501063627055273038920565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55667375751370182025947043 83501063627055273038920565)
            ·
              refine ⟨7828224715036431847398803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83501063627055273038920565 7828224715036431847398803)
              ·
                refine ⟨11742337072554647771098205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828224715036431847398803 11742337072554647771098205)
                ·
                  refine ⟨4403376402207992914161827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11742337072554647771098205 4403376402207992914161827)
                  ·
                    refine ⟨6605064603311989371242741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403376402207992914161827 6605064603311989371242741)
                    ·
                      refine ⟨619224806560499003554007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6605064603311989371242741 619224806560499003554007)
                      ·
                        rfl

theorem cell23_1205936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_1205936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205936 prefixEnd_1205936 := by exact prefixLift 1205936
  have htrace : WordTrace (prefixWord ++ tailWord_1205936) baseStart_1205936 baseEnd_1205936 := by
    simpa [prefixWord, tailWord_1205936, baseEnd_1205936] using wordTrace_append hprefix tailTrace_1205936
  have hstable : (prefixWord ++ tailWord_1205936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205936).length < 2 ^ (prefixWord ++ tailWord_1205936).sum := by decide
  have hdescent : baseEnd_1205936 < baseStart_1205936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205943 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 6]
def baseStart_1205943 : Nat := 118140960795 + 1205943 * 2 ^ 59
def prefixEnd_1205943 : Nat := 4983230072969 + 3 ^ 40 * 1205943 * 2
def baseEnd_1205943 : Nat := 206409466975026825388825

theorem tailTrace_1205943 : CollatzResearch.WordTrace tailWord_1205943 prefixEnd_1205943 206409466975026825388825 := by
  unfold tailWord_1205943
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984354670081944512302483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29322903113387963008201655 43984354670081944512302483)
  ·
    refine ⟨65976532005122916768453725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43984354670081944512302483 65976532005122916768453725)
    ·
      refine ⟨24741199501921093788170147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65976532005122916768453725 24741199501921093788170147)
      ·
        refine ⟨37111799252881640682255221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24741199501921093788170147 37111799252881640682255221)
        ·
          refine ⟨3479231179957653813961427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37111799252881640682255221 3479231179957653813961427)
          ·
            refine ⟨5218846769936480720942141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479231179957653813961427 5218846769936480720942141)
            ·
              refine ⟨1957067538726180270353303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5218846769936480720942141 1957067538726180270353303)
              ·
                refine ⟨2935601308089270405529955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957067538726180270353303 2935601308089270405529955)
                ·
                  refine ⟨4403401962133905608294933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935601308089270405529955 4403401962133905608294933)
                  ·
                    refine ⟨206409466975026825388825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4403401962133905608294933 206409466975026825388825)
                    ·
                      rfl

theorem cell23_1205943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_1205943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205943 prefixEnd_1205943 := by exact prefixLift 1205943
  have htrace : WordTrace (prefixWord ++ tailWord_1205943) baseStart_1205943 baseEnd_1205943 := by
    simpa [prefixWord, tailWord_1205943, baseEnd_1205943] using wordTrace_append hprefix tailTrace_1205943
  have hstable : (prefixWord ++ tailWord_1205943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205943).length < 2 ^ (prefixWord ++ tailWord_1205943).sum := by decide
  have hdescent : baseEnd_1205943 < baseStart_1205943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205950 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1205950 : Nat := 118140960795 + 1205950 * 2 ^ 59
def prefixEnd_1205950 : Nat := 4983230072969 + 3 ^ 40 * 1205950 * 2
def baseEnd_1205950 : Nat := 619231995289661948778943

theorem tailTrace_1205950 : CollatzResearch.WordTrace tailWord_1205950 prefixEnd_1205950 619231995289661948778943 := by
  unfold tailWord_1205950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5498076247632073088475913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29323073320704389805204869 5498076247632073088475913)
  ·
    refine ⟨4123557185724054816356935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5498076247632073088475913 4123557185724054816356935)
    ·
      refine ⟨6185335778586082224535403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123557185724054816356935 6185335778586082224535403)
      ·
        refine ⟨9278003667879123336803105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185335778586082224535403 9278003667879123336803105)
        ·
          refine ⟨6958502750909342502602329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9278003667879123336803105 6958502750909342502602329)
          ·
            refine ⟨5218877063182006876951747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6958502750909342502602329 5218877063182006876951747)
            ·
              refine ⟨7828315594773010315427621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218877063182006876951747 7828315594773010315427621)
              ·
                refine ⟨1467809174019939434142679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7828315594773010315427621 1467809174019939434142679)
                ·
                  refine ⟨2201713761029909151214019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467809174019939434142679 2201713761029909151214019)
                  ·
                    refine ⟨3302570641544863726821029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2201713761029909151214019 3302570641544863726821029)
                    ·
                      refine ⟨619231995289661948778943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3302570641544863726821029 619231995289661948778943)
                      ·
                        rfl

theorem cell23_1205950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1205950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205950 prefixEnd_1205950 := by exact prefixLift 1205950
  have htrace : WordTrace (prefixWord ++ tailWord_1205950) baseStart_1205950 baseEnd_1205950 := by
    simpa [prefixWord, tailWord_1205950, baseEnd_1205950] using wordTrace_append hprefix tailTrace_1205950
  have hstable : (prefixWord ++ tailWord_1205950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205950).length < 2 ^ (prefixWord ++ tailWord_1205950).sum := by decide
  have hdescent : baseEnd_1205950 < baseStart_1205950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205970 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1205970 : Nat := 118140960795 + 1205970 * 2 ^ 59
def prefixEnd_1205970 : Nat := 4983230072969 + 3 ^ 40 * 1205970 * 2
def baseEnd_1205970 : Nat := 619242264902751870528851

theorem tailTrace_1205970 : CollatzResearch.WordTrace tailWord_1205970 prefixEnd_1205970 619242264902751870528851 := by
  unfold tailWord_1205970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996334860246032030883841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29323559627322752082356909 10996334860246032030883841)
  ·
    refine ⟨8247251145184524023162881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10996334860246032030883841 8247251145184524023162881)
    ·
      refine ⟨6185438358888393017372161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8247251145184524023162881 6185438358888393017372161)
      ·
        refine ⟨4639078769166294763029121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185438358888393017372161 4639078769166294763029121)
        ·
          refine ⟨3479309076874721072271841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4639078769166294763029121 3479309076874721072271841)
          ·
            refine ⟨2609481807656040804203881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479309076874721072271841 2609481807656040804203881)
            ·
              refine ⟨1957111355742030603152911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609481807656040804203881 1957111355742030603152911)
              ·
                refine ⟨2935667033613045904729367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957111355742030603152911 2935667033613045904729367)
                ·
                  refine ⟨4403500550419568857094051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935667033613045904729367 4403500550419568857094051)
                  ·
                    refine ⟨6605250825629353285641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403500550419568857094051 6605250825629353285641077)
                    ·
                      refine ⟨619242264902751870528851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6605250825629353285641077 619242264902751870528851)
                      ·
                        rfl

theorem cell23_1205970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1205970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205970 prefixEnd_1205970 := by exact prefixLift 1205970
  have htrace : WordTrace (prefixWord ++ tailWord_1205970) baseStart_1205970 baseEnd_1205970 := by
    simpa [prefixWord, tailWord_1205970, baseEnd_1205970] using wordTrace_append hprefix tailTrace_1205970
  have hstable : (prefixWord ++ tailWord_1205970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205970).length < 2 ^ (prefixWord ++ tailWord_1205970).sum := by decide
  have hdescent : baseEnd_1205970 < baseStart_1205970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205993 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 7, 2]
def baseStart_1205993 : Nat := 118140960795 + 1205993 * 2 ^ 59
def prefixEnd_1205993 : Nat := 4983230072969 + 3 ^ 40 * 1205993 * 2
def baseEnd_1205993 : Nat := 619254074957805280541245

theorem tailTrace_1205993 : CollatzResearch.WordTrace tailWord_1205993 prefixEnd_1205993 619254074957805280541245 := by
  unfold tailWord_1205993
  simp only [CollatzResearch.WordTrace]
  refine ⟨43986178319900803051622633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29324118879933868701081755 43986178319900803051622633)
  ·
    refine ⟨32989633739925602288716975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43986178319900803051622633 32989633739925602288716975)
    ·
      refine ⟨49484450609888403433075463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32989633739925602288716975 49484450609888403433075463)
      ·
        refine ⟨74226675914832605149613195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49484450609888403433075463 74226675914832605149613195)
        ·
          refine ⟨111340013872248907724419793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74226675914832605149613195 111340013872248907724419793)
          ·
            refine ⟨83505010404186680793314845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111340013872248907724419793 83505010404186680793314845)
            ·
              refine ⟨31314378901570005297493067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83505010404186680793314845 31314378901570005297493067)
              ·
                refine ⟨46971568352355007946239601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31314378901570005297493067 46971568352355007946239601)
                ·
                  refine ⟨35228676264266255959679701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46971568352355007946239601 35228676264266255959679701)
                  ·
                    refine ⟨825672099943740374054993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35228676264266255959679701 825672099943740374054993)
                    ·
                      refine ⟨619254074957805280541245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825672099943740374054993 619254074957805280541245)
                      ·
                        rfl

theorem cell23_1205993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7, 2].length) (baseStart_1205993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1205993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1205993 prefixEnd_1205993 := by exact prefixLift 1205993
  have htrace : WordTrace (prefixWord ++ tailWord_1205993) baseStart_1205993 baseEnd_1205993 := by
    simpa [prefixWord, tailWord_1205993, baseEnd_1205993] using wordTrace_append hprefix tailTrace_1205993
  have hstable : (prefixWord ++ tailWord_1205993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205993).length < 2 ^ (prefixWord ++ tailWord_1205993).sum := by decide
  have hdescent : baseEnd_1205993 < baseStart_1205993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206004 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1206004 : Nat := 118140960795 + 1206004 * 2 ^ 59
def prefixEnd_1206004 : Nat := 4983230072969 + 3 ^ 40 * 1206004 * 2
def baseEnd_1206004 : Nat := 619259723245004737503695

theorem tailTrace_1206004 : CollatzResearch.WordTrace tailWord_1206004 prefixEnd_1206004 619259723245004737503695 := by
  unfold tailWord_1206004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21993289761430475965136533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29324386348573967953515377 21993289761430475965136533)
  ·
    refine ⟨1030935457567053560865775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21993289761430475965136533 1030935457567053560865775)
    ·
      refine ⟨1546403186350580341298663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030935457567053560865775 1546403186350580341298663)
      ·
        refine ⟨2319604779525870511947995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546403186350580341298663 2319604779525870511947995)
        ·
          refine ⟨3479407169288805767921993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319604779525870511947995 3479407169288805767921993)
          ·
            refine ⟨2609555376966604325941495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479407169288805767921993 2609555376966604325941495)
            ·
              refine ⟨3914333065449906488912243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609555376966604325941495 3914333065449906488912243)
              ·
                refine ⟨5871499598174859733368365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914333065449906488912243 5871499598174859733368365)
                ·
                  refine ⟨2201812349315572400013137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5871499598174859733368365 2201812349315572400013137)
                  ·
                    refine ⟨1651359261986679300009853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2201812349315572400013137 1651359261986679300009853)
                    ·
                      refine ⟨619259723245004737503695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1651359261986679300009853 619259723245004737503695)
                      ·
                        rfl

theorem cell23_1206004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1206004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206004 prefixEnd_1206004 := by exact prefixLift 1206004
  have htrace : WordTrace (prefixWord ++ tailWord_1206004) baseStart_1206004 baseEnd_1206004 := by
    simpa [prefixWord, tailWord_1206004, baseEnd_1206004] using wordTrace_append hprefix tailTrace_1206004
  have hstable : (prefixWord ++ tailWord_1206004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206004).length < 2 ^ (prefixWord ++ tailWord_1206004).sum := by decide
  have hdescent : baseEnd_1206004 < baseStart_1206004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206016 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_1206016 : Nat := 118140960795 + 1206016 * 2 ^ 59
def prefixEnd_1206016 : Nat := 4983230072969 + 3 ^ 40 * 1206016 * 2
def baseEnd_1206016 : Nat := 206421961670952896851213

theorem tailTrace_1206016 : CollatzResearch.WordTrace tailWord_1206016 prefixEnd_1206016 206421961670952896851213 := by
  unfold tailWord_1206016
  simp only [CollatzResearch.WordTrace]
  refine ⟨21993508599408738989854951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29324678132544985319806601 21993508599408738989854951)
  ·
    refine ⟨32990262899113108484782427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21993508599408738989854951 32990262899113108484782427)
    ·
      refine ⟨49485394348669662727173641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32990262899113108484782427 49485394348669662727173641)
      ·
        refine ⟨37114045761502247045380231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49485394348669662727173641 37114045761502247045380231)
        ·
          refine ⟨55671068642253370568070347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37114045761502247045380231 55671068642253370568070347)
          ·
            refine ⟨83506602963380055852105521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55671068642253370568070347 83506602963380055852105521)
            ·
              refine ⟨62629952222535041889079141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83506602963380055852105521 62629952222535041889079141)
              ·
                refine ⟨11743116041725320354202339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62629952222535041889079141 11743116041725320354202339)
                ·
                  refine ⟨17614674062587980531303509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11743116041725320354202339 17614674062587980531303509)
                  ·
                    refine ⟨206421961670952896851213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17614674062587980531303509 206421961670952896851213)
                    ·
                      rfl

theorem cell23_1206016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_1206016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206016 prefixEnd_1206016 := by exact prefixLift 1206016
  have htrace : WordTrace (prefixWord ++ tailWord_1206016) baseStart_1206016 baseEnd_1206016 := by
    simpa [prefixWord, tailWord_1206016, baseEnd_1206016] using wordTrace_append hprefix tailTrace_1206016
  have hstable : (prefixWord ++ tailWord_1206016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206016).length < 2 ^ (prefixWord ++ tailWord_1206016).sum := by decide
  have hdescent : baseEnd_1206016 < baseStart_1206016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206029 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1206029 : Nat := 118140960795 + 1206029 * 2 ^ 59
def prefixEnd_1206029 : Nat := 4983230072969 + 3 ^ 40 * 1206029 * 2
def baseEnd_1206029 : Nat := 619272560261367139691081

theorem tailTrace_1206029 : CollatzResearch.WordTrace tailWord_1206029 prefixEnd_1206029 619272560261367139691081 := by
  unfold tailWord_1206029
  simp only [CollatzResearch.WordTrace]
  refine ⟨43987491347770381199933141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29324994231846920799955427 43987491347770381199933141)
  ·
    refine ⟨1030956828463368309373433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43987491347770381199933141 1030956828463368309373433)
    ·
      refine ⟨773217621347526232030075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030956828463368309373433 773217621347526232030075)
      ·
        refine ⟨1159826432021289348045113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773217621347526232030075 1159826432021289348045113)
        ·
          refine ⟨869869824015967011033835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159826432021289348045113 869869824015967011033835)
          ·
            refine ⟨1304804736023950516550753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869869824015967011033835 1304804736023950516550753)
            ·
              refine ⟨978603552017962887413065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304804736023950516550753 978603552017962887413065)
              ·
                refine ⟨733952664013472165559799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978603552017962887413065 733952664013472165559799)
                ·
                  refine ⟨1100928996020208248339699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733952664013472165559799 1100928996020208248339699)
                  ·
                    refine ⟨1651393494030312372509549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100928996020208248339699 1651393494030312372509549)
                    ·
                      refine ⟨619272560261367139691081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1651393494030312372509549 619272560261367139691081)
                      ·
                        rfl

theorem cell23_1206029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1206029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206029 prefixEnd_1206029 := by exact prefixLift 1206029
  have htrace : WordTrace (prefixWord ++ tailWord_1206029) baseStart_1206029 baseEnd_1206029 := by
    simpa [prefixWord, tailWord_1206029, baseEnd_1206029] using wordTrace_append hprefix tailTrace_1206029
  have hstable : (prefixWord ++ tailWord_1206029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206029).length < 2 ^ (prefixWord ++ tailWord_1206029).sum := by decide
  have hdescent : baseEnd_1206029 < baseStart_1206029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206034 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1206034 : Nat := 118140960795 + 1206034 * 2 ^ 59
def prefixEnd_1206034 : Nat := 4983230072969 + 3 ^ 40 * 1206034 * 2
def baseEnd_1206034 : Nat := 619275127664639620128557

theorem tailTrace_1206034 : CollatzResearch.WordTrace tailWord_1206034 prefixEnd_1206034 619275127664639620128557 := by
  unfold tailWord_1206034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996918428188066763466289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29325115808501511369243437 10996918428188066763466289)
  ·
    refine ⟨8247688821141050072599717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10996918428188066763466289 8247688821141050072599717)
    ·
      refine ⟨1546441653963946888612447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8247688821141050072599717 1546441653963946888612447)
      ·
        refine ⟨2319662480945920332918671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546441653963946888612447 2319662480945920332918671)
        ·
          refine ⟨3479493721418880499378007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319662480945920332918671 3479493721418880499378007)
          ·
            refine ⟨5219240582128320749067011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479493721418880499378007 5219240582128320749067011)
            ·
              refine ⟨7828860873192481123600517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219240582128320749067011 7828860873192481123600517)
              ·
                refine ⟨1467911413723590210675097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7828860873192481123600517 1467911413723590210675097)
                ·
                  refine ⟨1100933560292692658006323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467911413723590210675097 1100933560292692658006323)
                  ·
                    refine ⟨1651400340439038987009485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100933560292692658006323 1651400340439038987009485)
                    ·
                      refine ⟨619275127664639620128557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1651400340439038987009485 619275127664639620128557)
                      ·
                        rfl

theorem cell23_1206034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1206034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206034 prefixEnd_1206034 := by exact prefixLift 1206034
  have htrace : WordTrace (prefixWord ++ tailWord_1206034) baseStart_1206034 baseEnd_1206034 := by
    simpa [prefixWord, tailWord_1206034, baseEnd_1206034] using wordTrace_append hprefix tailTrace_1206034
  have hstable : (prefixWord ++ tailWord_1206034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206034).length < 2 ^ (prefixWord ++ tailWord_1206034).sum := by decide
  have hdescent : baseEnd_1206034 < baseStart_1206034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206053 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_1206053 : Nat := 118140960795 + 1206053 * 2 ^ 59
def prefixEnd_1206053 : Nat := 4983230072969 + 3 ^ 40 * 1206053 * 2
def baseEnd_1206053 : Nat := 619284883797075045790969

theorem tailTrace_1206053 : CollatzResearch.WordTrace tailWord_1206053 prefixEnd_1206053 619284883797075045790969 := by
  unfold tailWord_1206053
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988366699683433298806813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29325577799788955532537875 43988366699683433298806813)
  ·
    refine ⟨16495637512381287487052555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43988366699683433298806813 16495637512381287487052555)
    ·
      refine ⟨24743456268571931230578833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16495637512381287487052555 24743456268571931230578833)
      ·
        refine ⟨18557592201428948422934125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24743456268571931230578833 18557592201428948422934125)
        ·
          refine ⟨6959097075535855658600297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18557592201428948422934125 6959097075535855658600297)
          ·
            refine ⟨5219322806651891743950223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6959097075535855658600297 5219322806651891743950223)
            ·
              refine ⟨7828984209977837615925335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219322806651891743950223 7828984209977837615925335)
              ·
                refine ⟨11743476314966756423888003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828984209977837615925335 11743476314966756423888003)
                ·
                  refine ⟨17615214472450134635832005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11743476314966756423888003 17615214472450134635832005)
                  ·
                    refine ⟨3302852713584400244218501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17615214472450134635832005 3302852713584400244218501)
                    ·
                      refine ⟨619284883797075045790969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3302852713584400244218501 619284883797075045790969)
                      ·
                        rfl

theorem cell23_1206053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_1206053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206053 prefixEnd_1206053 := by exact prefixLift 1206053
  have htrace : WordTrace (prefixWord ++ tailWord_1206053) baseStart_1206053 baseEnd_1206053 := by
    simpa [prefixWord, tailWord_1206053, baseEnd_1206053] using wordTrace_append hprefix tailTrace_1206053
  have hstable : (prefixWord ++ tailWord_1206053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206053).length < 2 ^ (prefixWord ++ tailWord_1206053).sum := by decide
  have hdescent : baseEnd_1206053 < baseStart_1206053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206108 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1206108 : Nat := 118140960795 + 1206108 * 2 ^ 59
def prefixEnd_1206108 : Nat := 4983230072969 + 3 ^ 40 * 1206108 * 2
def baseEnd_1206108 : Nat := 619313125233072330603217

theorem tailTrace_1206108 : CollatzResearch.WordTrace tailWord_1206108 prefixEnd_1206108 619313125233072330603217 := by
  unfold tailWord_1206108
  simp only [CollatzResearch.WordTrace]
  refine ⟨21995186357242088846029489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29326915142989451794705985 21995186357242088846029489)
  ·
    refine ⟨16496389767931566634522117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21995186357242088846029489 16496389767931566634522117)
    ·
      refine ⟨3093073081487168743972897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16496389767931566634522117 3093073081487168743972897)
      ·
        refine ⟨2319804811115376557979673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093073081487168743972897 2319804811115376557979673)
        ·
          refine ⟨1739853608336532418484755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319804811115376557979673 1739853608336532418484755)
          ·
            refine ⟨2609780412504798627727133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739853608336532418484755 2609780412504798627727133)
            ·
              refine ⟨978667654689299485397675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2609780412504798627727133 978667654689299485397675)
              ·
                refine ⟨1468001482033949228096513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978667654689299485397675 1468001482033949228096513)
                ·
                  refine ⟨1101001111525461921072385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468001482033949228096513 1101001111525461921072385)
                  ·
                    refine ⟨825750833644096440804289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101001111525461921072385 825750833644096440804289)
                    ·
                      refine ⟨619313125233072330603217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825750833644096440804289 619313125233072330603217)
                      ·
                        rfl

theorem cell23_1206108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1206108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206108 prefixEnd_1206108 := by exact prefixLift 1206108
  have htrace : WordTrace (prefixWord ++ tailWord_1206108) baseStart_1206108 baseEnd_1206108 := by
    simpa [prefixWord, tailWord_1206108, baseEnd_1206108] using wordTrace_append hprefix tailTrace_1206108
  have hstable : (prefixWord ++ tailWord_1206108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206108).length < 2 ^ (prefixWord ++ tailWord_1206108).sum := by decide
  have hdescent : baseEnd_1206108 < baseStart_1206108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206113 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1206113 : Nat := 118140960795 + 1206113 * 2 ^ 59
def prefixEnd_1206113 : Nat := 4983230072969 + 3 ^ 40 * 1206113 * 2
def baseEnd_1206113 : Nat := 619315692636344811040693

theorem tailTrace_1206113 : CollatzResearch.WordTrace tailWord_1206113 prefixEnd_1206113 619315692636344811040693 := by
  unfold tailWord_1206113
  simp only [CollatzResearch.WordTrace]
  refine ⟨43990555079466063545990993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29327036719644042363993995 43990555079466063545990993)
  ·
    refine ⟨32992916309599547659493245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43990555079466063545990993 32992916309599547659493245)
    ·
      refine ⟨12372343616099830372309967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32992916309599547659493245 12372343616099830372309967)
      ·
        refine ⟨18558515424149745558464951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12372343616099830372309967 18558515424149745558464951)
        ·
          refine ⟨27837773136224618337697427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18558515424149745558464951 27837773136224618337697427)
          ·
            refine ⟨41756659704336927506546141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27837773136224618337697427 41756659704336927506546141)
            ·
              refine ⟨15658747389126347814954803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41756659704336927506546141 15658747389126347814954803)
              ·
                refine ⟨23488121083689521722432205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15658747389126347814954803 23488121083689521722432205)
                ·
                  refine ⟨8808045406383570645912077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23488121083689521722432205 8808045406383570645912077)
                  ·
                    refine ⟨3303017027393838992217029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8808045406383570645912077 3303017027393838992217029)
                    ·
                      refine ⟨619315692636344811040693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3303017027393838992217029 619315692636344811040693)
                      ·
                        rfl

theorem cell23_1206113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1206113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206113 prefixEnd_1206113 := by exact prefixLift 1206113
  have htrace : WordTrace (prefixWord ++ tailWord_1206113) baseStart_1206113 baseEnd_1206113 := by
    simpa [prefixWord, tailWord_1206113, baseEnd_1206113] using wordTrace_append hprefix tailTrace_1206113
  have hstable : (prefixWord ++ tailWord_1206113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206113).length < 2 ^ (prefixWord ++ tailWord_1206113).sum := by decide
  have hdescent : baseEnd_1206113 < baseStart_1206113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206130 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1206130 : Nat := 118140960795 + 1206130 * 2 ^ 59
def prefixEnd_1206130 : Nat := 4983230072969 + 3 ^ 40 * 1206130 * 2
def baseEnd_1206130 : Nat := 619324421807471244528115

theorem tailTrace_1206130 : CollatzResearch.WordTrace tailWord_1206130 prefixEnd_1206130 619324421807471244528115 := by
  unfold tailWord_1206130
  simp only [CollatzResearch.WordTrace]
  refine ⟨10997793780101118862339961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29327450080269650299573229 10997793780101118862339961)
  ·
    refine ⟨8248345335075839146754971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10997793780101118862339961 8248345335075839146754971)
    ·
      refine ⟨12372518002613758720132457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248345335075839146754971 12372518002613758720132457)
      ·
        refine ⟨9279388501960319040099343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12372518002613758720132457 9279388501960319040099343)
        ·
          refine ⟨13919082752940478560149015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9279388501960319040099343 13919082752940478560149015)
          ·
            refine ⟨20878624129410717840223523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13919082752940478560149015 20878624129410717840223523)
            ·
              refine ⟨31317936194116076760335285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20878624129410717840223523 31317936194116076760335285)
              ·
                refine ⟨2936056518198382196281433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31317936194116076760335285 2936056518198382196281433)
                ·
                  refine ⟨2202042388648786647211075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936056518198382196281433 2202042388648786647211075)
                  ·
                    refine ⟨3303063582973179970816613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202042388648786647211075 3303063582973179970816613)
                    ·
                      refine ⟨619324421807471244528115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3303063582973179970816613 619324421807471244528115)
                      ·
                        rfl

theorem cell23_1206130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1206130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206130 prefixEnd_1206130 := by exact prefixLift 1206130
  have htrace : WordTrace (prefixWord ++ tailWord_1206130) baseStart_1206130 baseEnd_1206130 := by
    simpa [prefixWord, tailWord_1206130, baseEnd_1206130] using wordTrace_append hprefix tailTrace_1206130
  have hstable : (prefixWord ++ tailWord_1206130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206130).length < 2 ^ (prefixWord ++ tailWord_1206130).sum := by decide
  have hdescent : baseEnd_1206130 < baseStart_1206130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206153 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 8]
def baseStart_1206153 : Nat := 118140960795 + 1206153 * 2 ^ 59
def prefixEnd_1206153 : Nat := 4983230072969 + 3 ^ 40 * 1206153 * 2
def baseEnd_1206153 : Nat := 68815136873613850504501

theorem tailTrace_1206153 : CollatzResearch.WordTrace tailWord_1206153 prefixEnd_1206153 68815136873613850504501 := by
  unfold tailWord_1206153
  simp only [CollatzResearch.WordTrace]
  refine ⟨43992013999321150377447113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29328009332880766918298075 43992013999321150377447113)
  ·
    refine ⟨32994010499490862783085335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43992013999321150377447113 32994010499490862783085335)
    ·
      refine ⟨49491015749236294174628003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32994010499490862783085335 49491015749236294174628003)
      ·
        refine ⟨74236523623854441261942005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49491015749236294174628003 74236523623854441261942005)
        ·
          refine ⟨6959674089736353868307063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74236523623854441261942005 6959674089736353868307063)
          ·
            refine ⟨10439511134604530802460595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959674089736353868307063 10439511134604530802460595)
            ·
              refine ⟨15659266701906796203690893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439511134604530802460595 15659266701906796203690893)
              ·
                refine ⟨5872225013215048576384085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15659266701906796203690893 5872225013215048576384085)
                ·
                  refine ⟨68815136873613850504501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5872225013215048576384085 68815136873613850504501)
                  ·
                    rfl

theorem cell23_1206153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_1206153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206153 prefixEnd_1206153 := by exact prefixLift 1206153
  have htrace : WordTrace (prefixWord ++ tailWord_1206153) baseStart_1206153 baseEnd_1206153 := by
    simpa [prefixWord, tailWord_1206153, baseEnd_1206153] using wordTrace_append hprefix tailTrace_1206153
  have hstable : (prefixWord ++ tailWord_1206153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206153).length < 2 ^ (prefixWord ++ tailWord_1206153).sum := by decide
  have hdescent : baseEnd_1206153 < baseStart_1206153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206204 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 6]
def baseStart_1206204 : Nat := 118140960795 + 1206204 * 2 ^ 59
def prefixEnd_1206204 : Nat := 4983230072969 + 3 ^ 40 * 1206204 * 2
def baseEnd_1206204 : Nat := 68818046597322661666975

theorem tailTrace_1206204 : CollatzResearch.WordTrace tailWord_1206204 prefixEnd_1206204 68818046597322661666975 := by
  unfold tailWord_1206204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21996937061068193043776833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29329249414757590725035777 21996937061068193043776833)
  ·
    refine ⟨16497702795801144782832625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21996937061068193043776833 16497702795801144782832625)
    ·
      refine ⟨12373277096850858587124469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16497702795801144782832625 12373277096850858587124469)
      ·
        refine ⟨1159994727829767992542919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12373277096850858587124469 1159994727829767992542919)
        ·
          refine ⟨1739992091744651988814379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159994727829767992542919 1739992091744651988814379)
          ·
            refine ⟨2609988137616977983221569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739992091744651988814379 2609988137616977983221569)
            ·
              refine ⟨1957491103212733487416177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609988137616977983221569 1957491103212733487416177)
              ·
                refine ⟨1468118327409550115562133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957491103212733487416177 1468118327409550115562133)
                ·
                  refine ⟨68818046597322661666975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1468118327409550115562133 68818046597322661666975)
                  ·
                    rfl

theorem cell23_1206204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_1206204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206204 prefixEnd_1206204 := by exact prefixLift 1206204
  have htrace : WordTrace (prefixWord ++ tailWord_1206204) baseStart_1206204 baseEnd_1206204 := by
    simpa [prefixWord, tailWord_1206204, baseEnd_1206204] using wordTrace_append hprefix tailTrace_1206204
  have hstable : (prefixWord ++ tailWord_1206204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206204).length < 2 ^ (prefixWord ++ tailWord_1206204).sum := by decide
  have hdescent : baseEnd_1206204 < baseStart_1206204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206207 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 2, 3, 2]
def baseStart_1206207 : Nat := 118140960795 + 1206207 * 2 ^ 59
def prefixEnd_1206207 : Nat := 4983230072969 + 3 ^ 40 * 1206207 * 2
def baseEnd_1206207 : Nat := 619363959817867443265261

theorem tailTrace_1206207 : CollatzResearch.WordTrace tailWord_1206207 prefixEnd_1206207 619363959817867443265261 := by
  unfold tailWord_1206207
  simp only [CollatzResearch.WordTrace]
  refine ⟨43993983541125517599912875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29329322360750345066608583 43993983541125517599912875)
  ·
    refine ⟨65990975311688276399869313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43993983541125517599912875 65990975311688276399869313)
    ·
      refine ⟨49493231483766207299901985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65990975311688276399869313 49493231483766207299901985)
      ·
        refine ⟨37119923612824655474926489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49493231483766207299901985 37119923612824655474926489)
        ·
          refine ⟨27839942709618491606194867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37119923612824655474926489 27839942709618491606194867)
          ·
            refine ⟨41759914064427737409292301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27839942709618491606194867 41759914064427737409292301)
            ·
              refine ⟨15659967774160401528484613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41759914064427737409292301 15659967774160401528484613)
              ·
                refine ⟨2936243957655075286590865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15659967774160401528484613 2936243957655075286590865)
                ·
                  refine ⟨2202182968241306464943149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936243957655075286590865 2202182968241306464943149)
                  ·
                    refine ⟨825818613090489924353681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202182968241306464943149 825818613090489924353681)
                    ·
                      refine ⟨619363959817867443265261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825818613090489924353681 619363959817867443265261)
                      ·
                        rfl

theorem cell23_1206207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_1206207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206207 prefixEnd_1206207 := by exact prefixLift 1206207
  have htrace : WordTrace (prefixWord ++ tailWord_1206207) baseStart_1206207 baseEnd_1206207 := by
    simpa [prefixWord, tailWord_1206207, baseEnd_1206207] using wordTrace_append hprefix tailTrace_1206207
  have hstable : (prefixWord ++ tailWord_1206207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206207).length < 2 ^ (prefixWord ++ tailWord_1206207).sum := by decide
  have hdescent : baseEnd_1206207 < baseStart_1206207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206254 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1206254 : Nat := 118140960795 + 1206254 * 2 ^ 59
def prefixEnd_1206254 : Nat := 4983230072969 + 3 ^ 40 * 1206254 * 2
def baseEnd_1206254 : Nat := 619388093408628759377545

theorem tailTrace_1206254 : CollatzResearch.WordTrace tailWord_1206254 prefixEnd_1206254 619388093408628759377545 := by
  unfold tailWord_1206254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499462221494405578359227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29330465181303496417915877 5499462221494405578359227)
  ·
    refine ⟨8249193332241608367538841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5499462221494405578359227 8249193332241608367538841)
    ·
      refine ⟨6186894999181206275654131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8249193332241608367538841 6186894999181206275654131)
      ·
        refine ⟨9280342498771809413481197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6186894999181206275654131 9280342498771809413481197)
        ·
          refine ⟨3480128437039428530055449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9280342498771809413481197 3480128437039428530055449)
          ·
            refine ⟨2610096327779571397541587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480128437039428530055449 2610096327779571397541587)
            ·
              refine ⟨3915144491669357096312381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610096327779571397541587 3915144491669357096312381)
              ·
                refine ⟨1468179184376008911117143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3915144491669357096312381 1468179184376008911117143)
                ·
                  refine ⟨2202268776564013366675715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468179184376008911117143 2202268776564013366675715)
                  ·
                    refine ⟨3303403164846020050013573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202268776564013366675715 3303403164846020050013573)
                    ·
                      refine ⟨619388093408628759377545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3303403164846020050013573 619388093408628759377545)
                      ·
                        rfl

theorem cell23_1206254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1206254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206254 prefixEnd_1206254 := by exact prefixLift 1206254
  have htrace : WordTrace (prefixWord ++ tailWord_1206254) baseStart_1206254 baseEnd_1206254 := by
    simpa [prefixWord, tailWord_1206254, baseEnd_1206254] using wordTrace_append hprefix tailTrace_1206254
  have hstable : (prefixWord ++ tailWord_1206254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206254).length < 2 ^ (prefixWord ++ tailWord_1206254).sum := by decide
  have hdescent : baseEnd_1206254 < baseStart_1206254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206305 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1206305 : Nat := 118140960795 + 1206305 * 2 ^ 59
def prefixEnd_1206305 : Nat := 4983230072969 + 3 ^ 40 * 1206305 * 2
def baseEnd_1206305 : Nat := 619414280922008059839811

theorem tailTrace_1206305 : CollatzResearch.WordTrace tailWord_1206305 prefixEnd_1206305 619414280922008059839811 := by
  unfold tailWord_1206305
  simp only [CollatzResearch.WordTrace]
  refine ⟨43997557894770480336980369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29331705263180320224653579 43997557894770480336980369)
  ·
    refine ⟨32998168421077860252735277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43997557894770480336980369 32998168421077860252735277)
    ·
      refine ⟨12374313157904197594775729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32998168421077860252735277 12374313157904197594775729)
      ·
        refine ⟨9280734868428148196081797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12374313157904197594775729 9280734868428148196081797)
        ·
          refine ⟨1740137787830277786765337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9280734868428148196081797 1740137787830277786765337)
          ·
            refine ⟨1305103340872708340074003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740137787830277786765337 1305103340872708340074003)
            ·
              refine ⟨1957655011309062510111005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305103340872708340074003 1957655011309062510111005)
              ·
                refine ⟨734120629240898441291627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1957655011309062510111005 734120629240898441291627)
                ·
                  refine ⟨1101180943861347661937441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734120629240898441291627 1101180943861347661937441)
                  ·
                    refine ⟨825885707896010746453081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101180943861347661937441 825885707896010746453081)
                    ·
                      refine ⟨619414280922008059839811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825885707896010746453081 619414280922008059839811)
                      ·
                        rfl

theorem cell23_1206305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1206305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206305 prefixEnd_1206305 := by exact prefixLift 1206305
  have htrace : WordTrace (prefixWord ++ tailWord_1206305) baseStart_1206305 baseEnd_1206305 := by
    simpa [prefixWord, tailWord_1206305, baseEnd_1206305] using wordTrace_append hprefix tailTrace_1206305
  have hstable : (prefixWord ++ tailWord_1206305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206305).length < 2 ^ (prefixWord ++ tailWord_1206305).sum := by decide
  have hdescent : baseEnd_1206305 < baseStart_1206305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206330 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1206330 : Nat := 118140960795 + 1206330 * 2 ^ 59
def prefixEnd_1206330 : Nat := 4983230072969 + 3 ^ 40 * 1206330 * 2
def baseEnd_1206330 : Nat := 619427117938370462027195

theorem tailTrace_1206330 : CollatzResearch.WordTrace tailWord_1206330 prefixEnd_1206330 619427117938370462027195 := by
  unfold tailWord_1206330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999617429919977401660111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29332313146453273071093629 10999617429919977401660111)
  ·
    refine ⟨16499426144879966102490167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10999617429919977401660111 16499426144879966102490167)
    ·
      refine ⟨24749139217319949153735251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16499426144879966102490167 24749139217319949153735251)
      ·
        refine ⟨37123708825979923730602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24749139217319949153735251 37123708825979923730602877)
        ·
          refine ⟨13921390809742471398976079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37123708825979923730602877 13921390809742471398976079)
          ·
            refine ⟨20882086214613707098464119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13921390809742471398976079 20882086214613707098464119)
            ·
              refine ⟨31323129321920560647696179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20882086214613707098464119 31323129321920560647696179)
              ·
                refine ⟨46984693982880840971544269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31323129321920560647696179 46984693982880840971544269)
                ·
                  refine ⟨17619260243580315364329101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46984693982880840971544269 17619260243580315364329101)
                  ·
                    refine ⟨6607222591342618261623413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17619260243580315364329101 6607222591342618261623413)
                    ·
                      refine ⟨619427117938370462027195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6607222591342618261623413 619427117938370462027195)
                      ·
                        rfl

theorem cell23_1206330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1206330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206330 prefixEnd_1206330 := by exact prefixLift 1206330
  have htrace : WordTrace (prefixWord ++ tailWord_1206330) baseStart_1206330 baseEnd_1206330 := by
    simpa [prefixWord, tailWord_1206330, baseEnd_1206330] using wordTrace_append hprefix tailTrace_1206330
  have hstable : (prefixWord ++ tailWord_1206330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206330).length < 2 ^ (prefixWord ++ tailWord_1206330).sum := by decide
  have hdescent : baseEnd_1206330 < baseStart_1206330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206344 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_1206344 : Nat := 118140960795 + 1206344 * 2 ^ 59
def prefixEnd_1206344 : Nat := 4983230072969 + 3 ^ 40 * 1206344 * 2
def baseEnd_1206344 : Nat := 619434306667533407252131

theorem tailTrace_1206344 : CollatzResearch.WordTrace tailWord_1206344 prefixEnd_1206344 619434306667533407252131 := by
  unfold tailWord_1206344
  simp only [CollatzResearch.WordTrace]
  refine ⟨21999490170814594998825043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29332653561086126665100057 21999490170814594998825043)
  ·
    refine ⟨32999235256221892498237565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21999490170814594998825043 32999235256221892498237565)
    ·
      refine ⟨12374713221083209686839087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32999235256221892498237565 12374713221083209686839087)
      ·
        refine ⟨18562069831624814530258631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12374713221083209686839087 18562069831624814530258631)
        ·
          refine ⟨27843104747437221795387947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562069831624814530258631 27843104747437221795387947)
          ·
            refine ⟨41764657121155832693081921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27843104747437221795387947 41764657121155832693081921)
            ·
              refine ⟨31323492840866874519811441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41764657121155832693081921 31323492840866874519811441)
              ·
                refine ⟨23492619630650155889858581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31323492840866874519811441 23492619630650155889858581)
                ·
                  refine ⟨1101216545186726057337121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23492619630650155889858581 1101216545186726057337121)
                  ·
                    refine ⟨825912408890044543002841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101216545186726057337121 825912408890044543002841)
                    ·
                      refine ⟨619434306667533407252131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825912408890044543002841 619434306667533407252131)
                      ·
                        rfl

theorem cell23_1206344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_1206344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206344 prefixEnd_1206344 := by exact prefixLift 1206344
  have htrace : WordTrace (prefixWord ++ tailWord_1206344) baseStart_1206344 baseEnd_1206344 := by
    simpa [prefixWord, tailWord_1206344, baseEnd_1206344] using wordTrace_append hprefix tailTrace_1206344
  have hstable : (prefixWord ++ tailWord_1206344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206344).length < 2 ^ (prefixWord ++ tailWord_1206344).sum := by decide
  have hdescent : baseEnd_1206344 < baseStart_1206344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206365 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1206365 : Nat := 118140960795 + 1206365 * 2 ^ 59
def prefixEnd_1206365 : Nat := 4983230072969 + 3 ^ 40 * 1206365 * 2
def baseEnd_1206365 : Nat := 619445089761277825089535

theorem tailTrace_1206365 : CollatzResearch.WordTrace tailWord_1206365 prefixEnd_1206365 619445089761277825089535 := by
  unfold tailWord_1206365
  simp only [CollatzResearch.WordTrace]
  refine ⟨43999746274553110584164549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29333164183035407056109699 43999746274553110584164549)
  ·
    refine ⟨8249952426478708234530853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43999746274553110584164549 8249952426478708234530853)
    ·
      refine ⟨1546866079964757793974535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8249952426478708234530853 1546866079964757793974535)
      ·
        refine ⟨2320299119947136690961803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546866079964757793974535 2320299119947136690961803)
        ·
          refine ⟨3480448679920705036442705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320299119947136690961803 3480448679920705036442705)
          ·
            refine ⟨2610336509940528777332029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480448679920705036442705 2610336509940528777332029)
            ·
              refine ⟨978876191227698291499511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2610336509940528777332029 978876191227698291499511)
              ·
                refine ⟨1468314286841547437249267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978876191227698291499511 1468314286841547437249267)
                ·
                  refine ⟨2202471430262321155873901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468314286841547437249267 2202471430262321155873901)
                  ·
                    refine ⟨825926786348370433452713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202471430262321155873901 825926786348370433452713)
                    ·
                      refine ⟨619445089761277825089535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825926786348370433452713 619445089761277825089535)
                      ·
                        rfl

theorem cell23_1206365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1206365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206365 prefixEnd_1206365 := by exact prefixLift 1206365
  have htrace : WordTrace (prefixWord ++ tailWord_1206365) baseStart_1206365 baseEnd_1206365 := by
    simpa [prefixWord, tailWord_1206365, baseEnd_1206365] using wordTrace_append hprefix tailTrace_1206365
  have hstable : (prefixWord ++ tailWord_1206365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206365).length < 2 ^ (prefixWord ++ tailWord_1206365).sum := by decide
  have hdescent : baseEnd_1206365 < baseStart_1206365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206377 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_1206377 : Nat := 118140960795 + 1206377 * 2 ^ 59
def prefixEnd_1206377 : Nat := 4983230072969 + 3 ^ 40 * 1206377 * 2
def baseEnd_1206377 : Nat := 619451251529131778139479

theorem tailTrace_1206377 : CollatzResearch.WordTrace tailWord_1206377 prefixEnd_1206377 619451251529131778139479 := by
  unfold tailWord_1206377
  simp only [CollatzResearch.WordTrace]
  refine ⟨44000183950509636633601385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29333455967006424422400923 44000183950509636633601385)
  ·
    refine ⟨33000137962882227475201039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44000183950509636633601385 33000137962882227475201039)
    ·
      refine ⟨49500206944323341212801559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33000137962882227475201039 49500206944323341212801559)
      ·
        refine ⟨74250310416485011819202339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49500206944323341212801559 74250310416485011819202339)
        ·
          refine ⟨111375465624727517728803509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74250310416485011819202339 111375465624727517728803509)
          ·
            refine ⟨10441449902318204787075329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111375465624727517728803509 10441449902318204787075329)
            ·
              refine ⟨7831087426738653590306497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10441449902318204787075329 7831087426738653590306497)
              ·
                refine ⟨5873315570053990192729873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831087426738653590306497 5873315570053990192729873)
                ·
                  refine ⟨4404986677540492644547405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873315570053990192729873 4404986677540492644547405)
                  ·
                    refine ⟨1651870004077684741705277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4404986677540492644547405 1651870004077684741705277)
                    ·
                      refine ⟨619451251529131778139479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1651870004077684741705277 619451251529131778139479)
                      ·
                        rfl

theorem cell23_1206377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_1206377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206377 prefixEnd_1206377 := by exact prefixLift 1206377
  have htrace : WordTrace (prefixWord ++ tailWord_1206377) baseStart_1206377 baseEnd_1206377 := by
    simpa [prefixWord, tailWord_1206377, baseEnd_1206377] using wordTrace_append hprefix tailTrace_1206377
  have hstable : (prefixWord ++ tailWord_1206377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206377).length < 2 ^ (prefixWord ++ tailWord_1206377).sum := by decide
  have hdescent : baseEnd_1206377 < baseStart_1206377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206384 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 5]
def baseStart_1206384 : Nat := 118140960795 + 1206384 * 2 ^ 59
def prefixEnd_1206384 : Nat := 4983230072969 + 3 ^ 40 * 1206384 * 2
def baseEnd_1206384 : Nat := 68828316210412583416883

theorem tailTrace_1206384 : CollatzResearch.WordTrace tailWord_1206384 prefixEnd_1206384 68828316210412583416883 := by
  unfold tailWord_1206384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000219630742138414553103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29333626174322851219404137 22000219630742138414553103)
  ·
    refine ⟨33000329446113207621829655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22000219630742138414553103 33000329446113207621829655)
    ·
      refine ⟨49500494169169811432744483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33000329446113207621829655 49500494169169811432744483)
      ·
        refine ⟨74250741253754717149116725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49500494169169811432744483 74250741253754717149116725)
        ·
          refine ⟨6961006992539504732729693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74250741253754717149116725 6961006992539504732729693)
          ·
            refine ⟨2610377622202314274773635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6961006992539504732729693 2610377622202314274773635)
            ·
              refine ⟨3915566433303471412160453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610377622202314274773635 3915566433303471412160453)
              ·
                refine ⟨734168706244400889780085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3915566433303471412160453 734168706244400889780085)
                ·
                  refine ⟨68828316210412583416883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734168706244400889780085 68828316210412583416883)
                  ·
                    rfl

theorem cell23_1206384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 5].length) (baseStart_1206384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206384 prefixEnd_1206384 := by exact prefixLift 1206384
  have htrace : WordTrace (prefixWord ++ tailWord_1206384) baseStart_1206384 baseEnd_1206384 := by
    simpa [prefixWord, tailWord_1206384, baseEnd_1206384] using wordTrace_append hprefix tailTrace_1206384
  have hstable : (prefixWord ++ tailWord_1206384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206384).length < 2 ^ (prefixWord ++ tailWord_1206384).sum := by decide
  have hdescent : baseEnd_1206384 < baseStart_1206384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206404 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_1206404 : Nat := 118140960795 + 1206404 * 2 ^ 59
def prefixEnd_1206404 : Nat := 4983230072969 + 3 ^ 40 * 1206404 * 2
def baseEnd_1206404 : Nat := 619465115506803172501855

theorem tailTrace_1206404 : CollatzResearch.WordTrace tailWord_1206404 prefixEnd_1206404 619465115506803172501855 := by
  unfold tailWord_1206404
  simp only [CollatzResearch.WordTrace]
  refine ⟨22000584360705910122417133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29334112480941213496556177 22000584360705910122417133)
  ·
    refine ⟨8250219135264716295906425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22000584360705910122417133 8250219135264716295906425)
    ·
      refine ⟨6187664351448537221929819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8250219135264716295906425 6187664351448537221929819)
      ·
        refine ⟨9281496527172805832894729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6187664351448537221929819 9281496527172805832894729)
        ·
          refine ⟨6961122395379604374671047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9281496527172805832894729 6961122395379604374671047)
          ·
            refine ⟨10441683593069406562006571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961122395379604374671047 10441683593069406562006571)
            ·
              refine ⟨15662525389604109843009857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10441683593069406562006571 15662525389604109843009857)
              ·
                refine ⟨11746894042203082382257393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15662525389604109843009857 11746894042203082382257393)
                ·
                  refine ⟨8810170531652311786693045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11746894042203082382257393 8810170531652311786693045)
                  ·
                    refine ⟨825953487342404230002473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8810170531652311786693045 825953487342404230002473)
                    ·
                      refine ⟨619465115506803172501855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 825953487342404230002473 619465115506803172501855)
                      ·
                        rfl

theorem cell23_1206404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_1206404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206404 prefixEnd_1206404 := by exact prefixLift 1206404
  have htrace : WordTrace (prefixWord ++ tailWord_1206404) baseStart_1206404 baseEnd_1206404 := by
    simpa [prefixWord, tailWord_1206404, baseEnd_1206404] using wordTrace_append hprefix tailTrace_1206404
  have hstable : (prefixWord ++ tailWord_1206404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206404).length < 2 ^ (prefixWord ++ tailWord_1206404).sum := by decide
  have hdescent : baseEnd_1206404 < baseStart_1206404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206414 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1206414 : Nat := 118140960795 + 1206414 * 2 ^ 59
def prefixEnd_1206414 : Nat := 4983230072969 + 3 ^ 40 * 1206414 * 2
def baseEnd_1206414 : Nat := 206490083437782711125603

theorem tailTrace_1206414 : CollatzResearch.WordTrace tailWord_1206414 prefixEnd_1206414 206490083437782711125603 := by
  unfold tailWord_1206414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500191681421948994087287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29334355634250394635132197 5500191681421948994087287)
  ·
    refine ⟨8250287522132923491130931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500191681421948994087287 8250287522132923491130931)
    ·
      refine ⟨12375431283199385236696397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250287522132923491130931 12375431283199385236696397)
      ·
        refine ⟨4640786731199769463761149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12375431283199385236696397 4640786731199769463761149)
        ·
          refine ⟨1740295024199913548910431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4640786731199769463761149 1740295024199913548910431)
          ·
            refine ⟨2610442536299870323365647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740295024199913548910431 2610442536299870323365647)
            ·
              refine ⟨3915663804449805485048471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610442536299870323365647 3915663804449805485048471)
              ·
                refine ⟨5873495706674708227572707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915663804449805485048471 5873495706674708227572707)
                ·
                  refine ⟨8810243560012062341359061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873495706674708227572707 8810243560012062341359061)
                  ·
                    refine ⟨206490083437782711125603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8810243560012062341359061 206490083437782711125603)
                    ·
                      rfl

theorem cell23_1206414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1206414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206414 prefixEnd_1206414 := by exact prefixLift 1206414
  have htrace : WordTrace (prefixWord ++ tailWord_1206414) baseStart_1206414 baseEnd_1206414 := by
    simpa [prefixWord, tailWord_1206414, baseEnd_1206414] using wordTrace_append hprefix tailTrace_1206414
  have hstable : (prefixWord ++ tailWord_1206414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206414).length < 2 ^ (prefixWord ++ tailWord_1206414).sum := by decide
  have hdescent : baseEnd_1206414 < baseStart_1206414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206427 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 5, 4]
def baseStart_1206427 : Nat := 118140960795 + 1206427 * 2 ^ 59
def prefixEnd_1206427 : Nat := 4983230072969 + 3 ^ 40 * 1206427 * 2
def baseEnd_1206427 : Nat := 206492308520618860838083

theorem tailTrace_1206427 : CollatzResearch.WordTrace tailWord_1206427 prefixEnd_1206427 206492308520618860838083 := by
  unfold tailWord_1206427
  simp only [CollatzResearch.WordTrace]
  refine ⟨44002007600328495172921535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29334671733552330115281023 44002007600328495172921535)
  ·
    refine ⟨66003011400492742759382303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44002007600328495172921535 66003011400492742759382303)
    ·
      refine ⟨99004517100739114139073455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66003011400492742759382303 99004517100739114139073455)
      ·
        refine ⟨148506775651108671208610183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99004517100739114139073455 148506775651108671208610183)
        ·
          refine ⟨222760163476663006812915275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148506775651108671208610183 222760163476663006812915275)
          ·
            refine ⟨334140245214994510219372913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222760163476663006812915275 334140245214994510219372913)
            ·
              refine ⟨250605183911245882664529685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334140245214994510219372913 250605183911245882664529685)
              ·
                refine ⟨11747117995839650749899829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 250605183911245882664529685 11747117995839650749899829)
                ·
                  refine ⟨1101292312109967257803109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11747117995839650749899829 1101292312109967257803109)
                  ·
                    refine ⟨206492308520618860838083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101292312109967257803109 206492308520618860838083)
                    ·
                      rfl

theorem cell23_1206427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 4].length) (baseStart_1206427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206427 prefixEnd_1206427 := by exact prefixLift 1206427
  have htrace : WordTrace (prefixWord ++ tailWord_1206427) baseStart_1206427 baseEnd_1206427 := by
    simpa [prefixWord, tailWord_1206427, baseEnd_1206427] using wordTrace_append hprefix tailTrace_1206427
  have hstable : (prefixWord ++ tailWord_1206427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206427).length < 2 ^ (prefixWord ++ tailWord_1206427).sum := by decide
  have hdescent : baseEnd_1206427 < baseStart_1206427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206478 : List Nat := [4, 1, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1206478 : Nat := 118140960795 + 1206478 * 2 ^ 59
def prefixEnd_1206478 : Nat := 4983230072969 + 3 ^ 40 * 1206478 * 2
def baseEnd_1206478 : Nat := 206501037691745294325505

theorem tailTrace_1206478 : CollatzResearch.WordTrace tailWord_1206478 prefixEnd_1206478 206501037691745294325505 := by
  unfold tailWord_1206478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500483465392966360378511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29335911815429153922018725 5500483465392966360378511)
  ·
    refine ⟨8250725198089449540567767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500483465392966360378511 8250725198089449540567767)
    ·
      refine ⟨12376087797134174310851651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250725198089449540567767 12376087797134174310851651)
      ·
        refine ⟨18564131695701261466277477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12376087797134174310851651 18564131695701261466277477)
        ·
          refine ⟨3480774692943986524927027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18564131695701261466277477 3480774692943986524927027)
          ·
            refine ⟨5221162039415979787390541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480774692943986524927027 5221162039415979787390541)
            ·
              refine ⟨1957935764780992420271453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5221162039415979787390541 1957935764780992420271453)
              ·
                refine ⟨734225911792872157601795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1957935764780992420271453 734225911792872157601795)
                ·
                  refine ⟨1101338867689308236402693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734225911792872157601795 1101338867689308236402693)
                  ·
                    refine ⟨206501037691745294325505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101338867689308236402693 206501037691745294325505)
                    ·
                      rfl

theorem cell23_1206478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1206478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206478 prefixEnd_1206478 := by exact prefixLift 1206478
  have htrace : WordTrace (prefixWord ++ tailWord_1206478) baseStart_1206478 baseEnd_1206478 := by
    simpa [prefixWord, tailWord_1206478, baseEnd_1206478] using wordTrace_append hprefix tailTrace_1206478
  have hstable : (prefixWord ++ tailWord_1206478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206478).length < 2 ^ (prefixWord ++ tailWord_1206478).sum := by decide
  have hdescent : baseEnd_1206478 < baseStart_1206478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206487 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 5, 5]
def baseStart_1206487 : Nat := 118140960795 + 1206487 * 2 ^ 59
def prefixEnd_1206487 : Nat := 4983230072969 + 3 ^ 40 * 1206487 * 2
def baseEnd_1206487 : Nat := 206502578133708782587991

theorem tailTrace_1206487 : CollatzResearch.WordTrace tailWord_1206487 prefixEnd_1206487 206502578133708782587991 := by
  unfold tailWord_1206487
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004195980111125420105715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29336130653407416946737143 44004195980111125420105715)
  ·
    refine ⟨66006293970166688130158573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44004195980111125420105715 66006293970166688130158573)
    ·
      refine ⟨24752360238812508048809465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66006293970166688130158573 24752360238812508048809465)
      ·
        refine ⟨18564270179109381036607099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24752360238812508048809465 18564270179109381036607099)
        ·
          refine ⟨27846405268664071554910649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18564270179109381036607099 27846405268664071554910649)
          ·
            refine ⟨20884803951498053666182987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27846405268664071554910649 20884803951498053666182987)
            ·
              refine ⟨31327205927247080499274481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20884803951498053666182987 31327205927247080499274481)
              ·
                refine ⟨23495404445435310374455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31327205927247080499274481 23495404445435310374455861)
                ·
                  refine ⟨2202694166759560347605237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23495404445435310374455861 2202694166759560347605237)
                  ·
                    refine ⟨206502578133708782587991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2202694166759560347605237 206502578133708782587991)
                    ·
                      rfl

theorem cell23_1206487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_1206487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206487 prefixEnd_1206487 := by exact prefixLift 1206487
  have htrace : WordTrace (prefixWord ++ tailWord_1206487) baseStart_1206487 baseEnd_1206487 := by
    simpa [prefixWord, tailWord_1206487, baseEnd_1206487] using wordTrace_append hprefix tailTrace_1206487
  have hstable : (prefixWord ++ tailWord_1206487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206487).length < 2 ^ (prefixWord ++ tailWord_1206487).sum := by decide
  have hdescent : baseEnd_1206487 < baseStart_1206487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206551 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 2, 4]
def baseStart_1206551 : Nat := 118140960795 + 1206551 * 2 ^ 59
def prefixEnd_1206551 : Nat := 4983230072969 + 3 ^ 40 * 1206551 * 2
def baseEnd_1206551 : Nat := 206513532387671365787893

theorem tailTrace_1206551 : CollatzResearch.WordTrace tailWord_1206551 prefixEnd_1206551 206513532387671365787893 := by
  unfold tailWord_1206551
  simp only [CollatzResearch.WordTrace]
  refine ⟨44006530251879264350435507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29337686834586176233623671 44006530251879264350435507)
  ·
    refine ⟨66009795377818896525653261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44006530251879264350435507 66009795377818896525653261)
    ·
      refine ⟨24753673266682086197119973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66009795377818896525653261 24753673266682086197119973)
      ·
        refine ⟨4641313737502891161959995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24753673266682086197119973 4641313737502891161959995)
        ·
          refine ⟨6961970606254336742939993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641313737502891161959995 6961970606254336742939993)
          ·
            refine ⟨5221477954690752557204995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6961970606254336742939993 5221477954690752557204995)
            ·
              refine ⟨7832216932036128835807493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221477954690752557204995 7832216932036128835807493)
              ·
                refine ⟨1468540674756774156713905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7832216932036128835807493 1468540674756774156713905)
                ·
                  refine ⟨1101405506067580617535429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468540674756774156713905 1101405506067580617535429)
                  ·
                    refine ⟨206513532387671365787893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101405506067580617535429 206513532387671365787893)
                    ·
                      rfl

theorem cell23_1206551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_1206551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206551 prefixEnd_1206551 := by exact prefixLift 1206551
  have htrace : WordTrace (prefixWord ++ tailWord_1206551) baseStart_1206551 baseEnd_1206551 := by
    simpa [prefixWord, tailWord_1206551, baseEnd_1206551] using wordTrace_append hprefix tailTrace_1206551
  have hstable : (prefixWord ++ tailWord_1206551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206551).length < 2 ^ (prefixWord ++ tailWord_1206551).sum := by decide
  have hdescent : baseEnd_1206551 < baseStart_1206551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206558 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1206558 : Nat := 118140960795 + 1206558 * 2 ^ 59
def prefixEnd_1206558 : Nat := 4983230072969 + 3 ^ 40 * 1206558 * 2
def baseEnd_1206558 : Nat := 619544191527595569976147

theorem tailTrace_1206558 : CollatzResearch.WordTrace tailWord_1206558 prefixEnd_1206558 619544191527595569976147 := by
  unfold tailWord_1206558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500848195356738068242541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29337857041902603030626885 5500848195356738068242541)
  ·
    refine ⟨2062818073258776775590953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5500848195356738068242541 2062818073258776775590953)
    ·
      refine ⟨1547113554944082581693215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062818073258776775590953 1547113554944082581693215)
      ·
        refine ⟨2320670332416123872539823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547113554944082581693215 2320670332416123872539823)
        ·
          refine ⟨3481005498624185808809735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320670332416123872539823 3481005498624185808809735)
          ·
            refine ⟨5221508247936278713214603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481005498624185808809735 5221508247936278713214603)
            ·
              refine ⟨7832262371904418069821905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221508247936278713214603 7832262371904418069821905)
              ·
                refine ⟨5874196778928313552366429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832262371904418069821905 5874196778928313552366429)
                ·
                  refine ⟨2202823792098117582137411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5874196778928313552366429 2202823792098117582137411)
                  ·
                    refine ⟨3304235688147176373206117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202823792098117582137411 3304235688147176373206117)
                    ·
                      refine ⟨619544191527595569976147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3304235688147176373206117 619544191527595569976147)
                      ·
                        rfl

theorem cell23_1206558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1206558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206558 prefixEnd_1206558 := by exact prefixLift 1206558
  have htrace : WordTrace (prefixWord ++ tailWord_1206558) baseStart_1206558 baseEnd_1206558 := by
    simpa [prefixWord, tailWord_1206558, baseEnd_1206558] using wordTrace_append hprefix tailTrace_1206558
  have hstable : (prefixWord ++ tailWord_1206558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206558).length < 2 ^ (prefixWord ++ tailWord_1206558).sum := by decide
  have hdescent : baseEnd_1206558 < baseStart_1206558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206564 : List Nat := [2, 3, 1, 3, 1, 2, 3, 8]
def baseStart_1206564 : Nat := 118140960795 + 1206564 * 2 ^ 59
def prefixEnd_1206564 : Nat := 4983230072969 + 3 ^ 40 * 1206564 * 2
def baseEnd_1206564 : Nat := 22946195274500835055597

theorem tailTrace_1206564 : CollatzResearch.WordTrace tailWord_1206564 prefixEnd_1206564 22946195274500835055597 := by
  unfold tailWord_1206564
  simp only [CollatzResearch.WordTrace]
  refine ⟨22003502200416083785329373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29338002933888111713772497 22003502200416083785329373)
  ·
    refine ⟨8251313325156031419498515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22003502200416083785329373 8251313325156031419498515)
    ·
      refine ⟨12376969987734047129247773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8251313325156031419498515 12376969987734047129247773)
      ·
        refine ⟨4641363745400267673467915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12376969987734047129247773 4641363745400267673467915)
        ·
          refine ⟨6962045618100401510201873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641363745400267673467915 6962045618100401510201873)
          ·
            refine ⟨5221534213575301132651405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962045618100401510201873 5221534213575301132651405)
            ·
              refine ⟨1958075330090737924744277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5221534213575301132651405 1958075330090737924744277)
              ·
                refine ⟨22946195274500835055597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1958075330090737924744277 22946195274500835055597)
                ·
                  rfl

theorem cell23_1206564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 8].length) (baseStart_1206564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206564 prefixEnd_1206564 := by exact prefixLift 1206564
  have htrace : WordTrace (prefixWord ++ tailWord_1206564) baseStart_1206564 baseEnd_1206564 := by
    simpa [prefixWord, tailWord_1206564, baseEnd_1206564] using wordTrace_append hprefix tailTrace_1206564
  have hstable : (prefixWord ++ tailWord_1206564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206564).length < 2 ^ (prefixWord ++ tailWord_1206564).sum := by decide
  have hdescent : baseEnd_1206564 < baseStart_1206564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206591 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_1206591 : Nat := 118140960795 + 1206591 * 2 ^ 59
def prefixEnd_1206591 : Nat := 4983230072969 + 3 ^ 40 * 1206591 * 2
def baseEnd_1206591 : Nat := 619561136389193940863495

theorem tailTrace_1206591 : CollatzResearch.WordTrace tailWord_1206591 prefixEnd_1206591 619561136389193940863495 := by
  unfold tailWord_1206591
  simp only [CollatzResearch.WordTrace]
  refine ⟨44007989171734351181891627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29338659447822900787927751 44007989171734351181891627)
  ·
    refine ⟨66011983757601526772837441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44007989171734351181891627 66011983757601526772837441)
    ·
      refine ⟨49508987818201145079628081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66011983757601526772837441 49508987818201145079628081)
      ·
        refine ⟨37131740863650858809721061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49508987818201145079628081 37131740863650858809721061)
        ·
          refine ⟨6962201411934536026822699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37131740863650858809721061 6962201411934536026822699)
          ·
            refine ⟨10443302117901804040234049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962201411934536026822699 10443302117901804040234049)
            ·
              refine ⟨7832476588426353030175537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10443302117901804040234049 7832476588426353030175537)
              ·
                refine ⟨5874357441319764772631653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832476588426353030175537 5874357441319764772631653)
                ·
                  refine ⟨1101442020247455894868435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5874357441319764772631653 1101442020247455894868435)
                  ·
                    refine ⟨1652163030371183842302653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1101442020247455894868435 1652163030371183842302653)
                    ·
                      refine ⟨619561136389193940863495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1652163030371183842302653 619561136389193940863495)
                      ·
                        rfl

theorem cell23_1206591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_1206591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206591 prefixEnd_1206591 := by exact prefixLift 1206591
  have htrace : WordTrace (prefixWord ++ tailWord_1206591) baseStart_1206591 baseEnd_1206591 := by
    simpa [prefixWord, tailWord_1206591, baseEnd_1206591] using wordTrace_append hprefix tailTrace_1206591
  have hstable : (prefixWord ++ tailWord_1206591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206591).length < 2 ^ (prefixWord ++ tailWord_1206591).sum := by decide
  have hdescent : baseEnd_1206591 < baseStart_1206591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206608 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_1206608 : Nat := 118140960795 + 1206608 * 2 ^ 59
def prefixEnd_1206608 : Nat := 4983230072969 + 3 ^ 40 * 1206608 * 2
def baseEnd_1206608 : Nat := 619569865560320374350917

theorem tailTrace_1206608 : CollatzResearch.WordTrace tailWord_1206608 prefixEnd_1206608 619569865560320374350917 := by
  unfold tailWord_1206608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004304606336381542630239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29339072808448508723506985 22004304606336381542630239)
  ·
    refine ⟨33006456909504572313945359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22004304606336381542630239 33006456909504572313945359)
    ·
      refine ⟨49509685364256858470918039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33006456909504572313945359 49509685364256858470918039)
      ·
        refine ⟨74264528046385287706377059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49509685364256858470918039 74264528046385287706377059)
        ·
          refine ⟨111396792069577931559565589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74264528046385287706377059 111396792069577931559565589)
          ·
            refine ⟨5221724628261465541854637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111396792069577931559565589 5221724628261465541854637)
            ·
              refine ⟨1958146735598049578195489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5221724628261465541854637 1958146735598049578195489)
              ·
                refine ⟨1468610051698537183646617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958146735598049578195489 1468610051698537183646617)
                ·
                  refine ⟨1101457538773902887734963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468610051698537183646617 1101457538773902887734963)
                  ·
                    refine ⟨1652186308160854331602445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1101457538773902887734963 1652186308160854331602445)
                    ·
                      refine ⟨619569865560320374350917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1652186308160854331602445 619569865560320374350917)
                      ·
                        rfl

theorem cell23_1206608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_1206608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206608 prefixEnd_1206608 := by exact prefixLift 1206608
  have htrace : WordTrace (prefixWord ++ tailWord_1206608) baseStart_1206608 baseEnd_1206608 := by
    simpa [prefixWord, tailWord_1206608, baseEnd_1206608] using wordTrace_append hprefix tailTrace_1206608
  have hstable : (prefixWord ++ tailWord_1206608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206608).length < 2 ^ (prefixWord ++ tailWord_1206608).sum := by decide
  have hdescent : baseEnd_1206608 < baseStart_1206608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206622 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1206622 : Nat := 118140960795 + 1206622 * 2 ^ 59
def prefixEnd_1206622 : Nat := 4983230072969 + 3 ^ 40 * 1206622 * 2
def baseEnd_1206622 : Nat := 619577054289483319575853

theorem tailTrace_1206622 : CollatzResearch.WordTrace tailWord_1206622 prefixEnd_1206622 619577054289483319575853 := by
  unfold tailWord_1206622
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501139979327755434533765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29339413223081362317513413 5501139979327755434533765)
  ·
    refine ⟨1031463746123954143975081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5501139979327755434533765 1031463746123954143975081)
    ·
      refine ⟨773597809592965607981311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1031463746123954143975081 773597809592965607981311)
      ·
        refine ⟨1160396714389448411971967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773597809592965607981311 1160396714389448411971967)
        ·
          refine ⟨1740595071584172617957951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160396714389448411971967 1740595071584172617957951)
          ·
            refine ⟨2610892607376258926936927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740595071584172617957951 2610892607376258926936927)
            ·
              refine ⟨3916338911064388390405391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610892607376258926936927 3916338911064388390405391)
              ·
                refine ⟨5874508366596582585608087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916338911064388390405391 5874508366596582585608087)
                ·
                  refine ⟨8811762549894873878412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874508366596582585608087 8811762549894873878412131)
                  ·
                    refine ⟨13217643824842310817618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8811762549894873878412131 13217643824842310817618197)
                    ·
                      refine ⟨619577054289483319575853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13217643824842310817618197 619577054289483319575853)
                      ·
                        rfl

theorem cell23_1206622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1206622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206622 prefixEnd_1206622 := by exact prefixLift 1206622
  have htrace : WordTrace (prefixWord ++ tailWord_1206622) baseStart_1206622 baseEnd_1206622 := by
    simpa [prefixWord, tailWord_1206622, baseEnd_1206622] using wordTrace_append hprefix tailTrace_1206622
  have hstable : (prefixWord ++ tailWord_1206622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206622).length < 2 ^ (prefixWord ++ tailWord_1206622).sum := by decide
  have hdescent : baseEnd_1206622 < baseStart_1206622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206664 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1206664 : Nat := 118140960795 + 1206664 * 2 ^ 59
def prefixEnd_1206664 : Nat := 4983230072969 + 3 ^ 40 * 1206664 * 2
def baseEnd_1206664 : Nat := 619598620476972155250659

theorem tailTrace_1206664 : CollatzResearch.WordTrace tailWord_1206664 prefixEnd_1206664 619598620476972155250659 := by
  unfold tailWord_1206664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005325850234942324649523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29340434466979923099532697 22005325850234942324649523)
  ·
    refine ⟨33007988775352413486974285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22005325850234942324649523 33007988775352413486974285)
    ·
      refine ⟨12377995790757155057615357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33007988775352413486974285 12377995790757155057615357)
      ·
        refine ⟨4641748421533933146605759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12377995790757155057615357 4641748421533933146605759)
        ·
          refine ⟨6962622632300899719908639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641748421533933146605759 6962622632300899719908639)
          ·
            refine ⟨10443933948451349579862959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962622632300899719908639 10443933948451349579862959)
            ·
              refine ⟨15665900922677024369794439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443933948451349579862959 15665900922677024369794439)
              ·
                refine ⟨23498851384015536554691659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15665900922677024369794439 23498851384015536554691659)
                ·
                  refine ⟨35248277076023304832037489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23498851384015536554691659 35248277076023304832037489)
                  ·
                    refine ⟨26436207807017478624028117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35248277076023304832037489 26436207807017478624028117)
                    ·
                      refine ⟨619598620476972155250659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26436207807017478624028117 619598620476972155250659)
                      ·
                        rfl

theorem cell23_1206664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1206664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206664 prefixEnd_1206664 := by exact prefixLift 1206664
  have htrace : WordTrace (prefixWord ++ tailWord_1206664) baseStart_1206664 baseEnd_1206664 := by
    simpa [prefixWord, tailWord_1206664, baseEnd_1206664] using wordTrace_append hprefix tailTrace_1206664
  have hstable : (prefixWord ++ tailWord_1206664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206664).length < 2 ^ (prefixWord ++ tailWord_1206664).sum := by decide
  have hdescent : baseEnd_1206664 < baseStart_1206664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206682 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_1206682 : Nat := 118140960795 + 1206682 * 2 ^ 59
def prefixEnd_1206682 : Nat := 4983230072969 + 3 ^ 40 * 1206682 * 2
def baseEnd_1206682 : Nat := 619607863128753084825577

theorem tailTrace_1206682 : CollatzResearch.WordTrace tailWord_1206682 prefixEnd_1206682 619607863128753084825577 := by
  unfold tailWord_1206682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11002827053601168430863575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29340872142936449148969533 11002827053601168430863575)
  ·
    refine ⟨16504240580401752646295363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11002827053601168430863575 16504240580401752646295363)
    ·
      refine ⟨24756360870602628969443045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16504240580401752646295363 24756360870602628969443045)
      ·
        refine ⟨4641817663237992931770571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24756360870602628969443045 4641817663237992931770571)
        ·
          refine ⟨6962726494856989397655857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641817663237992931770571 6962726494856989397655857)
          ·
            refine ⟨5222044871142742048241893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962726494856989397655857 5222044871142742048241893)
            ·
              refine ⟨979133413339264134045355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5222044871142742048241893 979133413339264134045355)
              ·
                refine ⟨1468700120008896201068033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979133413339264134045355 1468700120008896201068033)
                ·
                  refine ⟨1101525090006672150801025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468700120008896201068033 1101525090006672150801025)
                  ·
                    refine ⟨826143817505004113100769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101525090006672150801025 826143817505004113100769)
                    ·
                      refine ⟨619607863128753084825577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826143817505004113100769 619607863128753084825577)
                      ·
                        rfl

theorem cell23_1206682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_1206682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206682 prefixEnd_1206682 := by exact prefixLift 1206682
  have htrace : WordTrace (prefixWord ++ tailWord_1206682) baseStart_1206682 baseEnd_1206682 := by
    simpa [prefixWord, tailWord_1206682, baseEnd_1206682] using wordTrace_append hprefix tailTrace_1206682
  have hstable : (prefixWord ++ tailWord_1206682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206682).length < 2 ^ (prefixWord ++ tailWord_1206682).sum := by decide
  have hdescent : baseEnd_1206682 < baseStart_1206682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206704 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_1206704 : Nat := 118140960795 + 1206704 * 2 ^ 59
def prefixEnd_1206704 : Nat := 4983230072969 + 3 ^ 40 * 1206704 * 2
def baseEnd_1206704 : Nat := 619619159703151998750475

theorem tailTrace_1206704 : CollatzResearch.WordTrace tailWord_1206704 prefixEnd_1206704 619619159703151998750475 := by
  unfold tailWord_1206704
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006055310162485740377583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29341407080216647653836777 22006055310162485740377583)
  ·
    refine ⟨33009082965243728610566375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22006055310162485740377583 33009082965243728610566375)
    ·
      refine ⟨49513624447865592915849563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33009082965243728610566375 49513624447865592915849563)
      ·
        refine ⟨74270436671798389373774345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49513624447865592915849563 74270436671798389373774345)
        ·
          refine ⟨55702827503848792030330759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74270436671798389373774345 55702827503848792030330759)
          ·
            refine ⟨83554241255773188045496139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55702827503848792030330759 83554241255773188045496139)
            ·
              refine ⟨125331361883659782068244209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83554241255773188045496139 125331361883659782068244209)
              ·
                refine ⟨93998521412744836551183157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125331361883659782068244209 93998521412744836551183157)
                ·
                  refine ⟨8812361382444828426673421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93998521412744836551183157 8812361382444828426673421)
                  ·
                    refine ⟨3304635518416810660002533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8812361382444828426673421 3304635518416810660002533)
                    ·
                      refine ⟨619619159703151998750475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3304635518416810660002533 619619159703151998750475)
                      ·
                        rfl

theorem cell23_1206704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_1206704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206704 prefixEnd_1206704 := by exact prefixLift 1206704
  have htrace : WordTrace (prefixWord ++ tailWord_1206704) baseStart_1206704 baseEnd_1206704 := by
    simpa [prefixWord, tailWord_1206704, baseEnd_1206704] using wordTrace_append hprefix tailTrace_1206704
  have hstable : (prefixWord ++ tailWord_1206704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206704).length < 2 ^ (prefixWord ++ tailWord_1206704).sum := by decide
  have hdescent : baseEnd_1206704 < baseStart_1206704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206731 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 3, 4]
def baseStart_1206731 : Nat := 118140960795 + 1206731 * 2 ^ 59
def prefixEnd_1206731 : Nat := 4983230072969 + 3 ^ 40 * 1206731 * 2
def baseEnd_1206731 : Nat := 206544341226941131037617

theorem tailTrace_1206731 : CollatzResearch.WordTrace tailWord_1206731 prefixEnd_1206731 206544341226941131037617 := by
  unfold tailWord_1206731
  simp only [CollatzResearch.WordTrace]
  refine ⟨44013095391227155091988047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29342063594151436727992031 44013095391227155091988047)
  ·
    refine ⟨66019643086840732637982071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44013095391227155091988047 66019643086840732637982071)
    ·
      refine ⟨99029464630261098956973107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66019643086840732637982071 99029464630261098956973107)
      ·
        refine ⟨148544196945391648435459661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99029464630261098956973107 148544196945391648435459661)
        ·
          refine ⟨55704073854521868163297373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148544196945391648435459661 55704073854521868163297373)
          ·
            refine ⟨20889027695445700561236515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55704073854521868163297373 20889027695445700561236515)
            ·
              refine ⟨31333541543168550841854773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20889027695445700561236515 31333541543168550841854773)
              ·
                refine ⟨2937519519672051641423885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31333541543168550841854773 2937519519672051641423885)
                ·
                  refine ⟨1101569819877019365533957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2937519519672051641423885 1101569819877019365533957)
                  ·
                    refine ⟨206544341226941131037617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101569819877019365533957 206544341226941131037617)
                    ·
                      rfl

theorem cell23_1206731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 4].length) (baseStart_1206731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206731 prefixEnd_1206731 := by exact prefixLift 1206731
  have htrace : WordTrace (prefixWord ++ tailWord_1206731) baseStart_1206731 baseEnd_1206731 := by
    simpa [prefixWord, tailWord_1206731, baseEnd_1206731] using wordTrace_append hprefix tailTrace_1206731
  have hstable : (prefixWord ++ tailWord_1206731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206731).length < 2 ^ (prefixWord ++ tailWord_1206731).sum := by decide
  have hdescent : baseEnd_1206731 < baseStart_1206731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206744 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 10]
def baseStart_1206744 : Nat := 118140960795 + 1206744 * 2 ^ 59
def prefixEnd_1206744 : Nat := 4983230072969 + 3 ^ 40 * 1206744 * 2
def baseEnd_1206744 : Nat := 68848855436592426916699

theorem tailTrace_1206744 : CollatzResearch.WordTrace tailWord_1206744 prefixEnd_1206744 68848855436592426916699 := by
  unfold tailWord_1206744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006784770090029156105643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29342379693453372208140857 22006784770090029156105643)
  ·
    refine ⟨33010177155135043734158465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22006784770090029156105643 33010177155135043734158465)
    ·
      refine ⟨24757632866351282800618849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33010177155135043734158465 24757632866351282800618849)
      ·
        refine ⟨18568224649763462100464137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24757632866351282800618849 18568224649763462100464137)
        ·
          refine ⟨13926168487322596575348103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18568224649763462100464137 13926168487322596575348103)
          ·
            refine ⟨20889252730983894863022155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13926168487322596575348103 20889252730983894863022155)
            ·
              refine ⟨31333879096475842294533233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20889252730983894863022155 31333879096475842294533233)
              ·
                refine ⟨23500409322356881720899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31333879096475842294533233 23500409322356881720899925)
                ·
                  refine ⟨68848855436592426916699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 23500409322356881720899925 68848855436592426916699)
                  ·
                    rfl

theorem cell23_1206744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_1206744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206744 prefixEnd_1206744 := by exact prefixLift 1206744
  have htrace : WordTrace (prefixWord ++ tailWord_1206744) baseStart_1206744 baseEnd_1206744 := by
    simpa [prefixWord, tailWord_1206744, baseEnd_1206744] using wordTrace_append hprefix tailTrace_1206744
  have hstable : (prefixWord ++ tailWord_1206744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206744).length < 2 ^ (prefixWord ++ tailWord_1206744).sum := by decide
  have hdescent : baseEnd_1206744 < baseStart_1206744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206755 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1206755 : Nat := 118140960795 + 1206755 * 2 ^ 59
def prefixEnd_1206755 : Nat := 4983230072969 + 3 ^ 40 * 1206755 * 2
def baseEnd_1206755 : Nat := 619645347216531299212741

theorem tailTrace_1206755 : CollatzResearch.WordTrace tailWord_1206755 prefixEnd_1206755 619645347216531299212741 := by
  unfold tailWord_1206755
  simp only [CollatzResearch.WordTrace]
  refine ⟨44013970743140207190861719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29342647162093471460574479 44013970743140207190861719)
  ·
    refine ⟨66020956114710310786292579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44013970743140207190861719 66020956114710310786292579)
    ·
      refine ⟨99031434172065466179438869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66020956114710310786292579 99031434172065466179438869)
      ·
        refine ⟨4642098476815568727161197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99031434172065466179438869 4642098476815568727161197)
        ·
          refine ⟨1740786928805838272685449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4642098476815568727161197 1740786928805838272685449)
          ·
            refine ⟨1305590196604378704514087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740786928805838272685449 1305590196604378704514087)
            ·
              refine ⟨1958385294906568056771131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305590196604378704514087 1958385294906568056771131)
              ·
                refine ⟨2937577942359852085156697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958385294906568056771131 2937577942359852085156697)
                ·
                  refine ⟨2203183456769889063867523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2937577942359852085156697 2203183456769889063867523)
                  ·
                    refine ⟨3304775185154833595801285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2203183456769889063867523 3304775185154833595801285)
                    ·
                      refine ⟨619645347216531299212741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3304775185154833595801285 619645347216531299212741)
                      ·
                        rfl

theorem cell23_1206755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1206755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206755 prefixEnd_1206755 := by exact prefixLift 1206755
  have htrace : WordTrace (prefixWord ++ tailWord_1206755) baseStart_1206755 baseEnd_1206755 := by
    simpa [prefixWord, tailWord_1206755, baseEnd_1206755] using wordTrace_append hprefix tailTrace_1206755
  have hstable : (prefixWord ++ tailWord_1206755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206755).length < 2 ^ (prefixWord ++ tailWord_1206755).sum := by decide
  have hdescent : baseEnd_1206755 < baseStart_1206755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206808 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_1206808 : Nat := 118140960795 + 1206808 * 2 ^ 59
def prefixEnd_1206808 : Nat := 4983230072969 + 3 ^ 40 * 1206808 * 2
def baseEnd_1206808 : Nat := 206557520563739863949999

theorem tailTrace_1206808 : CollatzResearch.WordTrace tailWord_1206808 prefixEnd_1206808 206557520563739863949999 := by
  unfold tailWord_1206808
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007951905974098621270539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29343935874632131495027385 22007951905974098621270539)
  ·
    refine ⟨33011927858961147931905809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22007951905974098621270539 33011927858961147931905809)
    ·
      refine ⟨24758945894220860948929357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33011927858961147931905809 24758945894220860948929357)
      ·
        refine ⟨9284604710332822855848509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24758945894220860948929357 9284604710332822855848509)
        ·
          refine ⟨3481726766374808570943191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9284604710332822855848509 3481726766374808570943191)
          ·
            refine ⟨5222590149562212856414787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481726766374808570943191 5222590149562212856414787)
            ·
              refine ⟨7833885224343319284622181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222590149562212856414787 7833885224343319284622181)
              ·
                refine ⟨1468853479564372365866659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7833885224343319284622181 1468853479564372365866659)
                ·
                  refine ⟨2203280219346558548799989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468853479564372365866659 2203280219346558548799989)
                  ·
                    refine ⟨206557520563739863949999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2203280219346558548799989 206557520563739863949999)
                    ·
                      rfl

theorem cell23_1206808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_1206808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206808 prefixEnd_1206808 := by exact prefixLift 1206808
  have htrace : WordTrace (prefixWord ++ tailWord_1206808) baseStart_1206808 baseEnd_1206808 := by
    simpa [prefixWord, tailWord_1206808, baseEnd_1206808] using wordTrace_append hprefix tailTrace_1206808
  have hstable : (prefixWord ++ tailWord_1206808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206808).length < 2 ^ (prefixWord ++ tailWord_1206808).sum := by decide
  have hdescent : baseEnd_1206808 < baseStart_1206808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206821 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_1206821 : Nat := 118140960795 + 1206821 * 2 ^ 59
def prefixEnd_1206821 : Nat := 4983230072969 + 3 ^ 40 * 1206821 * 2
def baseEnd_1206821 : Nat := 206559745646576013662479

theorem tailTrace_1206821 : CollatzResearch.WordTrace tailWord_1206821 prefixEnd_1206821 206559745646576013662479 := by
  unfold tailWord_1206821
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016377960901100462764317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29344251973934066975176211 44016377960901100462764317)
  ·
    refine ⟨16506141735337912673536619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44016377960901100462764317 16506141735337912673536619)
    ·
      refine ⟨24759212603006869010304929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16506141735337912673536619 24759212603006869010304929)
      ·
        refine ⟨18569409452255151757728697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24759212603006869010304929 18569409452255151757728697)
        ·
          refine ⟨13927057089191363818296523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18569409452255151757728697 13927057089191363818296523)
          ·
            refine ⟨20890585633787045727444785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13927057089191363818296523 20890585633787045727444785)
            ·
              refine ⟨15667939225340284295583589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20890585633787045727444785 15667939225340284295583589)
              ·
                refine ⟨2937738604751303305421923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15667939225340284295583589 2937738604751303305421923)
                ·
                  refine ⟨4406607907126954958132885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937738604751303305421923 4406607907126954958132885)
                  ·
                    refine ⟨206559745646576013662479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4406607907126954958132885 206559745646576013662479)
                    ·
                      rfl

theorem cell23_1206821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_1206821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206821 prefixEnd_1206821 := by exact prefixLift 1206821
  have htrace : WordTrace (prefixWord ++ tailWord_1206821) baseStart_1206821 baseEnd_1206821 := by
    simpa [prefixWord, tailWord_1206821, baseEnd_1206821] using wordTrace_append hprefix tailTrace_1206821
  have hstable : (prefixWord ++ tailWord_1206821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206821).length < 2 ^ (prefixWord ++ tailWord_1206821).sum := by decide
  have hdescent : baseEnd_1206821 < baseStart_1206821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206841 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1206841 : Nat := 118140960795 + 1206841 * 2 ^ 59
def prefixEnd_1206841 : Nat := 4983230072969 + 3 ^ 40 * 1206841 * 2
def baseEnd_1206841 : Nat := 619689506552817962737345

theorem tailTrace_1206841 : CollatzResearch.WordTrace tailWord_1206841 prefixEnd_1206841 619689506552817962737345 := by
  unfold tailWord_1206841
  simp only [CollatzResearch.WordTrace]
  refine ⟨44017107420828643878492377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29344738280552429252328251 44017107420828643878492377)
  ·
    refine ⟨33012830565621482908869283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44017107420828643878492377 33012830565621482908869283)
    ·
      refine ⟨49519245848432224363303925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33012830565621482908869283 49519245848432224363303925)
      ·
        refine ⟨4642429298290521034059743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49519245848432224363303925 4642429298290521034059743)
        ·
          refine ⟨6963643947435781551089615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642429298290521034059743 6963643947435781551089615)
          ·
            refine ⟨10445465921153672326634423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963643947435781551089615 10445465921153672326634423)
            ·
              refine ⟨15668198881730508489951635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10445465921153672326634423 15668198881730508489951635)
              ·
                refine ⟨23502298322595762734927453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15668198881730508489951635 23502298322595762734927453)
                ·
                  refine ⟨8813361870973411025597795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23502298322595762734927453 8813361870973411025597795)
                  ·
                    refine ⟨13220042806460116538396693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8813361870973411025597795 13220042806460116538396693)
                    ·
                      refine ⟨619689506552817962737345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13220042806460116538396693 619689506552817962737345)
                      ·
                        rfl

theorem cell23_1206841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1206841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206841 prefixEnd_1206841 := by exact prefixLift 1206841
  have htrace : WordTrace (prefixWord ++ tailWord_1206841) baseStart_1206841 baseEnd_1206841 := by
    simpa [prefixWord, tailWord_1206841, baseEnd_1206841] using wordTrace_append hprefix tailTrace_1206841
  have hstable : (prefixWord ++ tailWord_1206841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206841).length < 2 ^ (prefixWord ++ tailWord_1206841).sum := by decide
  have hdescent : baseEnd_1206841 < baseStart_1206841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206855 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 2, 4]
def baseStart_1206855 : Nat := 118140960795 + 1206855 * 2 ^ 59
def prefixEnd_1206855 : Nat := 4983230072969 + 3 ^ 40 * 1206855 * 2
def baseEnd_1206855 : Nat := 206565565093993635987427

theorem tailTrace_1206855 : CollatzResearch.WordTrace tailWord_1206855 prefixEnd_1206855 206565565093993635987427 := by
  unfold tailWord_1206855
  simp only [CollatzResearch.WordTrace]
  refine ⟨44017618042777924269502019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29345078695185282846334679 44017618042777924269502019)
  ·
    refine ⟨66026427064166886404253029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44017618042777924269502019 66026427064166886404253029)
    ·
      refine ⟨12379955074531291200797443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66026427064166886404253029 12379955074531291200797443)
      ·
        refine ⟨18569932611796936801196165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12379955074531291200797443 18569932611796936801196165)
        ·
          refine ⟨3481862364711925650224281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18569932611796936801196165 3481862364711925650224281)
          ·
            refine ⟨2611396773533944237668211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481862364711925650224281 2611396773533944237668211)
            ·
              refine ⟨3917095160300916356502317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611396773533944237668211 3917095160300916356502317)
              ·
                refine ⟨1468910685112843633688369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3917095160300916356502317 1468910685112843633688369)
                ·
                  refine ⟨1101683013834632725266277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468910685112843633688369 1101683013834632725266277)
                  ·
                    refine ⟨206565565093993635987427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101683013834632725266277 206565565093993635987427)
                    ·
                      rfl

theorem cell23_1206855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_1206855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206855 prefixEnd_1206855 := by exact prefixLift 1206855
  have htrace : WordTrace (prefixWord ++ tailWord_1206855) baseStart_1206855 baseEnd_1206855 := by
    simpa [prefixWord, tailWord_1206855, baseEnd_1206855] using wordTrace_append hprefix tailTrace_1206855
  have hstable : (prefixWord ++ tailWord_1206855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206855).length < 2 ^ (prefixWord ++ tailWord_1206855).sum := by decide
  have hdescent : baseEnd_1206855 < baseStart_1206855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206865 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_1206865 : Nat := 118140960795 + 1206865 * 2 ^ 59
def prefixEnd_1206865 : Nat := 4983230072969 + 3 ^ 40 * 1206865 * 2
def baseEnd_1206865 : Nat := 619701830088525868837235

theorem tailTrace_1206865 : CollatzResearch.WordTrace tailWord_1206865 prefixEnd_1206865 619701830088525868837235 := by
  unfold tailWord_1206865
  simp only [CollatzResearch.WordTrace]
  refine ⟨44017982772741695977366049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29345321848494463984910699 44017982772741695977366049)
  ·
    refine ⟨33013487079556271983024537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44017982772741695977366049 33013487079556271983024537)
    ·
      refine ⟨24760115309667203987268403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33013487079556271983024537 24760115309667203987268403)
      ·
        refine ⟨37140172964500805980902605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24760115309667203987268403 37140172964500805980902605)
        ·
          refine ⟨13927564861687802242838477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37140172964500805980902605 13927564861687802242838477)
          ·
            refine ⟨5222836823132925841064429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13927564861687802242838477 5222836823132925841064429)
            ·
              refine ⟨1958563808674847190399161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5222836823132925841064429 1958563808674847190399161)
              ·
                refine ⟨1468922856506135392799371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958563808674847190399161 1468922856506135392799371)
                ·
                  refine ⟨2203384284759203089199057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468922856506135392799371 2203384284759203089199057)
                  ·
                    refine ⟨1652538213569402316899293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203384284759203089199057 1652538213569402316899293)
                    ·
                      refine ⟨619701830088525868837235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1652538213569402316899293 619701830088525868837235)
                      ·
                        rfl

theorem cell23_1206865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_1206865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206865 prefixEnd_1206865 := by exact prefixLift 1206865
  have htrace : WordTrace (prefixWord ++ tailWord_1206865) baseStart_1206865 baseEnd_1206865 := by
    simpa [prefixWord, tailWord_1206865, baseEnd_1206865] using wordTrace_append hprefix tailTrace_1206865
  have hstable : (prefixWord ++ tailWord_1206865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206865).length < 2 ^ (prefixWord ++ tailWord_1206865).sum := by decide
  have hdescent : baseEnd_1206865 < baseStart_1206865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206895 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_1206895 : Nat := 118140960795 + 1206895 * 2 ^ 59
def prefixEnd_1206895 : Nat := 4983230072969 + 3 ^ 40 * 1206895 * 2
def baseEnd_1206895 : Nat := 619717234508160751462097

theorem tailTrace_1206895 : CollatzResearch.WordTrace tailWord_1206895 prefixEnd_1206895 619717234508160751462097 := by
  unfold tailWord_1206895
  simp only [CollatzResearch.WordTrace]
  refine ⟨44019076962633011100958139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29346051308422007400638759 44019076962633011100958139)
  ·
    refine ⟨66028615443949516651437209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44019076962633011100958139 66028615443949516651437209)
    ·
      refine ⟨49521461582962137488577907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66028615443949516651437209 49521461582962137488577907)
      ·
        refine ⟨74282192374443206232866861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49521461582962137488577907 74282192374443206232866861)
        ·
          refine ⟨27855822140416202337325073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74282192374443206232866861 27855822140416202337325073)
          ·
            refine ⟨20891866605312151752993805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27855822140416202337325073 20891866605312151752993805)
            ·
              refine ⟨7834449976992056907372677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20891866605312151752993805 7834449976992056907372677)
              ·
                refine ⟨1468959370686010670132377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7834449976992056907372677 1468959370686010670132377)
                ·
                  refine ⟨1101719528014508002599283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468959370686010670132377 1101719528014508002599283)
                  ·
                    refine ⟨1652579292021762003898925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1101719528014508002599283 1652579292021762003898925)
                    ·
                      refine ⟨619717234508160751462097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1652579292021762003898925 619717234508160751462097)
                      ·
                        rfl

theorem cell23_1206895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_1206895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206895 prefixEnd_1206895 := by exact prefixLift 1206895
  have htrace : WordTrace (prefixWord ++ tailWord_1206895) baseStart_1206895 baseEnd_1206895 := by
    simpa [prefixWord, tailWord_1206895, baseEnd_1206895] using wordTrace_append hprefix tailTrace_1206895
  have hstable : (prefixWord ++ tailWord_1206895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206895).length < 2 ^ (prefixWord ++ tailWord_1206895).sum := by decide
  have hdescent : baseEnd_1206895 < baseStart_1206895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
