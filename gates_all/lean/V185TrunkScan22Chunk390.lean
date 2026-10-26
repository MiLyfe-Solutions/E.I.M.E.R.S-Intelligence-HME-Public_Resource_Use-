import V185TrunkScan22Chunk389

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3478236 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3478236 : Nat := 118140960795 + 3478236 * 2 ^ 59
def prefixEnd_3478236 : Nat := 4983230072969 + 3 ^ 40 * 3478236 * 2
def baseEnd_3478236 : Nat := 1190671265181305746235927

theorem tailTrace_3478236 : CollatzResearch.WordTrace tailWord_3478236 prefixEnd_3478236 1190671265181305746235927 := by
  unfold tailWord_3478236
  simp only [CollatzResearch.WordTrace]
  refine ⟨63430844513476241130167281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84574459351301654840223041 63430844513476241130167281)
  ·
    refine ⟨47573133385107180847625461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63430844513476241130167281 47573133385107180847625461)
    ·
      refine ⟨4459981254853798204464887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47573133385107180847625461 4459981254853798204464887)
      ·
        refine ⟨6689971882280697306697331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459981254853798204464887 6689971882280697306697331)
        ·
          refine ⟨10034957823421045960045997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689971882280697306697331 10034957823421045960045997)
          ·
            refine ⟨3763109183782892235017249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10034957823421045960045997 3763109183782892235017249)
            ·
              refine ⟨2822331887837169176262937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763109183782892235017249 2822331887837169176262937)
              ·
                refine ⟨2116748915877876882197203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822331887837169176262937 2116748915877876882197203)
                ·
                  refine ⟨3175123373816815323295805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116748915877876882197203 3175123373816815323295805)
                  ·
                    refine ⟨1190671265181305746235927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175123373816815323295805 1190671265181305746235927)
                    ·
                      rfl

theorem cell22_3478236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3478236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478236 prefixEnd_3478236 := by exact prefixLift 3478236
  have htrace : WordTrace (prefixWord ++ tailWord_3478236) baseStart_3478236 baseEnd_3478236 := by
    simpa [prefixWord, tailWord_3478236, baseEnd_3478236] using wordTrace_append hprefix tailTrace_3478236
  have hstable : (prefixWord ++ tailWord_3478236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478236).length < 2 ^ (prefixWord ++ tailWord_3478236).sum := by decide
  have hdescent : baseEnd_3478236 < baseStart_3478236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478256 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_3478256 : Nat := 118140960795 + 3478256 * 2 ^ 59
def prefixEnd_3478256 : Nat := 4983230072969 + 3 ^ 40 * 3478256 * 2
def baseEnd_3478256 : Nat := 1190678111590032360735865

theorem tailTrace_3478256 : CollatzResearch.WordTrace tailWord_3478256 prefixEnd_3478256 1190678111590032360735865 := by
  unfold tailWord_3478256
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431209243440012838031311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84574945657920017117375081 63431209243440012838031311)
  ·
    refine ⟨95146813865160019257046967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63431209243440012838031311 95146813865160019257046967)
    ·
      refine ⟨142720220797740028885570451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95146813865160019257046967 142720220797740028885570451)
      ·
        refine ⟨214080331196610043328355677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142720220797740028885570451 214080331196610043328355677)
        ·
          refine ⟨80280124198728766248133379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214080331196610043328355677 80280124198728766248133379)
          ·
            refine ⟨120420186298093149372200069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80280124198728766248133379 120420186298093149372200069)
            ·
              refine ⟨22578784930892465507287513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120420186298093149372200069 22578784930892465507287513)
              ·
                refine ⟨16934088698169349130465635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22578784930892465507287513 16934088698169349130465635)
                ·
                  refine ⟨25401133047254023695698453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16934088698169349130465635 25401133047254023695698453)
                  ·
                    refine ⟨1190678111590032360735865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25401133047254023695698453 1190678111590032360735865)
                    ·
                      rfl

theorem cell22_3478256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_3478256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478256 prefixEnd_3478256 := by exact prefixLift 3478256
  have htrace : WordTrace (prefixWord ++ tailWord_3478256) baseStart_3478256 baseEnd_3478256 := by
    simpa [prefixWord, tailWord_3478256, baseEnd_3478256] using wordTrace_append hprefix tailTrace_3478256
  have hstable : (prefixWord ++ tailWord_3478256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478256).length < 2 ^ (prefixWord ++ tailWord_3478256).sum := by decide
  have hdescent : baseEnd_3478256 < baseStart_3478256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478258 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3478258 : Nat := 118140960795 + 3478258 * 2 ^ 59
def prefixEnd_3478258 : Nat := 4983230072969 + 3 ^ 40 * 3478258 * 2
def baseEnd_3478258 : Nat := 1190678796230905022185859

theorem tailTrace_3478258 : CollatzResearch.WordTrace tailWord_3478258 prefixEnd_3478258 1190678796230905022185859 := by
  unfold tailWord_3478258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31715622858218195004408857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84574994288581853345090285 31715622858218195004408857)
  ·
    refine ⟨23786717143663646253306643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31715622858218195004408857 23786717143663646253306643)
    ·
      refine ⟨35680075715495469379959965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23786717143663646253306643 35680075715495469379959965)
      ·
        refine ⟨13380028393310801017484987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35680075715495469379959965 13380028393310801017484987)
        ·
          refine ⟨20070042589966201526227481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380028393310801017484987 20070042589966201526227481)
          ·
            refine ⟨15052531942474651144670611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20070042589966201526227481 15052531942474651144670611)
            ·
              refine ⟨22578797913711976717005917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15052531942474651144670611 22578797913711976717005917)
              ·
                refine ⟨8467049217641991268877219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22578797913711976717005917 8467049217641991268877219)
                ·
                  refine ⟨12700573826462986903315829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467049217641991268877219 12700573826462986903315829)
                  ·
                    refine ⟨1190678796230905022185859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12700573826462986903315829 1190678796230905022185859)
                    ·
                      rfl

theorem cell22_3478258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3478258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478258 prefixEnd_3478258 := by exact prefixLift 3478258
  have htrace : WordTrace (prefixWord ++ tailWord_3478258) baseStart_3478258 baseEnd_3478258 := by
    simpa [prefixWord, tailWord_3478258, baseEnd_3478258] using wordTrace_append hprefix tailTrace_3478258
  have hstable : (prefixWord ++ tailWord_3478258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478258).length < 2 ^ (prefixWord ++ tailWord_3478258).sum := by decide
  have hdescent : baseEnd_3478258 < baseStart_3478258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478354 : List Nat := [3, 2, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3478354 : Nat := 118140960795 + 3478354 * 2 ^ 59
def prefixEnd_3478354 : Nat := 4983230072969 + 3 ^ 40 * 3478354 * 2
def baseEnd_3478354 : Nat := 1190711658992792771785565

theorem tailTrace_3478354 : CollatzResearch.WordTrace tailWord_3478354 prefixEnd_3478354 1190711658992792771785565 := by
  unfold tailWord_3478354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31716498210131247103282529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84577328560349992275420077 31716498210131247103282529)
  ·
    refine ⟨23787373657598435327461897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31716498210131247103282529 23787373657598435327461897)
    ·
      refine ⟨17840530243198826495596423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23787373657598435327461897 17840530243198826495596423)
      ·
        refine ⟨26760795364798239743394635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17840530243198826495596423 26760795364798239743394635)
        ·
          refine ⟨40141193047197359615091953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26760795364798239743394635 40141193047197359615091953)
          ·
            refine ⟨30105894785398019711318965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40141193047197359615091953 30105894785398019711318965)
            ·
              refine ⟨2822427636131064347936153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30105894785398019711318965 2822427636131064347936153)
              ·
                refine ⟨2116820727098298260952115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822427636131064347936153 2116820727098298260952115)
                ·
                  refine ⟨3175231090647447391428173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116820727098298260952115 3175231090647447391428173)
                  ·
                    refine ⟨1190711658992792771785565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175231090647447391428173 1190711658992792771785565)
                    ·
                      rfl

theorem cell22_3478354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3478354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478354 prefixEnd_3478354 := by exact prefixLift 3478354
  have htrace : WordTrace (prefixWord ++ tailWord_3478354) baseStart_3478354 baseEnd_3478354 := by
    simpa [prefixWord, tailWord_3478354, baseEnd_3478354] using wordTrace_append hprefix tailTrace_3478354
  have hstable : (prefixWord ++ tailWord_3478354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478354).length < 2 ^ (prefixWord ++ tailWord_3478354).sum := by decide
  have hdescent : baseEnd_3478354 < baseStart_3478354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478393 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_3478393 : Nat := 118140960795 + 3478393 * 2 ^ 59
def prefixEnd_3478393 : Nat := 4983230072969 + 3 ^ 40 * 3478393 * 2
def baseEnd_3478393 : Nat := 1190725009489809670060445

theorem tailTrace_3478393 : CollatzResearch.WordTrace tailWord_3478393 prefixEnd_3478393 1190725009489809670060445 := by
  unfold tailWord_3478393
  simp only [CollatzResearch.WordTrace]
  refine ⟨126867415287383698073799833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84578276858255798715866555 126867415287383698073799833)
  ·
    refine ⟨95150561465537773555349875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126867415287383698073799833 95150561465537773555349875)
    ·
      refine ⟨142725842198306660333024813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95150561465537773555349875 142725842198306660333024813)
      ·
        refine ⟨53522190824364997624884305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142725842198306660333024813 53522190824364997624884305)
        ·
          refine ⟨40141643118273748218663229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53522190824364997624884305 40141643118273748218663229)
          ·
            refine ⟨15053116169352655581998711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40141643118273748218663229 15053116169352655581998711)
            ·
              refine ⟨22579674254028983372998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053116169352655581998711 22579674254028983372998067)
              ·
                refine ⟨33869511381043475059497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22579674254028983372998067 33869511381043475059497101)
                ·
                  refine ⟨12701066767891303147311413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33869511381043475059497101 12701066767891303147311413)
                  ·
                    refine ⟨1190725009489809670060445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12701066767891303147311413 1190725009489809670060445)
                    ·
                      rfl

theorem cell22_3478393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_3478393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478393 prefixEnd_3478393 := by exact prefixLift 3478393
  have htrace : WordTrace (prefixWord ++ tailWord_3478393) baseStart_3478393 baseEnd_3478393 := by
    simpa [prefixWord, tailWord_3478393, baseEnd_3478393] using wordTrace_append hprefix tailTrace_3478393
  have hstable : (prefixWord ++ tailWord_3478393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478393).length < 2 ^ (prefixWord ++ tailWord_3478393).sum := by decide
  have hdescent : baseEnd_3478393 < baseStart_3478393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478412 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 4]
def baseStart_3478412 : Nat := 118140960795 + 3478412 * 2 ^ 59
def prefixEnd_3478412 : Nat := 4983230072969 + 3 ^ 40 * 3478412 * 2
def baseEnd_3478412 : Nat := 396910504526033317945129

theorem tailTrace_3478412 : CollatzResearch.WordTrace tailWord_3478412 prefixEnd_3478412 396910504526033317945129 := by
  unfold tailWord_3478412
  simp only [CollatzResearch.WordTrace]
  refine ⟨63434054137157432159370745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84578738849543242879160993 63434054137157432159370745)
  ·
    refine ⟨47575540602868074119528059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63434054137157432159370745 47575540602868074119528059)
    ·
      refine ⟨71363310904302111179292089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47575540602868074119528059 71363310904302111179292089)
      ·
        refine ⟨53522483178226583384469067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71363310904302111179292089 53522483178226583384469067)
        ·
          refine ⟨80283724767339875076703601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53522483178226583384469067 80283724767339875076703601)
          ·
            refine ⟨60212793575504906307527701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80283724767339875076703601 60212793575504906307527701)
            ·
              refine ⟨2822474698851792483165361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60212793575504906307527701 2822474698851792483165361)
              ·
                refine ⟨2116856024138844362374021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822474698851792483165361 2116856024138844362374021)
                ·
                  refine ⟨396910504526033317945129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116856024138844362374021 396910504526033317945129)
                  ·
                    rfl

theorem cell22_3478412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_3478412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478412 prefixEnd_3478412 := by exact prefixLift 3478412
  have htrace : WordTrace (prefixWord ++ tailWord_3478412) baseStart_3478412 baseEnd_3478412 := by
    simpa [prefixWord, tailWord_3478412, baseEnd_3478412] using wordTrace_append hprefix tailTrace_3478412
  have hstable : (prefixWord ++ tailWord_3478412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478412).length < 2 ^ (prefixWord ++ tailWord_3478412).sum := by decide
  have hdescent : baseEnd_3478412 < baseStart_3478412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478461 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_3478461 : Nat := 118140960795 + 3478461 * 2 ^ 59
def prefixEnd_3478461 : Nat := 4983230072969 + 3 ^ 40 * 3478461 * 2
def baseEnd_3478461 : Nat := 1190748287279480159360237

theorem tailTrace_3478461 : CollatzResearch.WordTrace tailWord_3478461 prefixEnd_3478461 1190748287279480159360237 := by
  unfold tailWord_3478461
  simp only [CollatzResearch.WordTrace]
  refine ⟨126869895451137345687275237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84579930300758230458183491 126869895451137345687275237)
  ·
    refine ⟨23788105397088252316364107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126869895451137345687275237 23788105397088252316364107)
    ·
      refine ⟨35682158095632378474546161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23788105397088252316364107 35682158095632378474546161)
      ·
        refine ⟨26761618571724283855909621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35682158095632378474546161 26761618571724283855909621)
        ·
          refine ⟨2508901741099151611491527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26761618571724283855909621 2508901741099151611491527)
          ·
            refine ⟨3763352611648727417237291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508901741099151611491527 3763352611648727417237291)
            ·
              refine ⟨5645028917473091125855937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763352611648727417237291 5645028917473091125855937)
              ·
                refine ⟨4233771688104818344391953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645028917473091125855937 4233771688104818344391953)
                ·
                  refine ⟨3175328766078613758293965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4233771688104818344391953 3175328766078613758293965)
                  ·
                    refine ⟨1190748287279480159360237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175328766078613758293965 1190748287279480159360237)
                    ·
                      rfl

theorem cell22_3478461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_3478461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478461 prefixEnd_3478461 := by exact prefixLift 3478461
  have htrace : WordTrace (prefixWord ++ tailWord_3478461) baseStart_3478461 baseEnd_3478461 := by
    simpa [prefixWord, tailWord_3478461, baseEnd_3478461] using wordTrace_append hprefix tailTrace_3478461
  have hstable : (prefixWord ++ tailWord_3478461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478461).length < 2 ^ (prefixWord ++ tailWord_3478461).sum := by decide
  have hdescent : baseEnd_3478461 < baseStart_3478461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478506 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3478506 : Nat := 118140960795 + 3478506 * 2 ^ 59
def prefixEnd_3478506 : Nat := 4983230072969 + 3 ^ 40 * 3478506 * 2
def baseEnd_3478506 : Nat := 1190763691699115041985099

theorem tailTrace_3478506 : CollatzResearch.WordTrace tailWord_3478506 prefixEnd_3478506 1190763691699115041985099 := by
  unfold tailWord_3478506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31717884183993579593165843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84581024490649545581775581 31717884183993579593165843)
  ·
    refine ⟨47576826275990369389748765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31717884183993579593165843 47576826275990369389748765)
    ·
      refine ⟨17841309853496388521155787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47576826275990369389748765 17841309853496388521155787)
      ·
        refine ⟨26761964780244582781733681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841309853496388521155787 26761964780244582781733681)
        ·
          refine ⟨20071473585183437086300261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26761964780244582781733681 20071473585183437086300261)
          ·
            refine ⟨3763401297221894453681299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20071473585183437086300261 3763401297221894453681299)
            ·
              refine ⟨5645101945832841680521949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763401297221894453681299 5645101945832841680521949)
              ·
                refine ⟨2116913229687315630195731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645101945832841680521949 2116913229687315630195731)
                ·
                  refine ⟨3175369844530973445293597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116913229687315630195731 3175369844530973445293597)
                  ·
                    refine ⟨1190763691699115041985099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175369844530973445293597 1190763691699115041985099)
                    ·
                      rfl

theorem cell22_3478506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3478506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478506 prefixEnd_3478506 := by exact prefixLift 3478506
  have htrace : WordTrace (prefixWord ++ tailWord_3478506) baseStart_3478506 baseEnd_3478506 := by
    simpa [prefixWord, tailWord_3478506, baseEnd_3478506] using wordTrace_append hprefix tailTrace_3478506
  have hstable : (prefixWord ++ tailWord_3478506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478506).length < 2 ^ (prefixWord ++ tailWord_3478506).sum := by decide
  have hdescent : baseEnd_3478506 < baseStart_3478506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478549 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3478549 : Nat := 118140960795 + 3478549 * 2 ^ 59
def prefixEnd_3478549 : Nat := 4983230072969 + 3 ^ 40 * 3478549 * 2
def baseEnd_3478549 : Nat := 1190778411477877263159967

theorem tailTrace_3478549 : CollatzResearch.WordTrace tailWord_3478549 prefixEnd_3478549 1190778411477877263159967 := by
  unfold tailWord_3478549
  simp only [CollatzResearch.WordTrace]
  refine ⟨126873105074818536716478701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84582070049879024477652467 126873105074818536716478701)
  ·
    refine ⟨47577414403056951268679513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126873105074818536716478701 47577414403056951268679513)
    ·
      refine ⟨35683060802292713451509635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47577414403056951268679513 35683060802292713451509635)
      ·
        refine ⟨53524591203439070177264453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35683060802292713451509635 53524591203439070177264453)
        ·
          refine ⟨10035860850644825658237085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53524591203439070177264453 10035860850644825658237085)
          ·
            refine ⟨3763447818991809621838907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10035860850644825658237085 3763447818991809621838907)
            ·
              refine ⟨5645171728487714432758361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763447818991809621838907 5645171728487714432758361)
              ·
                refine ⟨4233878796365785824568771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645171728487714432758361 4233878796365785824568771)
                ·
                  refine ⟨6350818194548678736853157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233878796365785824568771 6350818194548678736853157)
                  ·
                    refine ⟨1190778411477877263159967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6350818194548678736853157 1190778411477877263159967)
                    ·
                      rfl

theorem cell22_3478549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3478549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478549 prefixEnd_3478549 := by exact prefixLift 3478549
  have htrace : WordTrace (prefixWord ++ tailWord_3478549) baseStart_3478549 baseEnd_3478549 := by
    simpa [prefixWord, tailWord_3478549, baseEnd_3478549] using wordTrace_append hprefix tailTrace_3478549
  have hstable : (prefixWord ++ tailWord_3478549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478549).length < 2 ^ (prefixWord ++ tailWord_3478549).sum := by decide
  have hdescent : baseEnd_3478549 < baseStart_3478549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478562 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3478562 : Nat := 118140960795 + 3478562 * 2 ^ 59
def prefixEnd_3478562 : Nat := 4983230072969 + 3 ^ 40 * 3478562 * 2
def baseEnd_3478562 : Nat := 1190782861643549562584927

theorem tailTrace_3478562 : CollatzResearch.WordTrace tailWord_3478562 prefixEnd_3478562 1190782861643549562584927 := by
  unfold tailWord_3478562
  simp only [CollatzResearch.WordTrace]
  refine ⟨31718394805942859984175485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84582386149180959957801293 31718394805942859984175485)
  ·
    refine ⟨11894398052228572494065807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31718394805942859984175485 11894398052228572494065807)
    ·
      refine ⟨17841597078342858741098711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894398052228572494065807 17841597078342858741098711)
      ·
        refine ⟨26762395617514288111648067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841597078342858741098711 26762395617514288111648067)
        ·
          refine ⟨40143593426271432167472101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26762395617514288111648067 40143593426271432167472101)
          ·
            refine ⟨7526923767425893531401019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40143593426271432167472101 7526923767425893531401019)
            ·
              refine ⟨11290385651138840297101529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526923767425893531401019 11290385651138840297101529)
              ·
                refine ⟨8467789238354130222826147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11290385651138840297101529 8467789238354130222826147)
                ·
                  refine ⟨12701683857531195334239221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467789238354130222826147 12701683857531195334239221)
                  ·
                    refine ⟨1190782861643549562584927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12701683857531195334239221 1190782861643549562584927)
                    ·
                      rfl

theorem cell22_3478562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3478562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478562 prefixEnd_3478562 := by exact prefixLift 3478562
  have htrace : WordTrace (prefixWord ++ tailWord_3478562) baseStart_3478562 baseEnd_3478562 := by
    simpa [prefixWord, tailWord_3478562, baseEnd_3478562] using wordTrace_append hprefix tailTrace_3478562
  have hstable : (prefixWord ++ tailWord_3478562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478562).length < 2 ^ (prefixWord ++ tailWord_3478562).sum := by decide
  have hdescent : baseEnd_3478562 < baseStart_3478562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478637 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3478637 : Nat := 118140960795 + 3478637 * 2 ^ 59
def prefixEnd_3478637 : Nat := 4983230072969 + 3 ^ 40 * 3478637 * 2
def baseEnd_3478637 : Nat := 396936178558758122319899

theorem tailTrace_3478637 : CollatzResearch.WordTrace tailWord_3478637 prefixEnd_3478637 396936178558758122319899 := by
  unfold tailWord_3478637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126876314698499727745682165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84584209798999818497121443 126876314698499727745682165)
  ·
    refine ⟨11894654502984349476157703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126876314698499727745682165 11894654502984349476157703)
    ·
      refine ⟨17841981754476524214236555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894654502984349476157703 17841981754476524214236555)
      ·
        refine ⟨26762972631714786321354833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841981754476524214236555 26762972631714786321354833)
        ·
          refine ⟨20072229473786089741016125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26762972631714786321354833 20072229473786089741016125)
          ·
            refine ⟨7527086052669783652881047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20072229473786089741016125 7527086052669783652881047)
            ·
              refine ⟨11290629079004675479321571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527086052669783652881047 11290629079004675479321571)
              ·
                refine ⟨16935943618507013218982357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11290629079004675479321571 16935943618507013218982357)
                ·
                  refine ⟨396936178558758122319899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16935943618507013218982357 396936178558758122319899)
                  ·
                    rfl

theorem cell22_3478637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3478637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478637 prefixEnd_3478637 := by exact prefixLift 3478637
  have htrace : WordTrace (prefixWord ++ tailWord_3478637) baseStart_3478637 baseEnd_3478637 := by
    simpa [prefixWord, tailWord_3478637, baseEnd_3478637] using wordTrace_append hprefix tailTrace_3478637
  have hstable : (prefixWord ++ tailWord_3478637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478637).length < 2 ^ (prefixWord ++ tailWord_3478637).sum := by decide
  have hdescent : baseEnd_3478637 < baseStart_3478637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478684 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3478684 : Nat := 118140960795 + 3478684 * 2 ^ 59
def prefixEnd_3478684 : Nat := 4983230072969 + 3 ^ 40 * 3478684 * 2
def baseEnd_3478684 : Nat := 1190824624736781911034553

theorem tailTrace_3478684 : CollatzResearch.WordTrace tailWord_3478684 prefixEnd_3478684 1190824624736781911034553 := by
  unfold tailWord_3478684
  simp only [CollatzResearch.WordTrace]
  refine ⟨63439014464664727386321553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84585352619552969848428737 63439014464664727386321553)
  ·
    refine ⟨47579260848498545539741165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63439014464664727386321553 47579260848498545539741165)
    ·
      refine ⟨17842222818186954577402937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47579260848498545539741165 17842222818186954577402937)
      ·
        refine ⟨13381667113640215933052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17842222818186954577402937 13381667113640215933052203)
        ·
          refine ⟨20072500670460323899578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381667113640215933052203 20072500670460323899578305)
          ·
            refine ⟨15054375502845242924683729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20072500670460323899578305 15054375502845242924683729)
            ·
              refine ⟨11290781627133932193512797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15054375502845242924683729 11290781627133932193512797)
              ·
                refine ⟨4234043110175224572567299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11290781627133932193512797 4234043110175224572567299)
                ·
                  refine ⟨6351064665262836858850949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234043110175224572567299 6351064665262836858850949)
                  ·
                    refine ⟨1190824624736781911034553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351064665262836858850949 1190824624736781911034553)
                    ·
                      rfl

theorem cell22_3478684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3478684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478684 prefixEnd_3478684 := by exact prefixLift 3478684
  have htrace : WordTrace (prefixWord ++ tailWord_3478684) baseStart_3478684 baseEnd_3478684 := by
    simpa [prefixWord, tailWord_3478684, baseEnd_3478684] using wordTrace_append hprefix tailTrace_3478684
  have hstable : (prefixWord ++ tailWord_3478684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478684).length < 2 ^ (prefixWord ++ tailWord_3478684).sum := by decide
  have hdescent : baseEnd_3478684 < baseStart_3478684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478834 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3478834 : Nat := 118140960795 + 3478834 * 2 ^ 59
def prefixEnd_3478834 : Nat := 4983230072969 + 3 ^ 40 * 3478834 * 2
def baseEnd_3478834 : Nat := 396958657600743839928031

theorem tailTrace_3478834 : CollatzResearch.WordTrace tailWord_3478834 prefixEnd_3478834 396958657600743839928031 := by
  unfold tailWord_3478834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31720874969696507597650889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84588999919190686927069037 31720874969696507597650889)
  ·
    refine ⟨23790656227272380698238167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31720874969696507597650889 23790656227272380698238167)
    ·
      refine ⟨35685984340908571047357251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23790656227272380698238167 35685984340908571047357251)
      ·
        refine ⟨53528976511362856571035877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35685984340908571047357251 53528976511362856571035877)
        ·
          refine ⟨10036683095880535607069227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53528976511362856571035877 10036683095880535607069227)
          ·
            refine ⟨15055024643820803410603841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036683095880535607069227 15055024643820803410603841)
            ·
              refine ⟨11291268482865602557952881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055024643820803410603841 11291268482865602557952881)
              ·
                refine ⟨8468451362149201918464661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291268482865602557952881 8468451362149201918464661)
                ·
                  refine ⟨396958657600743839928031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8468451362149201918464661 396958657600743839928031)
                  ·
                    rfl

theorem cell22_3478834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3478834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478834 prefixEnd_3478834 := by exact prefixLift 3478834
  have htrace : WordTrace (prefixWord ++ tailWord_3478834) baseStart_3478834 baseEnd_3478834 := by
    simpa [prefixWord, tailWord_3478834, baseEnd_3478834] using wordTrace_append hprefix tailTrace_3478834
  have hstable : (prefixWord ++ tailWord_3478834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478834).length < 2 ^ (prefixWord ++ tailWord_3478834).sum := by decide
  have hdescent : baseEnd_3478834 < baseStart_3478834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478864 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_3478864 : Nat := 118140960795 + 3478864 * 2 ^ 59
def prefixEnd_3478864 : Nat := 4983230072969 + 3 ^ 40 * 3478864 * 2
def baseEnd_3478864 : Nat := 1190886242415321441534001

theorem tailTrace_3478864 : CollatzResearch.WordTrace tailWord_3478864 prefixEnd_3478864 1190886242415321441534001 := by
  unfold tailWord_3478864
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442297034338672757097823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84589729379118230342797097 63442297034338672757097823)
  ·
    refine ⟨95163445551508009135646735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63442297034338672757097823 95163445551508009135646735)
    ·
      refine ⟨142745168327262013703470103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95163445551508009135646735 142745168327262013703470103)
      ·
        refine ⟨214117752490893020555205155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142745168327262013703470103 214117752490893020555205155)
        ·
          refine ⟨321176628736339530832807733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214117752490893020555205155 321176628736339530832807733)
          ·
            refine ⟨30110308944031831015575725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321176628736339530832807733 30110308944031831015575725)
            ·
              refine ⟨11291365854011936630840897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30110308944031831015575725 11291365854011936630840897)
              ·
                refine ⟨8468524390508952473130673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291365854011936630840897 8468524390508952473130673)
                ·
                  refine ⟨6351393292881714354848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468524390508952473130673 6351393292881714354848005)
                  ·
                    refine ⟨1190886242415321441534001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351393292881714354848005 1190886242415321441534001)
                    ·
                      rfl

theorem cell22_3478864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_3478864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478864 prefixEnd_3478864 := by exact prefixLift 3478864
  have htrace : WordTrace (prefixWord ++ tailWord_3478864) baseStart_3478864 baseEnd_3478864 := by
    simpa [prefixWord, tailWord_3478864, baseEnd_3478864] using wordTrace_append hprefix tailTrace_3478864
  have hstable : (prefixWord ++ tailWord_3478864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478864).length < 2 ^ (prefixWord ++ tailWord_3478864).sum := by decide
  have hdescent : baseEnd_3478864 < baseStart_3478864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478866 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_3478866 : Nat := 118140960795 + 3478866 * 2 ^ 59
def prefixEnd_3478866 : Nat := 4983230072969 + 3 ^ 40 * 3478866 * 2
def baseEnd_3478866 : Nat := 1190886927056194102983995

theorem tailTrace_3478866 : CollatzResearch.WordTrace tailWord_3478866 prefixEnd_3478866 1190886927056194102983995 := by
  unfold tailWord_3478866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721166753667524963942113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84589778009780066570512301 31721166753667524963942113)
  ·
    refine ⟨23790875065250643722956585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31721166753667524963942113 23790875065250643722956585)
    ·
      refine ⟨17843156298937982792217439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23790875065250643722956585 17843156298937982792217439)
      ·
        refine ⟨26764734448406974188326159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843156298937982792217439 26764734448406974188326159)
        ·
          refine ⟨40147101672610461282489239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26764734448406974188326159 40147101672610461282489239)
          ·
            refine ⟨60220652508915691923733859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40147101672610461282489239 60220652508915691923733859)
            ·
              refine ⟨90330978763373537885600789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60220652508915691923733859 90330978763373537885600789)
              ·
                refine ⟨4234264629533134588387537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90330978763373537885600789 4234264629533134588387537)
                ·
                  refine ⟨3175698472149850941290653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234264629533134588387537 3175698472149850941290653)
                  ·
                    refine ⟨1190886927056194102983995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175698472149850941290653 1190886927056194102983995)
                    ·
                      rfl

theorem cell22_3478866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_3478866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478866 prefixEnd_3478866 := by exact prefixLift 3478866
  have htrace : WordTrace (prefixWord ++ tailWord_3478866) baseStart_3478866 baseEnd_3478866 := by
    simpa [prefixWord, tailWord_3478866, baseEnd_3478866] using wordTrace_append hprefix tailTrace_3478866
  have hstable : (prefixWord ++ tailWord_3478866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478866).length < 2 ^ (prefixWord ++ tailWord_3478866).sum := by decide
  have hdescent : baseEnd_3478866 < baseStart_3478866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478868 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 4]
def baseStart_3478868 : Nat := 118140960795 + 3478868 * 2 ^ 59
def prefixEnd_3478868 : Nat := 4983230072969 + 3 ^ 40 * 3478868 * 2
def baseEnd_3478868 : Nat := 396962537232355588144663

theorem tailTrace_3478868 : CollatzResearch.WordTrace tailWord_3478868 prefixEnd_3478868 396962537232355588144663 := by
  unfold tailWord_3478868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63442369980331427098670629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84589826640441902798227505 63442369980331427098670629)
  ·
    refine ⟨11895444371312142581000743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63442369980331427098670629 11895444371312142581000743)
    ·
      refine ⟨17843166556968213871501115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11895444371312142581000743 17843166556968213871501115)
      ·
        refine ⟨26764749835452320807251673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843166556968213871501115 26764749835452320807251673)
        ·
          refine ⟨20073562376589240605438755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26764749835452320807251673 20073562376589240605438755)
          ·
            refine ⟨30110343564883860908158133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073562376589240605438755 30110343564883860908158133)
            ·
              refine ⟨2822844709207861960139825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30110343564883860908158133 2822844709207861960139825)
              ·
                refine ⟨2117133531905896470104869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822844709207861960139825 2117133531905896470104869)
                ·
                  refine ⟨396962537232355588144663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117133531905896470104869 396962537232355588144663)
                  ·
                    rfl

theorem cell22_3478868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_3478868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478868 prefixEnd_3478868 := by exact prefixLift 3478868
  have htrace : WordTrace (prefixWord ++ tailWord_3478868) baseStart_3478868 baseEnd_3478868 := by
    simpa [prefixWord, tailWord_3478868, baseEnd_3478868] using wordTrace_append hprefix tailTrace_3478868
  have hstable : (prefixWord ++ tailWord_3478868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478868).length < 2 ^ (prefixWord ++ tailWord_3478868).sum := by decide
  have hdescent : baseEnd_3478868 < baseStart_3478868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478883 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 2, 3]
def baseStart_3478883 : Nat := 118140960795 + 3478883 * 2 ^ 59
def prefixEnd_3478883 : Nat := 4983230072969 + 3 ^ 40 * 3478883 * 2
def baseEnd_3478883 : Nat := 1190892746503611725308943

theorem tailTrace_3478883 : CollatzResearch.WordTrace tailWord_3478883 prefixEnd_3478883 1190892746503611725308943 := by
  unfold tailWord_3478883
  simp only [CollatzResearch.WordTrace]
  refine ⟨126885287055608511759137303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84590191370405674506091535 126885287055608511759137303)
  ·
    refine ⟨190327930583412767638705955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126885287055608511759137303 190327930583412767638705955)
    ·
      refine ⟨285491895875119151458058933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190327930583412767638705955 285491895875119151458058933)
      ·
        refine ⟨26764865238292420449193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285491895875119151458058933 26764865238292420449193025)
        ·
          refine ⟨20073648928719315336894769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26764865238292420449193025 20073648928719315336894769)
          ·
            refine ⟨15055236696539486502671077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20073648928719315336894769 15055236696539486502671077)
            ·
              refine ⟨2822856880601153719250827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15055236696539486502671077 2822856880601153719250827)
              ·
                refine ⟨4234285320901730578876241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822856880601153719250827 4234285320901730578876241)
                ·
                  refine ⟨3175713990676297934157181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234285320901730578876241 3175713990676297934157181)
                  ·
                    refine ⟨1190892746503611725308943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175713990676297934157181 1190892746503611725308943)
                    ·
                      rfl

theorem cell22_3478883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 3].length) (baseStart_3478883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478883 prefixEnd_3478883 := by exact prefixLift 3478883
  have htrace : WordTrace (prefixWord ++ tailWord_3478883) baseStart_3478883 baseEnd_3478883 := by
    simpa [prefixWord, tailWord_3478883, baseEnd_3478883] using wordTrace_append hprefix tailTrace_3478883
  have hstable : (prefixWord ++ tailWord_3478883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478883).length < 2 ^ (prefixWord ++ tailWord_3478883).sum := by decide
  have hdescent : baseEnd_3478883 < baseStart_3478883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478930 : List Nat := [3, 2, 3, 3, 2, 1, 1, 7]
def baseStart_3478930 : Nat := 118140960795 + 3478930 * 2 ^ 59
def prefixEnd_3478930 : Nat := 4983230072969 + 3 ^ 40 * 3478930 * 2
def baseEnd_3478930 : Nat := 132323203951568807709311

theorem tailTrace_3478930 : CollatzResearch.WordTrace tailWord_3478930 prefixEnd_3478930 132323203951568807709311 := by
  unfold tailWord_3478930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721750321609559696524561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84591334190958825857398829 31721750321609559696524561)
  ·
    refine ⟨23791312741207169772393421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31721750321609559696524561 23791312741207169772393421)
    ·
      refine ⟨8921742277952688664647533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23791312741207169772393421 8921742277952688664647533)
      ·
        refine ⟨3345653354232258249242825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8921742277952688664647533 3345653354232258249242825)
        ·
          refine ⟨2509240015674193686932119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345653354232258249242825 2509240015674193686932119)
          ·
            refine ⟨3763860023511290530398179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509240015674193686932119 3763860023511290530398179)
            ·
              refine ⟨5645790035266935795597269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763860023511290530398179 5645790035266935795597269)
              ·
                refine ⟨132323203951568807709311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5645790035266935795597269 132323203951568807709311)
                ·
                  rfl

theorem cell22_3478930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_3478930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478930 prefixEnd_3478930 := by exact prefixLift 3478930
  have htrace : WordTrace (prefixWord ++ tailWord_3478930) baseStart_3478930 baseEnd_3478930 := by
    simpa [prefixWord, tailWord_3478930, baseEnd_3478930] using wordTrace_append hprefix tailTrace_3478930
  have hstable : (prefixWord ++ tailWord_3478930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478930).length < 2 ^ (prefixWord ++ tailWord_3478930).sum := by decide
  have hdescent : baseEnd_3478930 < baseStart_3478930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478941 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3478941 : Nat := 118140960795 + 3478941 * 2 ^ 59
def prefixEnd_3478941 : Nat := 4983230072969 + 3 ^ 40 * 3478941 * 2
def baseEnd_3478941 : Nat := 396970867029639635786255

theorem tailTrace_3478941 : CollatzResearch.WordTrace tailWord_3478941 prefixEnd_3478941 396970867029639635786255 := by
  unfold tailWord_3478941
  simp only [CollatzResearch.WordTrace]
  refine ⟨126887402489398387664748677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84591601659598925109832451 126887402489398387664748677)
  ·
    refine ⟨23791387966762197687140377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126887402489398387664748677 23791387966762197687140377)
    ·
      refine ⟨17843540975071648265355283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23791387966762197687140377 17843540975071648265355283)
      ·
        refine ⟨26765311462607472398032925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843540975071648265355283 26765311462607472398032925)
        ·
          refine ⟨10036991798477802149262347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26765311462607472398032925 10036991798477802149262347)
          ·
            refine ⟨15055487697716703223893521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036991798477802149262347 15055487697716703223893521)
            ·
              refine ⟨11291615773287527417920141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15055487697716703223893521 11291615773287527417920141)
              ·
                refine ⟨4234355914982822781720053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11291615773287527417920141 4234355914982822781720053)
                ·
                  refine ⟨396970867029639635786255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4234355914982822781720053 396970867029639635786255)
                  ·
                    rfl

theorem cell22_3478941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3478941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478941 prefixEnd_3478941 := by exact prefixLift 3478941
  have htrace : WordTrace (prefixWord ++ tailWord_3478941) baseStart_3478941 baseEnd_3478941 := by
    simpa [prefixWord, tailWord_3478941, baseEnd_3478941] using wordTrace_append hprefix tailTrace_3478941
  have hstable : (prefixWord ++ tailWord_3478941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478941).length < 2 ^ (prefixWord ++ tailWord_3478941).sum := by decide
  have hdescent : baseEnd_3478941 < baseStart_3478941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478986 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_3478986 : Nat := 118140960795 + 3478986 * 2 ^ 59
def prefixEnd_3478986 : Nat := 4983230072969 + 3 ^ 40 * 3478986 * 2
def baseEnd_3478986 : Nat := 396976001836184596661209

theorem tailTrace_3478986 : CollatzResearch.WordTrace tailWord_3478986 prefixEnd_3478986 396976001836184596661209 := by
  unfold tailWord_3478986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722260943558840087534203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84592695849490240233424541 31722260943558840087534203)
  ·
    refine ⟨47583391415338260131301305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31722260943558840087534203 47583391415338260131301305)
    ·
      refine ⟨35687543561503695098475979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47583391415338260131301305 35687543561503695098475979)
      ·
        refine ⟨53531315342255542647713969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35687543561503695098475979 53531315342255542647713969)
        ·
          refine ⟨40148486506691656985785477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53531315342255542647713969 40148486506691656985785477)
          ·
            refine ⟨7527841220004685684834777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40148486506691656985785477 7527841220004685684834777)
            ·
              refine ⟨5645880915003514263626083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7527841220004685684834777 5645880915003514263626083)
              ·
                refine ⟨8468821372505271395439125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645880915003514263626083 8468821372505271395439125)
                ·
                  refine ⟨396976001836184596661209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8468821372505271395439125 396976001836184596661209)
                  ·
                    rfl

theorem cell22_3478986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_3478986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478986 prefixEnd_3478986 := by exact prefixLift 3478986
  have htrace : WordTrace (prefixWord ++ tailWord_3478986) baseStart_3478986 baseEnd_3478986 := by
    simpa [prefixWord, tailWord_3478986, baseEnd_3478986] using wordTrace_append hprefix tailTrace_3478986
  have hstable : (prefixWord ++ tailWord_3478986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478986).length < 2 ^ (prefixWord ++ tailWord_3478986).sum := by decide
  have hdescent : baseEnd_3478986 < baseStart_3478986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479001 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_3479001 : Nat := 118140960795 + 3479001 * 2 ^ 59
def prefixEnd_3479001 : Nat := 4983230072969 + 3 ^ 40 * 3479001 * 2
def baseEnd_3479001 : Nat := 1190933140315098750858581

theorem tailTrace_3479001 : CollatzResearch.WordTrace tailWord_3479001 prefixEnd_3479001 1190933140315098750858581 := by
  unfold tailWord_3479001
  simp only [CollatzResearch.WordTrace]
  refine ⟨126889590869181017911932857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84593060579454011941288571 126889590869181017911932857)
  ·
    refine ⟨95167193151885763433949643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126889590869181017911932857 95167193151885763433949643)
    ·
      refine ⟨142750789727828645150924465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95167193151885763433949643 142750789727828645150924465)
      ·
        refine ⟨107063092295871483863193349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142750789727828645150924465 107063092295871483863193349)
        ·
          refine ⟨20074329805475903224348753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107063092295871483863193349 20074329805475903224348753)
          ·
            refine ⟨15055747354106927418261565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20074329805475903224348753 15055747354106927418261565)
            ·
              refine ⟨5645905257790097781848087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15055747354106927418261565 5645905257790097781848087)
              ·
                refine ⟨8468857886685146672772131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645905257790097781848087 8468857886685146672772131)
                ·
                  refine ⟨12703286830027720009158197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468857886685146672772131 12703286830027720009158197)
                  ·
                    refine ⟨1190933140315098750858581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12703286830027720009158197 1190933140315098750858581)
                    ·
                      rfl

theorem cell22_3479001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_3479001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479001 prefixEnd_3479001 := by exact prefixLift 3479001
  have htrace : WordTrace (prefixWord ++ tailWord_3479001) baseStart_3479001 baseEnd_3479001 := by
    simpa [prefixWord, tailWord_3479001, baseEnd_3479001] using wordTrace_append hprefix tailTrace_3479001
  have hstable : (prefixWord ++ tailWord_3479001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479001).length < 2 ^ (prefixWord ++ tailWord_3479001).sum := by decide
  have hdescent : baseEnd_3479001 < baseStart_3479001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479016 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3479016 : Nat := 118140960795 + 3479016 * 2 ^ 59
def prefixEnd_3479016 : Nat := 4983230072969 + 3 ^ 40 * 3479016 * 2
def baseEnd_3479016 : Nat := 1190938275121643711733535

theorem tailTrace_3479016 : CollatzResearch.WordTrace tailWord_3479016 prefixEnd_3479016 1190938275121643711733535 := by
  unfold tailWord_3479016
  simp only [CollatzResearch.WordTrace]
  refine ⟨63445068982063337736864451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84593425309417783649152601 63445068982063337736864451)
  ·
    refine ⟨95167603473095006605296677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63445068982063337736864451 95167603473095006605296677)
    ·
      refine ⟨17843925651205313738493127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95167603473095006605296677 17843925651205313738493127)
      ·
        refine ⟨26765888476807970607739691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843925651205313738493127 26765888476807970607739691)
        ·
          refine ⟨40148832715211955911609537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26765888476807970607739691 40148832715211955911609537)
          ·
            refine ⟨30111624536408966933707153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40148832715211955911609537 30111624536408966933707153)
            ·
              refine ⟨22583718402306725200280365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30111624536408966933707153 22583718402306725200280365)
              ·
                refine ⟨8468894400865021950105137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22583718402306725200280365 8468894400865021950105137)
                ·
                  refine ⟨6351670800648766462578853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468894400865021950105137 6351670800648766462578853)
                  ·
                    refine ⟨1190938275121643711733535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351670800648766462578853 1190938275121643711733535)
                    ·
                      rfl

theorem cell22_3479016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3479016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479016 prefixEnd_3479016 := by exact prefixLift 3479016
  have htrace : WordTrace (prefixWord ++ tailWord_3479016) baseStart_3479016 baseEnd_3479016 := by
    simpa [prefixWord, tailWord_3479016, baseEnd_3479016] using wordTrace_append hprefix tailTrace_3479016
  have hstable : (prefixWord ++ tailWord_3479016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479016).length < 2 ^ (prefixWord ++ tailWord_3479016).sum := by decide
  have hdescent : baseEnd_3479016 < baseStart_3479016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479052 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_3479052 : Nat := 118140960795 + 3479052 * 2 ^ 59
def prefixEnd_3479052 : Nat := 4983230072969 + 3 ^ 40 * 3479052 * 2
def baseEnd_3479052 : Nat := 1190950598657351617833425

theorem tailTrace_3479052 : CollatzResearch.WordTrace tailWord_3479052 prefixEnd_3479052 1190950598657351617833425 := by
  unfold tailWord_3479052
  simp only [CollatzResearch.WordTrace]
  refine ⟨63445725495998126811019705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84594300661330835748026273 63445725495998126811019705)
  ·
    refine ⟨47584294121998595108264779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63445725495998126811019705 47584294121998595108264779)
    ·
      refine ⟨71376441182997892662397169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47584294121998595108264779 71376441182997892662397169)
      ·
        refine ⟨53532330887248419496797877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71376441182997892662397169 53532330887248419496797877)
        ·
          refine ⟨5018656020679539327824801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53532330887248419496797877 5018656020679539327824801)
          ·
            refine ⟨3763992015509654495868601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018656020679539327824801 3763992015509654495868601)
            ·
              refine ⟨2822994011632240871901451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763992015509654495868601 2822994011632240871901451)
              ·
                refine ⟨4234491017448361307852177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822994011632240871901451 4234491017448361307852177)
                ·
                  refine ⟨3175868263086270980889133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234491017448361307852177 3175868263086270980889133)
                  ·
                    refine ⟨1190950598657351617833425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175868263086270980889133 1190950598657351617833425)
                    ·
                      rfl

theorem cell22_3479052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_3479052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479052 prefixEnd_3479052 := by exact prefixLift 3479052
  have htrace : WordTrace (prefixWord ++ tailWord_3479052) baseStart_3479052 baseEnd_3479052 := by
    simpa [prefixWord, tailWord_3479052, baseEnd_3479052] using wordTrace_append hprefix tailTrace_3479052
  have hstable : (prefixWord ++ tailWord_3479052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479052).length < 2 ^ (prefixWord ++ tailWord_3479052).sum := by decide
  have hdescent : baseEnd_3479052 < baseStart_3479052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479093 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 5]
def baseStart_3479093 : Nat := 118140960795 + 3479093 * 2 ^ 59
def prefixEnd_3479093 : Nat := 4983230072969 + 3 ^ 40 * 3479093 * 2
def baseEnd_3479093 : Nat := 396988211265080392519433

theorem tailTrace_3479093 : CollatzResearch.WordTrace tailWord_3479093 prefixEnd_3479093 396988211265080392519433 := by
  unfold tailWord_3479093
  simp only [CollatzResearch.WordTrace]
  refine ⟨126892946384847717624281933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84595297589898478416187955 126892946384847717624281933)
  ·
    refine ⟨47584854894317894109105725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126892946384847717624281933 47584854894317894109105725)
    ·
      refine ⟨17844320585369210290914647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47584854894317894109105725 17844320585369210290914647)
      ·
        refine ⟨26766480878053815436371971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844320585369210290914647 26766480878053815436371971)
        ·
          refine ⟨40149721317080723154557957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26766480878053815436371971 40149721317080723154557957)
          ·
            refine ⟨7528072746952635591479617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40149721317080723154557957 7528072746952635591479617)
            ·
              refine ⟨5646054560214476693609713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7528072746952635591479617 5646054560214476693609713)
              ·
                refine ⟨4234540920160857520207285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646054560214476693609713 4234540920160857520207285)
                ·
                  refine ⟨396988211265080392519433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4234540920160857520207285 396988211265080392519433)
                  ·
                    rfl

theorem cell22_3479093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_3479093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479093 prefixEnd_3479093 := by exact prefixLift 3479093
  have htrace : WordTrace (prefixWord ++ tailWord_3479093) baseStart_3479093 baseEnd_3479093 := by
    simpa [prefixWord, tailWord_3479093, baseEnd_3479093] using wordTrace_append hprefix tailTrace_3479093
  have hstable : (prefixWord ++ tailWord_3479093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479093).length < 2 ^ (prefixWord ++ tailWord_3479093).sum := by decide
  have hdescent : baseEnd_3479093 < baseStart_3479093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479097 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_3479097 : Nat := 118140960795 + 3479097 * 2 ^ 59
def prefixEnd_3479097 : Nat := 4983230072969 + 3 ^ 40 * 3479097 * 2
def baseEnd_3479097 : Nat := 1190966003076986500458287

theorem tailTrace_3479097 : CollatzResearch.WordTrace tailWord_3479097 prefixEnd_3479097 1190966003076986500458287 := by
  unfold tailWord_3479097
  simp only [CollatzResearch.WordTrace]
  refine ⟨126893092276833226307427545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84595394851222150871618363 126893092276833226307427545)
  ·
    refine ⟨95169819207624919730570659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126893092276833226307427545 95169819207624919730570659)
    ·
      refine ⟨142754728811437379595855989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95169819207624919730570659 142754728811437379595855989)
      ·
        refine ⟨13383255826072254337111499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142754728811437379595855989 13383255826072254337111499)
        ·
          refine ⟨20074883739108381505667249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383255826072254337111499 20074883739108381505667249)
          ·
            refine ⟨15056162804331286129250437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20074883739108381505667249 15056162804331286129250437)
            ·
              refine ⟨2823030525812116149234457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15056162804331286129250437 2823030525812116149234457)
              ·
                refine ⟨2117272894359087111925843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823030525812116149234457 2117272894359087111925843)
                ·
                  refine ⟨3175909341538630667888765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117272894359087111925843 3175909341538630667888765)
                  ·
                    refine ⟨1190966003076986500458287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3175909341538630667888765 1190966003076986500458287)
                    ·
                      rfl

theorem cell22_3479097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_3479097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479097 prefixEnd_3479097 := by exact prefixLift 3479097
  have htrace : WordTrace (prefixWord ++ tailWord_3479097) baseStart_3479097 baseEnd_3479097 := by
    simpa [prefixWord, tailWord_3479097, baseEnd_3479097] using wordTrace_append hprefix tailTrace_3479097
  have hstable : (prefixWord ++ tailWord_3479097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479097).length < 2 ^ (prefixWord ++ tailWord_3479097).sum := by decide
  have hdescent : baseEnd_3479097 < baseStart_3479097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479121 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 6]
def baseStart_3479121 : Nat := 118140960795 + 3479121 * 2 ^ 59
def prefixEnd_3479121 : Nat := 4983230072969 + 3 ^ 40 * 3479121 * 2
def baseEnd_3479121 : Nat := 396991406255819479286071

theorem tailTrace_3479121 : CollatzResearch.WordTrace tailWord_3479121 prefixEnd_3479121 396991406255819479286071 := by
  unfold tailWord_3479121
  simp only [CollatzResearch.WordTrace]
  refine ⟨126893967628746278406301217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84595978419164185604200811 126893967628746278406301217)
  ·
    refine ⟨95170475721559708804725913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126893967628746278406301217 95170475721559708804725913)
    ·
      refine ⟨71377856791169781603544435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95170475721559708804725913 71377856791169781603544435)
      ·
        refine ⟨107066785186754672405316653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71377856791169781603544435 107066785186754672405316653)
        ·
          refine ⟨40150044445033002151993745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107066785186754672405316653 40150044445033002151993745)
          ·
            refine ⟨30112533333774751613995309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40150044445033002151993745 30112533333774751613995309)
            ·
              refine ⟨11292200000165531855248241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30112533333774751613995309 11292200000165531855248241)
              ·
                refine ⟨8469150000124148891436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292200000165531855248241 8469150000124148891436181)
                ·
                  refine ⟨396991406255819479286071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8469150000124148891436181 396991406255819479286071)
                  ·
                    rfl

theorem cell22_3479121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_3479121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479121 prefixEnd_3479121 := by exact prefixLift 3479121
  have htrace : WordTrace (prefixWord ++ tailWord_3479121) baseStart_3479121 baseEnd_3479121 := by
    simpa [prefixWord, tailWord_3479121, baseEnd_3479121] using wordTrace_append hprefix tailTrace_3479121
  have hstable : (prefixWord ++ tailWord_3479121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479121).length < 2 ^ (prefixWord ++ tailWord_3479121).sum := by decide
  have hdescent : baseEnd_3479121 < baseStart_3479121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479140 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_3479140 : Nat := 118140960795 + 3479140 * 2 ^ 59
def prefixEnd_3479140 : Nat := 4983230072969 + 3 ^ 40 * 3479140 * 2
def baseEnd_3479140 : Nat := 1190980722855748721633155

theorem tailTrace_3479140 : CollatzResearch.WordTrace tailWord_3479140 prefixEnd_3479140 1190980722855748721633155 := by
  unfold tailWord_3479140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63447330307838722325621437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84596440410451629767495249 63447330307838722325621437)
  ·
    refine ⟨23792748865439520872108039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63447330307838722325621437 23792748865439520872108039)
    ·
      refine ⟨35689123298159281308162059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23792748865439520872108039 35689123298159281308162059)
      ·
        refine ⟨53533684947238921962243089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35689123298159281308162059 53533684947238921962243089)
        ·
          refine ⟨40150263710429191471682317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53533684947238921962243089 40150263710429191471682317)
          ·
            refine ⟨15056348891410946801880869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40150263710429191471682317 15056348891410946801880869)
            ·
              refine ⟨2823065417139552525352663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15056348891410946801880869 2823065417139552525352663)
              ·
                refine ⟨4234598125709328788028995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823065417139552525352663 4234598125709328788028995)
                ·
                  refine ⟨6351897188563993182043493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234598125709328788028995 6351897188563993182043493)
                  ·
                    refine ⟨1190980722855748721633155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351897188563993182043493 1190980722855748721633155)
                    ·
                      rfl

theorem cell22_3479140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_3479140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479140 prefixEnd_3479140 := by exact prefixLift 3479140
  have htrace : WordTrace (prefixWord ++ tailWord_3479140) baseStart_3479140 baseEnd_3479140 := by
    simpa [prefixWord, tailWord_3479140, baseEnd_3479140] using wordTrace_append hprefix tailTrace_3479140
  have hstable : (prefixWord ++ tailWord_3479140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479140).length < 2 ^ (prefixWord ++ tailWord_3479140).sum := by decide
  have hdescent : baseEnd_3479140 < baseStart_3479140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479151 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_3479151 : Nat := 118140960795 + 3479151 * 2 ^ 59
def prefixEnd_3479151 : Nat := 4983230072969 + 3 ^ 40 * 3479151 * 2
def baseEnd_3479151 : Nat := 1190984488380548359608121

theorem tailTrace_3479151 : CollatzResearch.WordTrace tailWord_3479151 prefixEnd_3479151 1190984488380548359608121 := by
  unfold tailWord_3479151
  simp only [CollatzResearch.WordTrace]
  refine ⟨126895061818637593529893307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84596707879091729019928871 126895061818637593529893307)
  ·
    refine ⟨190342592727956390294839961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126895061818637593529893307 190342592727956390294839961)
    ·
      refine ⟨142756944545967292721129971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190342592727956390294839961 142756944545967292721129971)
      ·
        refine ⟨214135416818950939081694957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142756944545967292721129971 214135416818950939081694957)
        ·
          refine ⟨80300781307106602155635609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214135416818950939081694957 80300781307106602155635609)
          ·
            refine ⟨60225585980329951616726707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80300781307106602155635609 60225585980329951616726707)
            ·
              refine ⟨90338378970494927425090061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60225585980329951616726707 90338378970494927425090061)
              ·
                refine ⟨33876892113935597784408773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90338378970494927425090061 33876892113935597784408773)
                ·
                  refine ⟨6351917271362924584576645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33876892113935597784408773 6351917271362924584576645)
                  ·
                    refine ⟨1190984488380548359608121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351917271362924584576645 1190984488380548359608121)
                    ·
                      rfl

theorem cell22_3479151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_3479151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479151 prefixEnd_3479151 := by exact prefixLift 3479151
  have htrace : WordTrace (prefixWord ++ tailWord_3479151) baseStart_3479151 baseEnd_3479151 := by
    simpa [prefixWord, tailWord_3479151, baseEnd_3479151] using wordTrace_append hprefix tailTrace_3479151
  have hstable : (prefixWord ++ tailWord_3479151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479151).length < 2 ^ (prefixWord ++ tailWord_3479151).sum := by decide
  have hdescent : baseEnd_3479151 < baseStart_3479151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479202 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3479202 : Nat := 118140960795 + 3479202 * 2 ^ 59
def prefixEnd_3479202 : Nat := 4983230072969 + 3 ^ 40 * 3479202 * 2
def baseEnd_3479202 : Nat := 1191001946722801226582965

theorem tailTrace_3479202 : CollatzResearch.WordTrace tailWord_3479202 prefixEnd_3479202 1191001946722801226582965 := by
  unfold tailWord_3479202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31724230485363207309999965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84597947960968552826666573 31724230485363207309999965)
  ·
    refine ⟨11896586432011202741249987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31724230485363207309999965 11896586432011202741249987)
    ·
      refine ⟨17844879648016804111874981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896586432011202741249987 17844879648016804111874981)
      ·
        refine ⟨3345914934003150770976559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17844879648016804111874981 3345914934003150770976559)
        ·
          refine ⟨5018872401004726156464839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345914934003150770976559 5018872401004726156464839)
          ·
            refine ⟨7528308601507089234697259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018872401004726156464839 7528308601507089234697259)
            ·
              refine ⟨11292462902260633852045889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528308601507089234697259 11292462902260633852045889)
              ·
                refine ⟨8469347176695475389034417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292462902260633852045889 8469347176695475389034417)
                ·
                  refine ⟨6352010382521606541775813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469347176695475389034417 6352010382521606541775813)
                  ·
                    refine ⟨1191001946722801226582965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352010382521606541775813 1191001946722801226582965)
                    ·
                      rfl

theorem cell22_3479202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3479202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479202 prefixEnd_3479202 := by exact prefixLift 3479202
  have htrace : WordTrace (prefixWord ++ tailWord_3479202) baseStart_3479202 baseEnd_3479202 := by
    simpa [prefixWord, tailWord_3479202, baseEnd_3479202] using wordTrace_append hprefix tailTrace_3479202
  have hstable : (prefixWord ++ tailWord_3479202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479202).length < 2 ^ (prefixWord ++ tailWord_3479202).sum := by decide
  have hdescent : baseEnd_3479202 < baseStart_3479202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479213 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3479213 : Nat := 118140960795 + 3479213 * 2 ^ 59
def prefixEnd_3479213 : Nat := 4983230072969 + 3 ^ 40 * 3479213 * 2
def baseEnd_3479213 : Nat := 1191005712247600864557931

theorem tailTrace_3479213 : CollatzResearch.WordTrace tailWord_3479213 prefixEnd_3479213 1191005712247600864557931 := by
  unfold tailWord_3479213
  simp only [CollatzResearch.WordTrace]
  refine ⟨126897323144412978118650293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84598215429608652079100195 126897323144412978118650293)
  ·
    refine ⟨11896624044788716698623465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126897323144412978118650293 11896624044788716698623465)
    ·
      refine ⟨8922468033591537523967599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11896624044788716698623465 8922468033591537523967599)
      ·
        refine ⟨13383702050387306285951399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922468033591537523967599 13383702050387306285951399)
        ·
          refine ⟨20075553075580959428927099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383702050387306285951399 20075553075580959428927099)
          ·
            refine ⟨30113329613371439143390649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075553075580959428927099 30113329613371439143390649)
            ·
              refine ⟨22584997210028579357542987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30113329613371439143390649 22584997210028579357542987)
              ·
                refine ⟨33877495815042869036314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22584997210028579357542987 33877495815042869036314481)
                ·
                  refine ⟨25408121861282151777235861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33877495815042869036314481 25408121861282151777235861)
                  ·
                    refine ⟨1191005712247600864557931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25408121861282151777235861 1191005712247600864557931)
                    ·
                      rfl

theorem cell22_3479213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3479213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479213 prefixEnd_3479213 := by exact prefixLift 3479213
  have htrace : WordTrace (prefixWord ++ tailWord_3479213) baseStart_3479213 baseEnd_3479213 := by
    simpa [prefixWord, tailWord_3479213, baseEnd_3479213] using wordTrace_append hprefix tailTrace_3479213
  have hstable : (prefixWord ++ tailWord_3479213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479213).length < 2 ^ (prefixWord ++ tailWord_3479213).sum := by decide
  have hdescent : baseEnd_3479213 < baseStart_3479213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479221 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3479221 : Nat := 118140960795 + 3479221 * 2 ^ 59
def prefixEnd_3479221 : Nat := 4983230072969 + 3 ^ 40 * 3479221 * 2
def baseEnd_3479221 : Nat := 1191008450811091510357907

theorem tailTrace_3479221 : CollatzResearch.WordTrace tailWord_3479221 prefixEnd_3479221 1191008450811091510357907 := by
  unfold tailWord_3479221
  simp only [CollatzResearch.WordTrace]
  refine ⟨126897614928383995484941517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84598409952255996989961011 126897614928383995484941517)
  ·
    refine ⟨47586605598143998306853069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126897614928383995484941517 47586605598143998306853069)
    ·
      refine ⟨17844977099303999365069901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47586605598143998306853069 17844977099303999365069901)
      ·
        refine ⟨6691866412238999761901213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17844977099303999365069901 6691866412238999761901213)
        ·
          refine ⟨2509449904589624910712955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6691866412238999761901213 2509449904589624910712955)
          ·
            refine ⟨3764174856884437366069433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509449904589624910712955 3764174856884437366069433)
            ·
              refine ⟨2823131142663328024552075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764174856884437366069433 2823131142663328024552075)
              ·
                refine ⟨4234696713994992036828113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823131142663328024552075 4234696713994992036828113)
                ·
                  refine ⟨3176022535496244027621085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234696713994992036828113 3176022535496244027621085)
                  ·
                    refine ⟨1191008450811091510357907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176022535496244027621085 1191008450811091510357907)
                    ·
                      rfl

theorem cell22_3479221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3479221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479221 prefixEnd_3479221 := by exact prefixLift 3479221
  have htrace : WordTrace (prefixWord ++ tailWord_3479221) baseStart_3479221 baseEnd_3479221 := by
    simpa [prefixWord, tailWord_3479221, baseEnd_3479221] using wordTrace_append hprefix tailTrace_3479221
  have hstable : (prefixWord ++ tailWord_3479221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479221).length < 2 ^ (prefixWord ++ tailWord_3479221).sum := by decide
  have hdescent : baseEnd_3479221 < baseStart_3479221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479322 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_3479322 : Nat := 118140960795 + 3479322 * 2 ^ 59
def prefixEnd_3479322 : Nat := 4983230072969 + 3 ^ 40 * 3479322 * 2
def baseEnd_3479322 : Nat := 1191043025175160913582597

theorem tailTrace_3479322 : CollatzResearch.WordTrace tailWord_3479322 prefixEnd_3479322 1191043025175160913582597 := by
  unfold tailWord_3479322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725324675254522433592055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84600865800678726489578813 31725324675254522433592055)
  ·
    refine ⟨47587987012881783650388083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31725324675254522433592055 47587987012881783650388083)
    ·
      refine ⟨71381980519322675475582125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47587987012881783650388083 71381980519322675475582125)
      ·
        refine ⟨26768242694746003303343297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71381980519322675475582125 26768242694746003303343297)
        ·
          refine ⟨20076182021059502477507473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26768242694746003303343297 20076182021059502477507473)
          ·
            refine ⟨15057136515794626858130605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20076182021059502477507473 15057136515794626858130605)
            ·
              refine ⟨5646426193422985071798977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15057136515794626858130605 5646426193422985071798977)
              ·
                refine ⟨4234819645067238803849233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646426193422985071798977 4234819645067238803849233)
                ·
                  refine ⟨3176114733800429102886925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4234819645067238803849233 3176114733800429102886925)
                  ·
                    refine ⟨1191043025175160913582597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176114733800429102886925 1191043025175160913582597)
                    ·
                      rfl

theorem cell22_3479322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_3479322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479322 prefixEnd_3479322 := by exact prefixLift 3479322
  have htrace : WordTrace (prefixWord ++ tailWord_3479322) baseStart_3479322 baseEnd_3479322 := by
    simpa [prefixWord, tailWord_3479322, baseEnd_3479322] using wordTrace_append hprefix tailTrace_3479322
  have hstable : (prefixWord ++ tailWord_3479322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479322).length < 2 ^ (prefixWord ++ tailWord_3479322).sum := by decide
  have hdescent : baseEnd_3479322 < baseStart_3479322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479363 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 7]
def baseStart_3479363 : Nat := 118140960795 + 3479363 * 2 ^ 59
def prefixEnd_3479363 : Nat := 4983230072969 + 3 ^ 40 * 3479363 * 2
def baseEnd_3479363 : Nat := 397019020104350157769157

theorem tailTrace_3479363 : CollatzResearch.WordTrace tailWord_3479363 prefixEnd_3479363 397019020104350157769157 := by
  unfold tailWord_3479363
  simp only [CollatzResearch.WordTrace]
  refine ⟨126902794093869553736610743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84601862729246369157740495 126902794093869553736610743)
  ·
    refine ⟨190354191140804330604916115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126902794093869553736610743 190354191140804330604916115)
    ·
      refine ⟨285531286711206495907374173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190354191140804330604916115 285531286711206495907374173)
      ·
        refine ⟨107074232516702435965265315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285531286711206495907374173 107074232516702435965265315)
        ·
          refine ⟨160611348775053653947897973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107074232516702435965265315 160611348775053653947897973)
          ·
            refine ⟨15057313947661280057615435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160611348775053653947897973 15057313947661280057615435)
            ·
              refine ⟨22585970921491920086423153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15057313947661280057615435 22585970921491920086423153)
              ·
                refine ⟨16939478191118940064817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22585970921491920086423153 16939478191118940064817365)
                ·
                  refine ⟨397019020104350157769157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16939478191118940064817365 397019020104350157769157)
                  ·
                    rfl

theorem cell22_3479363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_3479363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479363 prefixEnd_3479363 := by exact prefixLift 3479363
  have htrace : WordTrace (prefixWord ++ tailWord_3479363) baseStart_3479363 baseEnd_3479363 := by
    simpa [prefixWord, tailWord_3479363, baseEnd_3479363] using wordTrace_append hprefix tailTrace_3479363
  have hstable : (prefixWord ++ tailWord_3479363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479363).length < 2 ^ (prefixWord ++ tailWord_3479363).sum := by decide
  have hdescent : baseEnd_3479363 < baseStart_3479363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479380 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3479380 : Nat := 118140960795 + 3479380 * 2 ^ 59
def prefixEnd_3479380 : Nat := 4983230072969 + 3 ^ 40 * 3479380 * 2
def baseEnd_3479380 : Nat := 397020959920156031877473

theorem tailTrace_3479380 : CollatzResearch.WordTrace tailWord_3479380 prefixEnd_3479380 397020959920156031877473 := by
  unfold tailWord_3479380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63451707067403982819989797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84602276089871977093319729 63451707067403982819989797)
  ·
    refine ⟨11897195075138246778748087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63451707067403982819989797 11897195075138246778748087)
    ·
      refine ⟨17845792612707370168122131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897195075138246778748087 17845792612707370168122131)
      ·
        refine ⟨26768688919061055252183197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845792612707370168122131 26768688919061055252183197)
        ·
          refine ⟨10038258344647895719568699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26768688919061055252183197 10038258344647895719568699)
          ·
            refine ⟨15057387516971843579353049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038258344647895719568699 15057387516971843579353049)
            ·
              refine ⟨11293040637728882684514787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15057387516971843579353049 11293040637728882684514787)
              ·
                refine ⟨16939560956593324026772181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293040637728882684514787 16939560956593324026772181)
                ·
                  refine ⟨397020959920156031877473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16939560956593324026772181 397020959920156031877473)
                  ·
                    rfl

theorem cell22_3479380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3479380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479380 prefixEnd_3479380 := by exact prefixLift 3479380
  have htrace : WordTrace (prefixWord ++ tailWord_3479380) baseStart_3479380 baseEnd_3479380 := by
    simpa [prefixWord, tailWord_3479380, baseEnd_3479380] using wordTrace_append hprefix tailTrace_3479380
  have hstable : (prefixWord ++ tailWord_3479380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479380).length < 2 ^ (prefixWord ++ tailWord_3479380).sum := by decide
  have hdescent : baseEnd_3479380 < baseStart_3479380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479408 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 8]
def baseStart_3479408 : Nat := 118140960795 + 3479408 * 2 ^ 59
def prefixEnd_3479408 : Nat := 4983230072969 + 3 ^ 40 * 3479408 * 2
def baseEnd_3479408 : Nat := 397024154910895118644111

theorem tailTrace_3479408 : CollatzResearch.WordTrace tailWord_3479408 prefixEnd_3479408 397024154910895118644111 := by
  unfold tailWord_3479408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63452217689353263210999439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84602956919137684281332585 63452217689353263210999439)
  ·
    refine ⟨95178326534029894816499159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63452217689353263210999439 95178326534029894816499159)
    ·
      refine ⟨142767489801044842224748739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95178326534029894816499159 142767489801044842224748739)
      ·
        refine ⟨214151234701567263337123109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142767489801044842224748739 214151234701567263337123109)
        ·
          refine ⟨40153356506543861875710583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214151234701567263337123109 40153356506543861875710583)
          ·
            refine ⟨60230034759815792813565875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40153356506543861875710583 60230034759815792813565875)
            ·
              refine ⟨90345052139723689220348813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60230034759815792813565875 90345052139723689220348813)
              ·
                refine ⟨33879394552396383457630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90345052139723689220348813 33879394552396383457630805)
                ·
                  refine ⟨397024154910895118644111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33879394552396383457630805 397024154910895118644111)
                  ·
                    rfl

theorem cell22_3479408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_3479408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479408 prefixEnd_3479408 := by exact prefixLift 3479408
  have htrace : WordTrace (prefixWord ++ tailWord_3479408) baseStart_3479408 baseEnd_3479408 := by
    simpa [prefixWord, tailWord_3479408, baseEnd_3479408] using wordTrace_append hprefix tailTrace_3479408
  have hstable : (prefixWord ++ tailWord_3479408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479408).length < 2 ^ (prefixWord ++ tailWord_3479408).sum := by decide
  have hdescent : baseEnd_3479408 < baseStart_3479408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479446 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3479446 : Nat := 118140960795 + 3479446 * 2 ^ 59
def prefixEnd_3479446 : Nat := 4983230072969 + 3 ^ 40 * 3479446 * 2
def baseEnd_3479446 : Nat := 1191085472909265923482217

theorem tailTrace_3479446 : CollatzResearch.WordTrace tailWord_3479446 prefixEnd_3479446 1191085472909265923482217 := by
  unfold tailWord_3479446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931613834535553681992637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84603880901712572607921461 7931613834535553681992637)
  ·
    refine ⟨2974355187950832630747239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7931613834535553681992637 2974355187950832630747239)
    ·
      refine ⟨4461532781926248946120859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974355187950832630747239 4461532781926248946120859)
      ·
        refine ⟨6692299172889373419181289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461532781926248946120859 6692299172889373419181289)
        ·
          refine ⟨5019224379667030064385967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6692299172889373419181289 5019224379667030064385967)
          ·
            refine ⟨7528836569500545096578951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019224379667030064385967 7528836569500545096578951)
            ·
              refine ⟨11293254854250817644868427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528836569500545096578951 11293254854250817644868427)
              ·
                refine ⟨16939882281376226467302641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293254854250817644868427 16939882281376226467302641)
                ·
                  refine ⟨12704911711032169850476981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16939882281376226467302641 12704911711032169850476981)
                  ·
                    refine ⟨1191085472909265923482217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12704911711032169850476981 1191085472909265923482217)
                    ·
                      rfl

theorem cell22_3479446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3479446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479446 prefixEnd_3479446 := by exact prefixLift 3479446
  have htrace : WordTrace (prefixWord ++ tailWord_3479446) baseStart_3479446 baseEnd_3479446 := by
    simpa [prefixWord, tailWord_3479446, baseEnd_3479446] using wordTrace_append hprefix tailTrace_3479446
  have hstable : (prefixWord ++ tailWord_3479446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479446).length < 2 ^ (prefixWord ++ tailWord_3479446).sum := by decide
  have hdescent : baseEnd_3479446 < baseStart_3479446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479607 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3479607 : Nat := 118140960795 + 3479607 * 2 ^ 59
def prefixEnd_3479607 : Nat := 4983230072969 + 3 ^ 40 * 3479607 * 2
def baseEnd_3479607 : Nat := 1191140586499515170206723

theorem tailTrace_3479607 : CollatzResearch.WordTrace tailWord_3479607 prefixEnd_3479607 1191140586499515170206723 := by
  unfold tailWord_3479607
  simp only [CollatzResearch.WordTrace]
  refine ⟨126911693504985583408493075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84607795669990388938995383 126911693504985583408493075)
  ·
    refine ⟨190367540257478375112739613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126911693504985583408493075 190367540257478375112739613)
    ·
      refine ⟨71387827596554390667277355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190367540257478375112739613 71387827596554390667277355)
      ·
        refine ⟨107081741394831586000916033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71387827596554390667277355 107081741394831586000916033)
        ·
          refine ⟨80311306046123689500687025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107081741394831586000916033 80311306046123689500687025)
          ·
            refine ⟨60233479534592767125515269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80311306046123689500687025 60233479534592767125515269)
            ·
              refine ⟨11293777412736143836034113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60233479534592767125515269 11293777412736143836034113)
              ·
                refine ⟨8470333059552107877025585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11293777412736143836034113 8470333059552107877025585)
                ·
                  refine ⟨6352749794664080907769189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470333059552107877025585 6352749794664080907769189)
                  ·
                    refine ⟨1191140586499515170206723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352749794664080907769189 1191140586499515170206723)
                    ·
                      rfl

theorem cell22_3479607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3479607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479607 prefixEnd_3479607 := by exact prefixLift 3479607
  have htrace : WordTrace (prefixWord ++ tailWord_3479607) baseStart_3479607 baseEnd_3479607 := by
    simpa [prefixWord, tailWord_3479607, baseEnd_3479607] using wordTrace_append hprefix tailTrace_3479607
  have hstable : (prefixWord ++ tailWord_3479607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479607).length < 2 ^ (prefixWord ++ tailWord_3479607).sum := by decide
  have hdescent : baseEnd_3479607 < baseStart_3479607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_3479635 : Nat := 118140960795 + 3479635 * 2 ^ 59
def prefixEnd_3479635 : Nat := 4983230072969 + 3 ^ 40 * 3479635 * 2
def baseEnd_3479635 : Nat := 1191150171471732430506637

theorem tailTrace_3479635 : CollatzResearch.WordTrace tailWord_3479635 prefixEnd_3479635 1191150171471732430506637 := by
  unfold tailWord_3479635
  simp only [CollatzResearch.WordTrace]
  refine ⟨126912714748884144190512359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84608476499256096127008239 126912714748884144190512359)
  ·
    refine ⟨190369072123326216285768539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126912714748884144190512359 190369072123326216285768539)
    ·
      refine ⟨285553608184989324428652809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190369072123326216285768539 285553608184989324428652809)
      ·
        refine ⟨214165206138741993321489607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285553608184989324428652809 214165206138741993321489607)
        ·
          refine ⟨321247809208112989982234411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214165206138741993321489607 321247809208112989982234411)
          ·
            refine ⟨481871713812169484973351617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321247809208112989982234411 481871713812169484973351617)
            ·
              refine ⟨361403785359127113730013713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481871713812169484973351617 361403785359127113730013713)
              ·
                refine ⟨271052839019345335297510285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361403785359127113730013713 271052839019345335297510285)
                ·
                  refine ⟨101644814632254500736566357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271052839019345335297510285 101644814632254500736566357)
                  ·
                    refine ⟨1191150171471732430506637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101644814632254500736566357 1191150171471732430506637)
                    ·
                      rfl

theorem cell22_3479635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_3479635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479635 prefixEnd_3479635 := by exact prefixLift 3479635
  have htrace : WordTrace (prefixWord ++ tailWord_3479635) baseStart_3479635 baseEnd_3479635 := by
    simpa [prefixWord, tailWord_3479635, baseEnd_3479635] using wordTrace_append hprefix tailTrace_3479635
  have hstable : (prefixWord ++ tailWord_3479635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479635).length < 2 ^ (prefixWord ++ tailWord_3479635).sum := by decide
  have hdescent : baseEnd_3479635 < baseStart_3479635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479671 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3479671 : Nat := 118140960795 + 3479671 * 2 ^ 59
def prefixEnd_3479671 : Nat := 4983230072969 + 3 ^ 40 * 3479671 * 2
def baseEnd_3479671 : Nat := 1191162495007440336606527

theorem tailTrace_3479671 : CollatzResearch.WordTrace tailWord_3479671 prefixEnd_3479671 1191162495007440336606527 := by
  unfold tailWord_3479671
  simp only [CollatzResearch.WordTrace]
  refine ⟨126914027776753722338822867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84609351851169148225881911 126914027776753722338822867)
  ·
    refine ⟨190371041665130583508234301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126914027776753722338822867 190371041665130583508234301)
    ·
      refine ⟨71389140624423968815587863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190371041665130583508234301 71389140624423968815587863)
      ·
        refine ⟨107083710936635953223381795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71389140624423968815587863 107083710936635953223381795)
        ·
          refine ⟨160625566404953929835072693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107083710936635953223381795 160625566404953929835072693)
          ·
            refine ⟨15058646850464430922038065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160625566404953929835072693 15058646850464430922038065)
            ·
              refine ⟨11293985137848323191528549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15058646850464430922038065 11293985137848323191528549)
              ·
                refine ⟨2117622213346560598411603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11293985137848323191528549 2117622213346560598411603)
                ·
                  refine ⟨3176433320019840897617405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117622213346560598411603 3176433320019840897617405)
                  ·
                    refine ⟨1191162495007440336606527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176433320019840897617405 1191162495007440336606527)
                    ·
                      rfl

theorem cell22_3479671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3479671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479671 prefixEnd_3479671 := by exact prefixLift 3479671
  have htrace : WordTrace (prefixWord ++ tailWord_3479671) baseStart_3479671 baseEnd_3479671 := by
    simpa [prefixWord, tailWord_3479671, baseEnd_3479671] using wordTrace_append hprefix tailTrace_3479671
  have hstable : (prefixWord ++ tailWord_3479671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479671).length < 2 ^ (prefixWord ++ tailWord_3479671).sum := by decide
  have hdescent : baseEnd_3479671 < baseStart_3479671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479722 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3479722 : Nat := 118140960795 + 3479722 * 2 ^ 59
def prefixEnd_3479722 : Nat := 4983230072969 + 3 ^ 40 * 3479722 * 2
def baseEnd_3479722 : Nat := 1191179953349693203581371

theorem tailTrace_3479722 : CollatzResearch.WordTrace tailWord_3479722 prefixEnd_3479722 1191179953349693203581371 := by
  unfold tailWord_3479722
  simp only [CollatzResearch.WordTrace]
  refine ⟨31728971974892239512232355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84610591933045972032619613 31728971974892239512232355)
  ·
    refine ⟨47593457962338359268348533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31728971974892239512232355 47593457962338359268348533)
    ·
      refine ⟨4461886683969221181407675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47593457962338359268348533 4461886683969221181407675)
      ·
        refine ⟨6692830025953831772111513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461886683969221181407675 6692830025953831772111513)
        ·
          refine ⟨5019622519465373829083635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6692830025953831772111513 5019622519465373829083635)
          ·
            refine ⟨7529433779198060743625453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019622519465373829083635 7529433779198060743625453)
            ·
              refine ⟨2823537667199272778859545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7529433779198060743625453 2823537667199272778859545)
              ·
                refine ⟨2117653250399454584144659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823537667199272778859545 2117653250399454584144659)
                ·
                  refine ⟨3176479875599181876216989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2117653250399454584144659 3176479875599181876216989)
                  ·
                    refine ⟨1191179953349693203581371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3176479875599181876216989 1191179953349693203581371)
                    ·
                      rfl

theorem cell22_3479722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3479722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479722 prefixEnd_3479722 := by exact prefixLift 3479722
  have htrace : WordTrace (prefixWord ++ tailWord_3479722) baseStart_3479722 baseEnd_3479722 := by
    simpa [prefixWord, tailWord_3479722, baseEnd_3479722] using wordTrace_append hprefix tailTrace_3479722
  have hstable : (prefixWord ++ tailWord_3479722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479722).length < 2 ^ (prefixWord ++ tailWord_3479722).sum := by decide
  have hdescent : baseEnd_3479722 < baseStart_3479722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479748 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3479748 : Nat := 118140960795 + 3479748 * 2 ^ 59
def prefixEnd_3479748 : Nat := 4983230072969 + 3 ^ 40 * 3479748 * 2
def baseEnd_3479748 : Nat := 1191188853681037802431291

theorem tailTrace_3479748 : CollatzResearch.WordTrace tailWord_3479748 prefixEnd_3479748 1191188853681037802431291 := by
  unfold tailWord_3479748
  simp only [CollatzResearch.WordTrace]
  refine ⟨63458418098737382244687949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84611224131649842992917265 63458418098737382244687949)
  ·
    refine ⟨23796906787026518341757981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63458418098737382244687949 23796906787026518341757981)
    ·
      refine ⟨8923840045134944378159243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23796906787026518341757981 8923840045134944378159243)
      ·
        refine ⟨13385760067702416567238865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923840045134944378159243 13385760067702416567238865)
        ·
          refine ⟨10039320050776812425429149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13385760067702416567238865 10039320050776812425429149)
          ·
            refine ⟨3764745019041304659535931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10039320050776812425429149 3764745019041304659535931)
            ·
              refine ⟨5647117528561956989303897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764745019041304659535931 5647117528561956989303897)
              ·
                refine ⟨4235338146421467741977923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647117528561956989303897 4235338146421467741977923)
                ·
                  refine ⟨6353007219632201612966885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235338146421467741977923 6353007219632201612966885)
                  ·
                    refine ⟨1191188853681037802431291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353007219632201612966885 1191188853681037802431291)
                    ·
                      rfl

theorem cell22_3479748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3479748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479748 prefixEnd_3479748 := by exact prefixLift 3479748
  have htrace : WordTrace (prefixWord ++ tailWord_3479748) baseStart_3479748 baseEnd_3479748 := by
    simpa [prefixWord, tailWord_3479748, baseEnd_3479748] using wordTrace_append hprefix tailTrace_3479748
  have hstable : (prefixWord ++ tailWord_3479748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479748).length < 2 ^ (prefixWord ++ tailWord_3479748).sum := by decide
  have hdescent : baseEnd_3479748 < baseStart_3479748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479759 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_3479759 : Nat := 118140960795 + 3479759 * 2 ^ 59
def prefixEnd_3479759 : Nat := 4983230072969 + 3 ^ 40 * 3479759 * 2
def baseEnd_3479759 : Nat := 1191192619205837440406257

theorem tailTrace_3479759 : CollatzResearch.WordTrace tailWord_3479759 prefixEnd_3479759 1191192619205837440406257 := by
  unfold tailWord_3479759
  simp only [CollatzResearch.WordTrace]
  refine ⟨126917237400434913368026331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84611491600289942245350887 126917237400434913368026331)
  ·
    refine ⟨190375856100652370052039497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126917237400434913368026331 190375856100652370052039497)
    ·
      refine ⟨142781892075489277539029623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190375856100652370052039497 142781892075489277539029623)
      ·
        refine ⟨214172838113233916308544435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142781892075489277539029623 214172838113233916308544435)
        ·
          refine ⟨321259257169850874462816653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214172838113233916308544435 321259257169850874462816653)
          ·
            refine ⟨120472221438694077923556245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321259257169850874462816653 120472221438694077923556245)
            ·
              refine ⟨5647135379938784902666699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120472221438694077923556245 5647135379938784902666699)
              ·
                refine ⟨8470703069908177354000049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647135379938784902666699 8470703069908177354000049)
                ·
                  refine ⟨6353027302431133015500037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470703069908177354000049 6353027302431133015500037)
                  ·
                    refine ⟨1191192619205837440406257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353027302431133015500037 1191192619205837440406257)
                    ·
                      rfl

theorem cell22_3479759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_3479759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479759 prefixEnd_3479759 := by exact prefixLift 3479759
  have htrace : WordTrace (prefixWord ++ tailWord_3479759) baseStart_3479759 baseEnd_3479759 := by
    simpa [prefixWord, tailWord_3479759, baseEnd_3479759] using wordTrace_append hprefix tailTrace_3479759
  have hstable : (prefixWord ++ tailWord_3479759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479759).length < 2 ^ (prefixWord ++ tailWord_3479759).sum := by decide
  have hdescent : baseEnd_3479759 < baseStart_3479759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479787 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_3479787 : Nat := 118140960795 + 3479787 * 2 ^ 59
def prefixEnd_3479787 : Nat := 4983230072969 + 3 ^ 40 * 3479787 * 2
def baseEnd_3479787 : Nat := 1191202204178054700706171

theorem tailTrace_3479787 : CollatzResearch.WordTrace tailWord_3479787 prefixEnd_3479787 1191202204178054700706171 := by
  unfold tailWord_3479787
  simp only [CollatzResearch.WordTrace]
  refine ⟨126918258644333474150045615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84612172429555649433363743 126918258644333474150045615)
  ·
    refine ⟨190377387966500211225068423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126918258644333474150045615 190377387966500211225068423)
    ·
      refine ⟨285566081949750316837602635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190377387966500211225068423 285566081949750316837602635)
      ·
        refine ⟨428349122924625475256403953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285566081949750316837602635 428349122924625475256403953)
        ·
          refine ⟨321261842193469106442302965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428349122924625475256403953 321261842193469106442302965)
          ·
            refine ⟨30118297705637728728965903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321261842193469106442302965 30118297705637728728965903)
            ·
              refine ⟨45177446558456593093448855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30118297705637728728965903 45177446558456593093448855)
              ·
                refine ⟨67766169837684889640173283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45177446558456593093448855 67766169837684889640173283)
                ·
                  refine ⟨101649254756527334460259925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67766169837684889640173283 101649254756527334460259925)
                  ·
                    refine ⟨1191202204178054700706171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101649254756527334460259925 1191202204178054700706171)
                    ·
                      rfl

theorem cell22_3479787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_3479787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479787 prefixEnd_3479787 := by exact prefixLift 3479787
  have htrace : WordTrace (prefixWord ++ tailWord_3479787) baseStart_3479787 baseEnd_3479787 := by
    simpa [prefixWord, tailWord_3479787, baseEnd_3479787] using wordTrace_append hprefix tailTrace_3479787
  have hstable : (prefixWord ++ tailWord_3479787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479787).length < 2 ^ (prefixWord ++ tailWord_3479787).sum := by decide
  have hdescent : baseEnd_3479787 < baseStart_3479787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479864 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_3479864 : Nat := 118140960795 + 3479864 * 2 ^ 59
def prefixEnd_3479864 : Nat := 4983230072969 + 3 ^ 40 * 3479864 * 2
def baseEnd_3479864 : Nat := 397076187617217388843645

theorem tailTrace_3479864 : CollatzResearch.WordTrace tailWord_3479864 prefixEnd_3479864 397076187617217388843645 := by
  unfold tailWord_3479864
  simp only [CollatzResearch.WordTrace]
  refine ⟨63460533532527258150299323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84614044710036344200399097 63460533532527258150299323)
  ·
    refine ⟨95190800298790887225448985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63460533532527258150299323 95190800298790887225448985)
    ·
      refine ⟨71393100224093165419086739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95190800298790887225448985 71393100224093165419086739)
      ·
        refine ⟨107089650336139748128630109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71393100224093165419086739 107089650336139748128630109)
        ·
          refine ⟨40158618876052405548236291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107089650336139748128630109 40158618876052405548236291)
          ·
            refine ⟨60237928314078608322354437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40158618876052405548236291 60237928314078608322354437)
            ·
              refine ⟨11294611558889739060441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60237928314078608322354437 11294611558889739060441457)
              ·
                refine ⟨8470958669167304295331093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11294611558889739060441457 8470958669167304295331093)
                ·
                  refine ⟨397076187617217388843645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8470958669167304295331093 397076187617217388843645)
                  ·
                    rfl

theorem cell22_3479864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_3479864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479864 prefixEnd_3479864 := by exact prefixLift 3479864
  have htrace : WordTrace (prefixWord ++ tailWord_3479864) baseStart_3479864 baseEnd_3479864 := by
    simpa [prefixWord, tailWord_3479864, baseEnd_3479864] using wordTrace_append hprefix tailTrace_3479864
  have hstable : (prefixWord ++ tailWord_3479864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479864).length < 2 ^ (prefixWord ++ tailWord_3479864).sum := by decide
  have hdescent : baseEnd_3479864 < baseStart_3479864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479866 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_3479866 : Nat := 118140960795 + 3479866 * 2 ^ 59
def prefixEnd_3479866 : Nat := 4983230072969 + 3 ^ 40 * 3479866 * 2
def baseEnd_3479866 : Nat := 1191229247492524827980929

theorem tailTrace_3479866 : CollatzResearch.WordTrace tailWord_3479866 prefixEnd_3479866 1191229247492524827980929 := by
  unfold tailWord_3479866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730285002761817660542863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84614093340698180428114301 31730285002761817660542863)
  ·
    refine ⟨47595427504142726490814295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31730285002761817660542863 47595427504142726490814295)
    ·
      refine ⟨71393141256214089736221443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47595427504142726490814295 71393141256214089736221443)
      ·
        refine ⟨107089711884321134604332165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71393141256214089736221443 107089711884321134604332165)
        ·
          refine ⟨20079320978310212738312281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107089711884321134604332165 20079320978310212738312281)
          ·
            refine ⟨15059490733732659553734211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20079320978310212738312281 15059490733732659553734211)
            ·
              refine ⟨22589236100598989330601317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15059490733732659553734211 22589236100598989330601317)
              ·
                refine ⟨4235481768862310499487747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22589236100598989330601317 4235481768862310499487747)
                ·
                  refine ⟨6353222653293465749231621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235481768862310499487747 6353222653293465749231621)
                  ·
                    refine ⟨1191229247492524827980929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353222653293465749231621 1191229247492524827980929)
                    ·
                      rfl

theorem cell22_3479866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_3479866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479866 prefixEnd_3479866 := by exact prefixLift 3479866
  have htrace : WordTrace (prefixWord ++ tailWord_3479866) baseStart_3479866 baseEnd_3479866 := by
    simpa [prefixWord, tailWord_3479866, baseEnd_3479866] using wordTrace_append hprefix tailTrace_3479866
  have hstable : (prefixWord ++ tailWord_3479866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479866).length < 2 ^ (prefixWord ++ tailWord_3479866).sum := by decide
  have hdescent : baseEnd_3479866 < baseStart_3479866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479879 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3479879 : Nat := 118140960795 + 3479879 * 2 ^ 59
def prefixEnd_3479879 : Nat := 4983230072969 + 3 ^ 40 * 3479879 * 2
def baseEnd_3479879 : Nat := 1191233697658197127405889

theorem tailTrace_3479879 : CollatzResearch.WordTrace tailWord_3479879 prefixEnd_3479879 1191233697658197127405889 := by
  unfold tailWord_3479879
  simp only [CollatzResearch.WordTrace]
  refine ⟨126921614160000173862394691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84614409440000115908263127 126921614160000173862394691)
  ·
    refine ⟨190382421240000260793592037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126921614160000173862394691 190382421240000260793592037)
    ·
      refine ⟨35696703982500048898798507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190382421240000260793592037 35696703982500048898798507)
      ·
        refine ⟨53545055973750073348197761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35696703982500048898798507 53545055973750073348197761)
        ·
          refine ⟨40158791980312555011148321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53545055973750073348197761 40158791980312555011148321)
          ·
            refine ⟨30119093985234416258361241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40158791980312555011148321 30119093985234416258361241)
            ·
              refine ⟨22589320488925812193770931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30119093985234416258361241 22589320488925812193770931)
              ·
                refine ⟨33883980733388718290656397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22589320488925812193770931 33883980733388718290656397)
                ·
                  refine ⟨12706492775020769358996149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33883980733388718290656397 12706492775020769358996149)
                  ·
                    refine ⟨1191233697658197127405889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12706492775020769358996149 1191233697658197127405889)
                    ·
                      rfl

theorem cell22_3479879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3479879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479879 prefixEnd_3479879 := by exact prefixLift 3479879
  have htrace : WordTrace (prefixWord ++ tailWord_3479879) baseStart_3479879 baseEnd_3479879 := by
    simpa [prefixWord, tailWord_3479879, baseEnd_3479879] using wordTrace_append hprefix tailTrace_3479879
  have hstable : (prefixWord ++ tailWord_3479879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479879).length < 2 ^ (prefixWord ++ tailWord_3479879).sum := by decide
  have hdescent : baseEnd_3479879 < baseStart_3479879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479909 : List Nat := [1, 3, 1, 3, 1, 3, 1, 9]
def baseStart_3479909 : Nat := 118140960795 + 3479909 * 2 ^ 59
def prefixEnd_3479909 : Nat := 4983230072969 + 3 ^ 40 * 3479909 * 2
def baseEnd_3479909 : Nat := 132360440807920783239533

theorem tailTrace_3479909 : CollatzResearch.WordTrace tailWord_3479909 prefixEnd_3479909 132360440807920783239533 := by
  unfold tailWord_3479909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126922708349891488985986781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84615138899927659323991187 126922708349891488985986781)
  ·
    refine ⟨47596015631209308369745043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126922708349891488985986781 47596015631209308369745043)
    ·
      refine ⟨71394023446813962554617565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47596015631209308369745043 71394023446813962554617565)
      ·
        refine ⟨26772758792555235957981587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71394023446813962554617565 26772758792555235957981587)
        ·
          refine ⟨40159138188832853936972381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26772758792555235957981587 40159138188832853936972381)
          ·
            refine ⟨15059676820812320226364643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40159138188832853936972381 15059676820812320226364643)
            ·
              refine ⟨22589515231218480339546965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15059676820812320226364643 22589515231218480339546965)
              ·
                refine ⟨132360440807920783239533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22589515231218480339546965 132360440807920783239533)
                ·
                  rfl

theorem cell22_3479909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 9].length) (baseStart_3479909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479909 prefixEnd_3479909 := by exact prefixLift 3479909
  have htrace : WordTrace (prefixWord ++ tailWord_3479909) baseStart_3479909 baseEnd_3479909 := by
    simpa [prefixWord, tailWord_3479909, baseEnd_3479909] using wordTrace_append hprefix tailTrace_3479909
  have hstable : (prefixWord ++ tailWord_3479909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479909).length < 2 ^ (prefixWord ++ tailWord_3479909).sum := by decide
  have hdescent : baseEnd_3479909 < baseStart_3479909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3479971 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 5]
def baseStart_3479971 : Nat := 118140960795 + 3479971 * 2 ^ 59
def prefixEnd_3479971 : Nat := 4983230072969 + 3 ^ 40 * 3479971 * 2
def baseEnd_3479971 : Nat := 397088397046113184701869

theorem tailTrace_3479971 : CollatzResearch.WordTrace tailWord_3479971 prefixEnd_3479971 397088397046113184701869 := by
  unfold tailWord_3479971
  simp only [CollatzResearch.WordTrace]
  refine ⟨126924969675666873574743767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84616646450444582383162511 126924969675666873574743767)
  ·
    refine ⟨190387454513500310362115651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126924969675666873574743767 190387454513500310362115651)
    ·
      refine ⟨285581181770250465543173477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190387454513500310362115651 285581181770250465543173477)
      ·
        refine ⟨53546471581921962289345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285581181770250465543173477 53546471581921962289345027)
        ·
          refine ⟨80319707372882943434017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53546471581921962289345027 80319707372882943434017541)
          ·
            refine ⟨15059945132415551893878289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80319707372882943434017541 15059945132415551893878289)
            ·
              refine ⟨11294958849311663920408717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15059945132415551893878289 11294958849311663920408717)
              ·
                refine ⟨4235609568491873970153269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11294958849311663920408717 4235609568491873970153269)
                ·
                  refine ⟨397088397046113184701869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4235609568491873970153269 397088397046113184701869)
                  ·
                    rfl

theorem cell22_3479971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 5].length) (baseStart_3479971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3479971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3479971 prefixEnd_3479971 := by exact prefixLift 3479971
  have htrace : WordTrace (prefixWord ++ tailWord_3479971) baseStart_3479971 baseEnd_3479971 := by
    simpa [prefixWord, tailWord_3479971, baseEnd_3479971] using wordTrace_append hprefix tailTrace_3479971
  have hstable : (prefixWord ++ tailWord_3479971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3479971).length < 2 ^ (prefixWord ++ tailWord_3479971).sum := by decide
  have hdescent : baseEnd_3479971 < baseStart_3479971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3479971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480035 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 1, 4]
def baseStart_3480035 : Nat := 118140960795 + 3480035 * 2 ^ 59
def prefixEnd_3480035 : Nat := 4983230072969 + 3 ^ 40 * 3480035 * 2
def baseEnd_3480035 : Nat := 1191287099646264720505411

theorem tailTrace_3480035 : CollatzResearch.WordTrace tailWord_3480035 prefixEnd_3480035 1191287099646264720505411 := by
  unfold tailWord_3480035
  simp only [CollatzResearch.WordTrace]
  refine ⟨126927303947435012505073559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84618202631623341670049039 126927303947435012505073559)
  ·
    refine ⟨190390955921152518757610339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126927303947435012505073559 190390955921152518757610339)
    ·
      refine ⟨285586433881728778136415509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190390955921152518757610339 285586433881728778136415509)
      ·
        refine ⟨13386864088206036475144477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285586433881728778136415509 13386864088206036475144477)
        ·
          refine ⟨5020074033077263678179179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13386864088206036475144477 5020074033077263678179179)
          ·
            refine ⟨7530111049615895517268769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020074033077263678179179 7530111049615895517268769)
            ·
              refine ⟨5647583287211921637951577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530111049615895517268769 5647583287211921637951577)
              ·
                refine ⟨4235687465408941228463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647583287211921637951577 4235687465408941228463683)
                ·
                  refine ⟨6353531198113411842695525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235687465408941228463683 6353531198113411842695525)
                  ·
                    refine ⟨1191287099646264720505411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353531198113411842695525 1191287099646264720505411)
                    ·
                      rfl

theorem cell22_3480035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 4].length) (baseStart_3480035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480035 prefixEnd_3480035 := by exact prefixLift 3480035
  have htrace : WordTrace (prefixWord ++ tailWord_3480035) baseStart_3480035 baseEnd_3480035 := by
    simpa [prefixWord, tailWord_3480035, baseEnd_3480035] using wordTrace_append hprefix tailTrace_3480035
  have hstable : (prefixWord ++ tailWord_3480035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480035).length < 2 ^ (prefixWord ++ tailWord_3480035).sum := by decide
  have hdescent : baseEnd_3480035 < baseStart_3480035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480078 : List Nat := [4, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3480078 : Nat := 118140960795 + 3480078 * 2 ^ 59
def prefixEnd_3480078 : Nat := 4983230072969 + 3 ^ 40 * 3480078 * 2
def baseEnd_3480078 : Nat := 132366868825002993520031

theorem tailTrace_3480078 : CollatzResearch.WordTrace tailWord_3480078 prefixEnd_3480078 132366868825002993520031 := by
  unfold tailWord_3480078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866109035784903856111111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84619248190852820565925925 15866109035784903856111111)
  ·
    refine ⟨23799163553677355784166667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15866109035784903856111111 23799163553677355784166667)
    ·
      refine ⟨35698745330516033676250001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23799163553677355784166667 35698745330516033676250001)
      ·
        refine ⟨26774058997887025257187501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35698745330516033676250001 26774058997887025257187501)
        ·
          refine ⟨10040272124207634471445313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26774058997887025257187501 10040272124207634471445313)
          ·
            refine ⟨7530204093155725853583985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10040272124207634471445313 7530204093155725853583985)
            ·
              refine ⟨5647653069866794390187989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530204093155725853583985 5647653069866794390187989)
              ·
                refine ⟨132366868825002993520031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5647653069866794390187989 132366868825002993520031)
                ·
                  rfl

theorem cell22_3480078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3480078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480078 prefixEnd_3480078 := by exact prefixLift 3480078
  have htrace : WordTrace (prefixWord ++ tailWord_3480078) baseStart_3480078 baseEnd_3480078 := by
    simpa [prefixWord, tailWord_3480078, baseEnd_3480078] using wordTrace_append hprefix tailTrace_3480078
  have hstable : (prefixWord ++ tailWord_3480078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480078).length < 2 ^ (prefixWord ++ tailWord_3480078).sum := by decide
  have hdescent : baseEnd_3480078 < baseStart_3480078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480138 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3480138 : Nat := 118140960795 + 3480138 * 2 ^ 59
def prefixEnd_3480138 : Nat := 4983230072969 + 3 ^ 40 * 3480138 * 2
def baseEnd_3480138 : Nat := 1191322358651206785180095

theorem tailTrace_3480138 : CollatzResearch.WordTrace tailWord_3480138 prefixEnd_3480138 1191322358651206785180095 := by
  unfold tailWord_3480138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732765166515465274018267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84620707110707907397382045 31732765166515465274018267)
  ·
    refine ⟨47599147749773197911027401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31732765166515465274018267 47599147749773197911027401)
    ·
      refine ⟨35699360812329898433270551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47599147749773197911027401 35699360812329898433270551)
      ·
        refine ⟨53549041218494847649905827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35699360812329898433270551 53549041218494847649905827)
        ·
          refine ⟨80323561827742271474858741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53549041218494847649905827 80323561827742271474858741)
          ·
            refine ⟨7530333921350837950768007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80323561827742271474858741 7530333921350837950768007)
            ·
              refine ⟨11295500882026256926152011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530333921350837950768007 11295500882026256926152011)
              ·
                refine ⟨16943251323039385389228017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11295500882026256926152011 16943251323039385389228017)
                ·
                  refine ⟨12707438492279539041921013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16943251323039385389228017 12707438492279539041921013)
                  ·
                    refine ⟨1191322358651206785180095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12707438492279539041921013 1191322358651206785180095)
                    ·
                      rfl

theorem cell22_3480138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3480138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480138 prefixEnd_3480138 := by exact prefixLift 3480138
  have htrace : WordTrace (prefixWord ++ tailWord_3480138) baseStart_3480138 baseEnd_3480138 := by
    simpa [prefixWord, tailWord_3480138, baseEnd_3480138] using wordTrace_append hprefix tailTrace_3480138
  have hstable : (prefixWord ++ tailWord_3480138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480138).length < 2 ^ (prefixWord ++ tailWord_3480138).sum := by decide
  have hdescent : baseEnd_3480138 < baseStart_3480138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480170 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3480170 : Nat := 118140960795 + 3480170 * 2 ^ 59
def prefixEnd_3480170 : Nat := 4983230072969 + 3 ^ 40 * 3480170 * 2
def baseEnd_3480170 : Nat := 1191333312905169368379997

theorem tailTrace_3480170 : CollatzResearch.WordTrace tailWord_3480170 prefixEnd_3480170 1191333312905169368379997 := by
  unfold tailWord_3480170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31733056950486482640309491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84621485201297287040825309 31733056950486482640309491)
  ·
    refine ⟨47599585425729723960464237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31733056950486482640309491 47599585425729723960464237)
    ·
      refine ⟨17849844534648646485174089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47599585425729723960464237 17849844534648646485174089)
      ·
        refine ⟨13387383400986484863880567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17849844534648646485174089 13387383400986484863880567)
        ·
          refine ⟨20081075101479727295820851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13387383400986484863880567 20081075101479727295820851)
          ·
            refine ⟨30121612652219590943731277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20081075101479727295820851 30121612652219590943731277)
            ·
              refine ⟨11295604744582346603899229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30121612652219590943731277 11295604744582346603899229)
              ·
                refine ⟨4235851779218379976462211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11295604744582346603899229 4235851779218379976462211)
                ·
                  refine ⟨6353777668827569964693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235851779218379976462211 6353777668827569964693317)
                  ·
                    refine ⟨1191333312905169368379997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353777668827569964693317 1191333312905169368379997)
                    ·
                      rfl

theorem cell22_3480170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3480170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480170 prefixEnd_3480170 := by exact prefixLift 3480170
  have htrace : WordTrace (prefixWord ++ tailWord_3480170) baseStart_3480170 baseEnd_3480170 := by
    simpa [prefixWord, tailWord_3480170, baseEnd_3480170] using wordTrace_append hprefix tailTrace_3480170
  have hstable : (prefixWord ++ tailWord_3480170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480170).length < 2 ^ (prefixWord ++ tailWord_3480170).sum := by decide
  have hdescent : baseEnd_3480170 < baseStart_3480170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480185 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 4]
def baseStart_3480185 : Nat := 118140960795 + 3480185 * 2 ^ 59
def prefixEnd_3480185 : Nat := 4983230072969 + 3 ^ 40 * 3480185 * 2
def baseEnd_3480185 : Nat := 397112815903904776418317

theorem tailTrace_3480185 : CollatzResearch.WordTrace tailWord_3480185 prefixEnd_3480185 397112815903904776418317 := by
  unfold tailWord_3480185
  simp only [CollatzResearch.WordTrace]
  refine ⟨126932774896891588123034009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84621849931261058748689339 126932774896891588123034009)
  ·
    refine ⟨95199581172668691092275507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126932774896891588123034009 95199581172668691092275507)
    ·
      refine ⟨142799371759003036638413261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95199581172668691092275507 142799371759003036638413261)
      ·
        refine ⟨53549764409626138739404973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142799371759003036638413261 53549764409626138739404973)
        ·
          refine ⟨20081161653609802027276865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53549764409626138739404973 20081161653609802027276865)
          ·
            refine ⟨15060871240207351520457649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20081161653609802027276865 15060871240207351520457649)
            ·
              refine ⟨11295653430155513640343237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15060871240207351520457649 11295653430155513640343237)
              ·
                refine ⟨2117935018154158807564357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11295653430155513640343237 2117935018154158807564357)
                ·
                  refine ⟨397112815903904776418317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117935018154158807564357 397112815903904776418317)
                  ·
                    rfl

theorem cell22_3480185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_3480185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480185 prefixEnd_3480185 := by exact prefixLift 3480185
  have htrace : WordTrace (prefixWord ++ tailWord_3480185) baseStart_3480185 baseEnd_3480185 := by
    simpa [prefixWord, tailWord_3480185, baseEnd_3480185] using wordTrace_append hprefix tailTrace_3480185
  have hstable : (prefixWord ++ tailWord_3480185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480185).length < 2 ^ (prefixWord ++ tailWord_3480185).sum := by decide
  have hdescent : baseEnd_3480185 < baseStart_3480185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480322 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3480322 : Nat := 118140960795 + 3480322 * 2 ^ 59
def prefixEnd_3480322 : Nat := 4983230072969 + 3 ^ 40 * 3480322 * 2
def baseEnd_3480322 : Nat := 1191385345611491638579531

theorem tailTrace_3480322 : CollatzResearch.WordTrace tailWord_3480322 prefixEnd_3480322 1191385345611491638579531 := by
  unfold tailWord_3480322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31734442924348815130192805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84625181131596840347180813 31734442924348815130192805)
  ·
    refine ⟨5950208048315402836911151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31734442924348815130192805 5950208048315402836911151)
    ·
      refine ⟨8925312072473104255366727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950208048315402836911151 8925312072473104255366727)
      ·
        refine ⟨13387968108709656383050091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925312072473104255366727 13387968108709656383050091)
        ·
          refine ⟨20081952163064484574575137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13387968108709656383050091 20081952163064484574575137)
          ·
            refine ⟨15061464122298363430931353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20081952163064484574575137 15061464122298363430931353)
            ·
              refine ⟨11296098091723772573198515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15061464122298363430931353 11296098091723772573198515)
              ·
                refine ⟨16944147137585658859797773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296098091723772573198515 16944147137585658859797773)
                ·
                  refine ⟨6354055176594622072424165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16944147137585658859797773 6354055176594622072424165)
                  ·
                    refine ⟨1191385345611491638579531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354055176594622072424165 1191385345611491638579531)
                    ·
                      rfl

theorem cell22_3480322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3480322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480322 prefixEnd_3480322 := by exact prefixLift 3480322
  have htrace : WordTrace (prefixWord ++ tailWord_3480322) baseStart_3480322 baseEnd_3480322 := by
    simpa [prefixWord, tailWord_3480322, baseEnd_3480322] using wordTrace_append hprefix tailTrace_3480322
  have hstable : (prefixWord ++ tailWord_3480322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480322).length < 2 ^ (prefixWord ++ tailWord_3480322).sum := by decide
  have hdescent : baseEnd_3480322 < baseStart_3480322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480335 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 4, 3]
def baseStart_3480335 : Nat := 118140960795 + 3480335 * 2 ^ 59
def prefixEnd_3480335 : Nat := 4983230072969 + 3 ^ 40 * 3480335 * 2
def baseEnd_3480335 : Nat := 1191389795777163938004491

theorem tailTrace_3480335 : CollatzResearch.WordTrace tailWord_3480335 prefixEnd_3480335 1191389795777163938004491 := by
  unfold tailWord_3480335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126938245846348163740994459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84625497230898775827329639 126938245846348163740994459)
  ·
    refine ⟨190407368769522245611491689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126938245846348163740994459 190407368769522245611491689)
    ·
      refine ⟨142805526577141684208618767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190407368769522245611491689 142805526577141684208618767)
      ·
        refine ⟨214208289865712526312928151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142805526577141684208618767 214208289865712526312928151)
        ·
          refine ⟨321312434798568789469392227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214208289865712526312928151 321312434798568789469392227)
          ·
            refine ⟨481968652197853184204088341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321312434798568789469392227 481968652197853184204088341)
            ·
              refine ⟨22592280571774368009566641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 481968652197853184204088341 22592280571774368009566641)
              ·
                refine ⟨16944210428830776007174981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22592280571774368009566641 16944210428830776007174981)
                ·
                  refine ⟨3177039455405770501345309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16944210428830776007174981 3177039455405770501345309)
                  ·
                    refine ⟨1191389795777163938004491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177039455405770501345309 1191389795777163938004491)
                    ·
                      rfl

theorem cell22_3480335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_3480335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480335 prefixEnd_3480335 := by exact prefixLift 3480335
  have htrace : WordTrace (prefixWord ++ tailWord_3480335) baseStart_3480335 baseEnd_3480335 := by
    simpa [prefixWord, tailWord_3480335, baseEnd_3480335] using wordTrace_append hprefix tailTrace_3480335
  have hstable : (prefixWord ++ tailWord_3480335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480335).length < 2 ^ (prefixWord ++ tailWord_3480335).sum := by decide
  have hdescent : baseEnd_3480335 < baseStart_3480335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480352 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_3480352 : Nat := 118140960795 + 3480352 * 2 ^ 59
def prefixEnd_3480352 : Nat := 4983230072969 + 3 ^ 40 * 3480352 * 2
def baseEnd_3480352 : Nat := 1191395615224581560329439

theorem tailTrace_3480352 : CollatzResearch.WordTrace tailWord_3480352 prefixEnd_3480352 1191395615224581560329439 := by
  unfold tailWord_3480352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63469432943643287822181655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84625910591524383762908873 63469432943643287822181655)
  ·
    refine ⟨95204149415464931733272483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63469432943643287822181655 95204149415464931733272483)
    ·
      refine ⟨142806224123197397599908725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95204149415464931733272483 142806224123197397599908725)
      ·
        refine ⟨13388083511549756024991443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142806224123197397599908725 13388083511549756024991443)
        ·
          refine ⟨20082125267324634037487165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388083511549756024991443 20082125267324634037487165)
          ·
            refine ⟨7530796975246737764057687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20082125267324634037487165 7530796975246737764057687)
            ·
              refine ⟨11296195462870106646086531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530796975246737764057687 11296195462870106646086531)
              ·
                refine ⟨16944293194305159969129797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296195462870106646086531 16944293194305159969129797)
                ·
                  refine ⟨3177054973932217494211837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16944293194305159969129797 3177054973932217494211837)
                  ·
                    refine ⟨1191395615224581560329439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177054973932217494211837 1191395615224581560329439)
                    ·
                      rfl

theorem cell22_3480352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_3480352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480352 prefixEnd_3480352 := by exact prefixLift 3480352
  have htrace : WordTrace (prefixWord ++ tailWord_3480352) baseStart_3480352 baseEnd_3480352 := by
    simpa [prefixWord, tailWord_3480352, baseEnd_3480352] using wordTrace_append hprefix tailTrace_3480352
  have hstable : (prefixWord ++ tailWord_3480352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480352).length < 2 ^ (prefixWord ++ tailWord_3480352).sum := by decide
  have hdescent : baseEnd_3480352 < baseStart_3480352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480363 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_3480363 : Nat := 118140960795 + 3480363 * 2 ^ 59
def prefixEnd_3480363 : Nat := 4983230072969 + 3 ^ 40 * 3480363 * 2
def baseEnd_3480363 : Nat := 1191399380749381198304405

theorem tailTrace_3480363 : CollatzResearch.WordTrace tailWord_3480363 prefixEnd_3480363 1191399380749381198304405 := by
  unfold tailWord_3480363
  simp only [CollatzResearch.WordTrace]
  refine ⟨126939267090246724523013743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84626178060164483015342495 126939267090246724523013743)
  ·
    refine ⟨190408900635370086784520615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126939267090246724523013743 190408900635370086784520615)
    ·
      refine ⟨285613350953055130176780923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190408900635370086784520615 285613350953055130176780923)
      ·
        refine ⟨428420026429582695265171385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285613350953055130176780923 428420026429582695265171385)
        ·
          refine ⟨321315019822187021448878539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428420026429582695265171385 321315019822187021448878539)
          ·
            refine ⟨481972529733280532173317809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321315019822187021448878539 481972529733280532173317809)
            ·
              refine ⟨361479397299960399129988357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481972529733280532173317809 361479397299960399129988357)
              ·
                refine ⟨67777386993742574836872817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361479397299960399129988357 67777386993742574836872817)
                ·
                  refine ⟨50833040245306931127654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67777386993742574836872817 50833040245306931127654613)
                  ·
                    refine ⟨1191399380749381198304405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50833040245306931127654613 1191399380749381198304405)
                    ·
                      rfl

theorem cell22_3480363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_3480363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480363 prefixEnd_3480363 := by exact prefixLift 3480363
  have htrace : WordTrace (prefixWord ++ tailWord_3480363) baseStart_3480363 baseEnd_3480363 := by
    simpa [prefixWord, tailWord_3480363, baseEnd_3480363] using wordTrace_append hprefix tailTrace_3480363
  have hstable : (prefixWord ++ tailWord_3480363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480363).length < 2 ^ (prefixWord ++ tailWord_3480363).sum := by decide
  have hdescent : baseEnd_3480363 < baseStart_3480363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480369 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3480369 : Nat := 118140960795 + 3480369 * 2 ^ 59
def prefixEnd_3480369 : Nat := 4983230072969 + 3 ^ 40 * 3480369 * 2
def baseEnd_3480369 : Nat := 1191401434671999182654387

theorem tailTrace_3480369 : CollatzResearch.WordTrace tailWord_3480369 prefixEnd_3480369 1191401434671999182654387 := by
  unfold tailWord_3480369
  simp only [CollatzResearch.WordTrace]
  refine ⟨126939485928224987547732161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84626323952149991698488107 126939485928224987547732161)
  ·
    refine ⟨95204614446168740660799121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126939485928224987547732161 95204614446168740660799121)
    ·
      refine ⟨71403460834626555495599341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95204614446168740660799121 71403460834626555495599341)
      ·
        refine ⟨26776297812984958310849753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71403460834626555495599341 26776297812984958310849753)
        ·
          refine ⟨20082223359738718733137315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26776297812984958310849753 20082223359738718733137315)
          ·
            refine ⟨30123335039608078099705973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082223359738718733137315 30123335039608078099705973)
            ·
              refine ⟨2824062659963257321847435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30123335039608078099705973 2824062659963257321847435)
              ·
                refine ⟨4236093989944885982771153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824062659963257321847435 4236093989944885982771153)
                ·
                  refine ⟨3177070492458664487078365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236093989944885982771153 3177070492458664487078365)
                  ·
                    refine ⟨1191401434671999182654387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177070492458664487078365 1191401434671999182654387)
                    ·
                      rfl

theorem cell22_3480369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3480369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480369 prefixEnd_3480369 := by exact prefixLift 3480369
  have htrace : WordTrace (prefixWord ++ tailWord_3480369) baseStart_3480369 baseEnd_3480369 := by
    simpa [prefixWord, tailWord_3480369, baseEnd_3480369] using wordTrace_append hprefix tailTrace_3480369
  have hstable : (prefixWord ++ tailWord_3480369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480369).length < 2 ^ (prefixWord ++ tailWord_3480369).sum := by decide
  have hdescent : baseEnd_3480369 < baseStart_3480369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480382 : List Nat := [4, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3480382 : Nat := 118140960795 + 3480382 * 2 ^ 59
def prefixEnd_3480382 : Nat := 4983230072969 + 3 ^ 40 * 3480382 * 2
def baseEnd_3480382 : Nat := 132378431648630164675483

theorem tailTrace_3480382 : CollatzResearch.WordTrace tailWord_3480382 prefixEnd_3480382 132378431648630164675483 := by
  unfold tailWord_3480382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867495009647236345994425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84626640051451927178636933 15867495009647236345994425)
  ·
    refine ⟨11900621257235427259495819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15867495009647236345994425 11900621257235427259495819)
    ·
      refine ⟨17850931885853140889243729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11900621257235427259495819 17850931885853140889243729)
      ·
        refine ⟨13388198914389855666932797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17850931885853140889243729 13388198914389855666932797)
        ·
          refine ⟨5020574592896195875099799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13388198914389855666932797 5020574592896195875099799)
          ·
            refine ⟨7530861889344293812649699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020574592896195875099799 7530861889344293812649699)
            ·
              refine ⟨11296292834016440718974549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530861889344293812649699 11296292834016440718974549)
              ·
                refine ⟨132378431648630164675483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11296292834016440718974549 132378431648630164675483)
                ·
                  rfl

theorem cell22_3480382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3480382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480382 prefixEnd_3480382 := by exact prefixLift 3480382
  have htrace : WordTrace (prefixWord ++ tailWord_3480382) baseStart_3480382 baseEnd_3480382 := by
    simpa [prefixWord, tailWord_3480382, baseEnd_3480382] using wordTrace_append hprefix tailTrace_3480382
  have hstable : (prefixWord ++ tailWord_3480382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480382).length < 2 ^ (prefixWord ++ tailWord_3480382).sum := by decide
  have hdescent : baseEnd_3480382 < baseStart_3480382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480388 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3480388 : Nat := 118140960795 + 3480388 * 2 ^ 59
def prefixEnd_3480388 : Nat := 4983230072969 + 3 ^ 40 * 3480388 * 2
def baseEnd_3480388 : Nat := 397135979586763155476443

theorem tailTrace_3480388 : CollatzResearch.WordTrace tailWord_3480388 prefixEnd_3480388 397135979586763155476443 := by
  unfold tailWord_3480388
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470089457578076896336909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84626785943437435861782545 63470089457578076896336909)
  ·
    refine ⟨23801283546591778836126341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63470089457578076896336909 23801283546591778836126341)
    ·
      refine ⟨4462740664985958531773689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23801283546591778836126341 4462740664985958531773689)
      ·
        refine ⟨3347055498739468898830267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462740664985958531773689 3347055498739468898830267)
        ·
          refine ⟨5020583248109203348245401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347055498739468898830267 5020583248109203348245401)
          ·
            refine ⟨3765437436081902511184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5020583248109203348245401 3765437436081902511184051)
            ·
              refine ⟨5648156154122853766776077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765437436081902511184051 5648156154122853766776077)
              ·
                refine ⟨2118058557796070162541029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5648156154122853766776077 2118058557796070162541029)
                ·
                  refine ⟨397135979586763155476443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118058557796070162541029 397135979586763155476443)
                  ·
                    rfl

theorem cell22_3480388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3480388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480388 prefixEnd_3480388 := by exact prefixLift 3480388
  have htrace : WordTrace (prefixWord ++ tailWord_3480388) baseStart_3480388 baseEnd_3480388 := by
    simpa [prefixWord, tailWord_3480388, baseEnd_3480388] using wordTrace_append hprefix tailTrace_3480388
  have hstable : (prefixWord ++ tailWord_3480388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480388).length < 2 ^ (prefixWord ++ tailWord_3480388).sum := by decide
  have hdescent : baseEnd_3480388 < baseStart_3480388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480410 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_3480410 : Nat := 118140960795 + 3480410 * 2 ^ 59
def prefixEnd_3480410 : Nat := 4983230072969 + 3 ^ 40 * 3480410 * 2
def baseEnd_3480410 : Nat := 397138489936629580793087

theorem tailTrace_3480410 : CollatzResearch.WordTrace tailWord_3480410 prefixEnd_3480410 397138489936629580793087 := by
  unfold tailWord_3480410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31735245330269112887493671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84627320880717634366649789 31735245330269112887493671)
  ·
    refine ⟨47602867995403669331240507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31735245330269112887493671 47602867995403669331240507)
    ·
      refine ⟨71404301993105503996860761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47602867995403669331240507 71404301993105503996860761)
      ·
        refine ⟨53553226494829127997645571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71404301993105503996860761 53553226494829127997645571)
        ·
          refine ⟨80329839742243691996468357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53553226494829127997645571 80329839742243691996468357)
          ·
            refine ⟨15061844951670692249337817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80329839742243691996468357 15061844951670692249337817)
            ·
              refine ⟨11296383713753019187003363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15061844951670692249337817 11296383713753019187003363)
              ·
                refine ⟨16944575570629528780505045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296383713753019187003363 16944575570629528780505045)
                ·
                  refine ⟨397138489936629580793087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16944575570629528780505045 397138489936629580793087)
                  ·
                    rfl

theorem cell22_3480410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_3480410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480410 prefixEnd_3480410 := by exact prefixLift 3480410
  have htrace : WordTrace (prefixWord ++ tailWord_3480410) baseStart_3480410 baseEnd_3480410 := by
    simpa [prefixWord, tailWord_3480410, baseEnd_3480410] using wordTrace_append hprefix tailTrace_3480410
  have hstable : (prefixWord ++ tailWord_3480410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480410).length < 2 ^ (prefixWord ++ tailWord_3480410).sum := by decide
  have hdescent : baseEnd_3480410 < baseStart_3480410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480427 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 5]
def baseStart_3480427 : Nat := 118140960795 + 3480427 * 2 ^ 59
def prefixEnd_3480427 : Nat := 4983230072969 + 3 ^ 40 * 3480427 * 2
def baseEnd_3480427 : Nat := 397140429752435454901403

theorem tailTrace_3480427 : CollatzResearch.WordTrace tailWord_3480427 prefixEnd_3480427 397140429752435454901403 := by
  unfold tailWord_3480427
  simp only [CollatzResearch.WordTrace]
  refine ⟨126941601362014863453343535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84627734241343242302229023 126941601362014863453343535)
  ·
    refine ⟨190412402043022295180015303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126941601362014863453343535 190412402043022295180015303)
    ·
      refine ⟨285618603064533442770022955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190412402043022295180015303 285618603064533442770022955)
      ·
        refine ⟨428427904596800164155034433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285618603064533442770022955 428427904596800164155034433)
        ·
          refine ⟨321320928447600123116275825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428427904596800164155034433 321320928447600123116275825)
          ·
            refine ⟨240990696335700092337206869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321320928447600123116275825 240990696335700092337206869)
            ·
              refine ⟨2824109722683985457076643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 240990696335700092337206869 2824109722683985457076643)
              ·
                refine ⟨4236164584025978185614965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824109722683985457076643 4236164584025978185614965)
                ·
                  refine ⟨397140429752435454901403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236164584025978185614965 397140429752435454901403)
                  ·
                    rfl

theorem cell22_3480427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 5].length) (baseStart_3480427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480427 prefixEnd_3480427 := by exact prefixLift 3480427
  have htrace : WordTrace (prefixWord ++ tailWord_3480427) baseStart_3480427 baseEnd_3480427 := by
    simpa [prefixWord, tailWord_3480427, baseEnd_3480427] using wordTrace_append hprefix tailTrace_3480427
  have hstable : (prefixWord ++ tailWord_3480427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480427).length < 2 ^ (prefixWord ++ tailWord_3480427).sum := by decide
  have hdescent : baseEnd_3480427 < baseStart_3480427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480583 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3480583 : Nat := 118140960795 + 3480583 * 2 ^ 59
def prefixEnd_3480583 : Nat := 4983230072969 + 3 ^ 40 * 3480583 * 2
def baseEnd_3480583 : Nat := 1191474691245373957803731

theorem tailTrace_3480583 : CollatzResearch.WordTrace tailWord_3480583 prefixEnd_3480583 1191474691245373957803731 := by
  unfold tailWord_3480583
  simp only [CollatzResearch.WordTrace]
  refine ⟨126947291149449702096022403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84631527432966468064014935 126947291149449702096022403)
  ·
    refine ⟨190420936724174553144033605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126947291149449702096022403 190420936724174553144033605)
    ·
      refine ⟨35703925635782728714506301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190420936724174553144033605 35703925635782728714506301)
      ·
        refine ⟨13388972113418523267939863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35703925635782728714506301 13388972113418523267939863)
        ·
          refine ⟨20083458170127784901909795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388972113418523267939863 20083458170127784901909795)
          ·
            refine ⟨30125187255191677352864693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20083458170127784901909795 30125187255191677352864693)
            ·
              refine ⟨2824236305174219751831065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30125187255191677352864693 2824236305174219751831065)
              ·
                refine ⟨2118177228880664813873299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824236305174219751831065 2118177228880664813873299)
                ·
                  refine ⟨3177265843320997220809949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118177228880664813873299 3177265843320997220809949)
                  ·
                    refine ⟨1191474691245373957803731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177265843320997220809949 1191474691245373957803731)
                    ·
                      rfl

theorem cell22_3480583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3480583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480583 prefixEnd_3480583 := by exact prefixLift 3480583
  have htrace : WordTrace (prefixWord ++ tailWord_3480583) baseStart_3480583 baseEnd_3480583 := by
    simpa [prefixWord, tailWord_3480583, baseEnd_3480583] using wordTrace_append hprefix tailTrace_3480583
  have hstable : (prefixWord ++ tailWord_3480583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480583).length < 2 ^ (prefixWord ++ tailWord_3480583).sum := by decide
  have hdescent : baseEnd_3480583 < baseStart_3480583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480609 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3480609 : Nat := 118140960795 + 3480609 * 2 ^ 59
def prefixEnd_3480609 : Nat := 4983230072969 + 3 ^ 40 * 3480609 * 2
def baseEnd_3480609 : Nat := 1191483591576718556653651

theorem tailTrace_3480609 : CollatzResearch.WordTrace tailWord_3480609 prefixEnd_3480609 1191483591576718556653651 := by
  unfold tailWord_3480609
  simp only [CollatzResearch.WordTrace]
  refine ⟨126948239447355508536468881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84632159631570339024312587 126948239447355508536468881)
  ·
    refine ⟨95211179585516631402351661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126948239447355508536468881 95211179585516631402351661)
    ·
      refine ⟨35704192344568736775881873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95211179585516631402351661 35704192344568736775881873)
      ·
        refine ⟨26778144258426552581911405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35704192344568736775881873 26778144258426552581911405)
        ·
          refine ⟨10041804096909957218216777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26778144258426552581911405 10041804096909957218216777)
          ·
            refine ⟨7531353072682467913662583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10041804096909957218216777 7531353072682467913662583)
            ·
              refine ⟨11297029609023701870493875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531353072682467913662583 11297029609023701870493875)
              ·
                refine ⟨16945544413535552805740813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11297029609023701870493875 16945544413535552805740813)
                ·
                  refine ⟨6354579155075832302152805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16945544413535552805740813 6354579155075832302152805)
                  ·
                    refine ⟨1191483591576718556653651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354579155075832302152805 1191483591576718556653651)
                    ·
                      rfl

theorem cell22_3480609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3480609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480609 prefixEnd_3480609 := by exact prefixLift 3480609
  have htrace : WordTrace (prefixWord ++ tailWord_3480609) baseStart_3480609 baseEnd_3480609 := by
    simpa [prefixWord, tailWord_3480609, baseEnd_3480609] using wordTrace_append hprefix tailTrace_3480609
  have hstable : (prefixWord ++ tailWord_3480609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480609).length < 2 ^ (prefixWord ++ tailWord_3480609).sum := by decide
  have hdescent : baseEnd_3480609 < baseStart_3480609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480624 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_3480624 : Nat := 118140960795 + 3480624 * 2 ^ 59
def prefixEnd_3480624 : Nat := 4983230072969 + 3 ^ 40 * 3480624 * 2
def baseEnd_3480624 : Nat := 397162908794421172509535

theorem tailTrace_3480624 : CollatzResearch.WordTrace tailWord_3480624 prefixEnd_3480624 397162908794421172509535 := by
  unfold tailWord_3480624
  simp only [CollatzResearch.WordTrace]
  refine ⟨63474393271150583049132463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84632524361534110732176617 63474393271150583049132463)
  ·
    refine ⟨95211589906725874573698695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63474393271150583049132463 95211589906725874573698695)
    ·
      refine ⟨142817384860088811860548043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95211589906725874573698695 142817384860088811860548043)
      ·
        refine ⟨214226077290133217790822065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142817384860088811860548043 214226077290133217790822065)
        ·
          refine ⟨160669557967599913343116549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214226077290133217790822065 160669557967599913343116549)
          ·
            refine ⟨30125542118924983751834353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160669557967599913343116549 30125542118924983751834353)
            ·
              refine ⟨22594156589193737813875765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30125542118924983751834353 22594156589193737813875765)
              ·
                refine ⟨2118202180236912920050853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22594156589193737813875765 2118202180236912920050853)
                ·
                  refine ⟨397162908794421172509535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118202180236912920050853 397162908794421172509535)
                  ·
                    rfl

theorem cell22_3480624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_3480624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480624 prefixEnd_3480624 := by exact prefixLift 3480624
  have htrace : WordTrace (prefixWord ++ tailWord_3480624) baseStart_3480624 baseEnd_3480624 := by
    simpa [prefixWord, tailWord_3480624, baseEnd_3480624] using wordTrace_append hprefix tailTrace_3480624
  have hstable : (prefixWord ++ tailWord_3480624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480624).length < 2 ^ (prefixWord ++ tailWord_3480624).sum := by decide
  have hdescent : baseEnd_3480624 < baseStart_3480624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480626 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_3480626 : Nat := 118140960795 + 3480626 * 2 ^ 59
def prefixEnd_3480626 : Nat := 4983230072969 + 3 ^ 40 * 3480626 * 2
def baseEnd_3480626 : Nat := 1191489411024136178978599

theorem tailTrace_3480626 : CollatzResearch.WordTrace tailWord_3480626 prefixEnd_3480626 1191489411024136178978599 := by
  unfold tailWord_3480626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31737214872073480109959433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84632572992195946959891821 31737214872073480109959433)
  ·
    refine ⟨23802911154055110082469575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31737214872073480109959433 23802911154055110082469575)
    ·
      refine ⟨35704366731082665123704363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23802911154055110082469575 35704366731082665123704363)
      ·
        refine ⟨53556550096623997685556545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35704366731082665123704363 53556550096623997685556545)
        ·
          refine ⟨40167412572467998264167409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53556550096623997685556545 40167412572467998264167409)
          ·
            refine ⟨30125559429350998698125557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40167412572467998264167409 30125559429350998698125557)
            ·
              refine ⟨2824271196501656127949271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30125559429350998698125557 2824271196501656127949271)
              ·
                refine ⟨4236406794752484191923907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824271196501656127949271 4236406794752484191923907)
                ·
                  refine ⟨6354610192128726287885861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236406794752484191923907 6354610192128726287885861)
                  ·
                    refine ⟨1191489411024136178978599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354610192128726287885861 1191489411024136178978599)
                    ·
                      rfl

theorem cell22_3480626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_3480626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480626 prefixEnd_3480626 := by exact prefixLift 3480626
  have htrace : WordTrace (prefixWord ++ tailWord_3480626) baseStart_3480626 baseEnd_3480626 := by
    simpa [prefixWord, tailWord_3480626, baseEnd_3480626] using wordTrace_append hprefix tailTrace_3480626
  have hstable : (prefixWord ++ tailWord_3480626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480626).length < 2 ^ (prefixWord ++ tailWord_3480626).sum := by decide
  have hdescent : baseEnd_3480626 < baseStart_3480626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480684 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_3480684 : Nat := 118140960795 + 3480684 * 2 ^ 59
def prefixEnd_3480684 : Nat := 4983230072969 + 3 ^ 40 * 3480684 * 2
def baseEnd_3480684 : Nat := 1191509265609443361028421

theorem tailTrace_3480684 : CollatzResearch.WordTrace tailWord_3480684 prefixEnd_3480684 1191509265609443361028421 := by
  unfold tailWord_3480684
  simp only [CollatzResearch.WordTrace]
  refine ⟨63475487461041898172724553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84633983281389197563632737 63475487461041898172724553)
  ·
    refine ⟨47606615595781423629543415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63475487461041898172724553 47606615595781423629543415)
    ·
      refine ⟨71409923393672135444315123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47606615595781423629543415 71409923393672135444315123)
      ·
        refine ⟨107114885090508203166472685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71409923393672135444315123 107114885090508203166472685)
        ·
          refine ⟨40168081908940576187427257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107114885090508203166472685 40168081908940576187427257)
          ·
            refine ⟨30126061431705432140570443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40168081908940576187427257 30126061431705432140570443)
            ·
              refine ⟨45189092147558148210855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30126061431705432140570443 45189092147558148210855665)
              ·
                refine ⟨33891819110668611158141749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45189092147558148210855665 33891819110668611158141749)
                ·
                  refine ⟨3177358041625182296075789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33891819110668611158141749 3177358041625182296075789)
                  ·
                    refine ⟨1191509265609443361028421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177358041625182296075789 1191509265609443361028421)
                    ·
                      rfl

theorem cell22_3480684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_3480684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480684 prefixEnd_3480684 := by exact prefixLift 3480684
  have htrace : WordTrace (prefixWord ++ tailWord_3480684) baseStart_3480684 baseEnd_3480684 := by
    simpa [prefixWord, tailWord_3480684, baseEnd_3480684] using wordTrace_append hprefix tailTrace_3480684
  have hstable : (prefixWord ++ tailWord_3480684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480684).length < 2 ^ (prefixWord ++ tailWord_3480684).sum := by decide
  have hdescent : baseEnd_3480684 < baseStart_3480684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480701 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_3480701 : Nat := 118140960795 + 3480701 * 2 ^ 59
def prefixEnd_3480701 : Nat := 4983230072969 + 3 ^ 40 * 3480701 * 2
def baseEnd_3480701 : Nat := 1191515085056860983353369

theorem tailTrace_3480701 : CollatzResearch.WordTrace tailWord_3480701 prefixEnd_3480701 1191515085056860983353369 := by
  unfold tailWord_3480701
  simp only [CollatzResearch.WordTrace]
  refine ⟨126951594963022208248817957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84634396642014805499211971 126951594963022208248817957)
  ·
    refine ⟨23803424055566664046653367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126951594963022208248817957 23803424055566664046653367)
    ·
      refine ⟨35705136083349996069980051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23803424055566664046653367 35705136083349996069980051)
      ·
        refine ⟨53557704125024994104970077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35705136083349996069980051 53557704125024994104970077)
        ·
          refine ⟨20084139046884372789363779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53557704125024994104970077 20084139046884372789363779)
          ·
            refine ⟨30126208570326559184045669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20084139046884372789363779 30126208570326559184045669)
            ·
              refine ⟨5648664106936229847008563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30126208570326559184045669 5648664106936229847008563)
              ·
                refine ⟨8472996160404344770512845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648664106936229847008563 8472996160404344770512845)
                ·
                  refine ⟨3177373560151629288942317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8472996160404344770512845 3177373560151629288942317)
                  ·
                    refine ⟨1191515085056860983353369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177373560151629288942317 1191515085056860983353369)
                    ·
                      rfl

theorem cell22_3480701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_3480701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480701 prefixEnd_3480701 := by exact prefixLift 3480701
  have htrace : WordTrace (prefixWord ++ tailWord_3480701) baseStart_3480701 baseEnd_3480701 := by
    simpa [prefixWord, tailWord_3480701, baseEnd_3480701] using wordTrace_append hprefix tailTrace_3480701
  have hstable : (prefixWord ++ tailWord_3480701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480701).length < 2 ^ (prefixWord ++ tailWord_3480701).sum := by decide
  have hdescent : baseEnd_3480701 < baseStart_3480701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480778 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3480778 : Nat := 118140960795 + 3480778 * 2 ^ 59
def prefixEnd_3480778 : Nat := 4983230072969 + 3 ^ 40 * 3480778 * 2
def baseEnd_3480778 : Nat := 1191541443730458449178133

theorem tailTrace_3480778 : CollatzResearch.WordTrace tailWord_3480778 prefixEnd_3480778 1191541443730458449178133 := by
  unfold tailWord_3480778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738600845935812599842747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84636268922495500266247325 31738600845935812599842747)
  ·
    refine ⟨47607901268903718899764121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31738600845935812599842747 47607901268903718899764121)
    ·
      refine ⟨35705925951677789174823091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47607901268903718899764121 35705925951677789174823091)
      ·
        refine ⟨53558888927516683762234637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35705925951677789174823091 53558888927516683762234637)
        ·
          refine ⟨20084583347818756410837989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53558888927516683762234637 20084583347818756410837989)
          ·
            refine ⟨3765859377716016827032123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20084583347818756410837989 3765859377716016827032123)
            ·
              refine ⟨5648789066574025240548185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765859377716016827032123 5648789066574025240548185)
              ·
                refine ⟨4236591799930518930411139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648789066574025240548185 4236591799930518930411139)
                ·
                  refine ⟨6354887699895778395616709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236591799930518930411139 6354887699895778395616709)
                  ·
                    refine ⟨1191541443730458449178133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354887699895778395616709 1191541443730458449178133)
                    ·
                      rfl

theorem cell22_3480778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3480778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480778 prefixEnd_3480778 := by exact prefixLift 3480778
  have htrace : WordTrace (prefixWord ++ tailWord_3480778) baseStart_3480778 baseEnd_3480778 := by
    simpa [prefixWord, tailWord_3480778, baseEnd_3480778] using wordTrace_append hprefix tailTrace_3480778
  have hstable : (prefixWord ++ tailWord_3480778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480778).length < 2 ^ (prefixWord ++ tailWord_3480778).sum := by decide
  have hdescent : baseEnd_3480778 < baseStart_3480778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480808 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3480808 : Nat := 118140960795 + 3480808 * 2 ^ 59
def prefixEnd_3480808 : Nat := 4983230072969 + 3 ^ 40 * 3480808 * 2
def baseEnd_3480808 : Nat := 1191551713343548370928041

theorem tailTrace_3480808 : CollatzResearch.WordTrace tailWord_3480808 prefixEnd_3480808 1191551713343548370928041 := by
  unfold tailWord_3480808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63477748786817282761481539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84636998382423043681975385 63477748786817282761481539)
  ·
    refine ⟨95216623180225924142222309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63477748786817282761481539 95216623180225924142222309)
    ·
      refine ⟨17853116846292360776666683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95216623180225924142222309 17853116846292360776666683)
      ·
        refine ⟨26779675269438541165000025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853116846292360776666683 26779675269438541165000025)
        ·
          refine ⟨20084756452078905873750019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26779675269438541165000025 20084756452078905873750019)
          ·
            refine ⟨30127134678118358810625029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20084756452078905873750019 30127134678118358810625029)
            ·
              refine ⟨5648837752147192276992193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30127134678118358810625029 5648837752147192276992193)
              ·
                refine ⟨4236628314110394207744145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648837752147192276992193 4236628314110394207744145)
                ·
                  refine ⟨3177471235582795655808109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236628314110394207744145 3177471235582795655808109)
                  ·
                    refine ⟨1191551713343548370928041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177471235582795655808109 1191551713343548370928041)
                    ·
                      rfl

theorem cell22_3480808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3480808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480808 prefixEnd_3480808 := by exact prefixLift 3480808
  have htrace : WordTrace (prefixWord ++ tailWord_3480808) baseStart_3480808 baseEnd_3480808 := by
    simpa [prefixWord, tailWord_3480808, baseEnd_3480808] using wordTrace_append hprefix tailTrace_3480808
  have hstable : (prefixWord ++ tailWord_3480808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480808).length < 2 ^ (prefixWord ++ tailWord_3480808).sum := by decide
  have hdescent : baseEnd_3480808 < baseStart_3480808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480810 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_3480810 : Nat := 118140960795 + 3480810 * 2 ^ 59
def prefixEnd_3480810 : Nat := 4983230072969 + 3 ^ 40 * 3480810 * 2
def baseEnd_3480810 : Nat := 397184132661473677459345

theorem tailTrace_3480810 : CollatzResearch.WordTrace tailWord_3480810 prefixEnd_3480810 397184132661473677459345 := by
  unfold tailWord_3480810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738892629906829966133971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84637047013084879909690589 31738892629906829966133971)
  ·
    refine ⟨47608338944860244949200957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31738892629906829966133971 47608338944860244949200957)
    ·
      refine ⟨17853127104322591855950359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47608338944860244949200957 17853127104322591855950359)
      ·
        refine ⟨26779690656483887783925539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853127104322591855950359 26779690656483887783925539)
        ·
          refine ⟨40169535984725831675888309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779690656483887783925539 40169535984725831675888309)
          ·
            refine ⟨3765893998568046719614529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40169535984725831675888309 3765893998568046719614529)
            ·
              refine ⟨2824420498926035039710897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765893998568046719614529 2824420498926035039710897)
              ·
                refine ⟨2118315374194526279783173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824420498926035039710897 2118315374194526279783173)
                ·
                  refine ⟨397184132661473677459345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118315374194526279783173 397184132661473677459345)
                  ·
                    rfl

theorem cell22_3480810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_3480810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480810 prefixEnd_3480810 := by exact prefixLift 3480810
  have htrace : WordTrace (prefixWord ++ tailWord_3480810) baseStart_3480810 baseEnd_3480810 := by
    simpa [prefixWord, tailWord_3480810, baseEnd_3480810] using wordTrace_append hprefix tailTrace_3480810
  have hstable : (prefixWord ++ tailWord_3480810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480810).length < 2 ^ (prefixWord ++ tailWord_3480810).sum := by decide
  have hdescent : baseEnd_3480810 < baseStart_3480810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480840 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_3480840 : Nat := 118140960795 + 3480840 * 2 ^ 59
def prefixEnd_3480840 : Nat := 4983230072969 + 3 ^ 40 * 3480840 * 2
def baseEnd_3480840 : Nat := 1191562667597510954127943

theorem tailTrace_3480840 : CollatzResearch.WordTrace tailWord_3480840 prefixEnd_3480840 1191562667597510954127943 := by
  unfold tailWord_3480840
  simp only [CollatzResearch.WordTrace]
  refine ⟨63478332354759317494063987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84637776473012423325418649 63478332354759317494063987)
  ·
    refine ⟨95217498532138976241095981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63478332354759317494063987 95217498532138976241095981)
    ·
      refine ⟨35706561949552116090410993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95217498532138976241095981 35706561949552116090410993)
      ·
        refine ⟨26779921462164087067808245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35706561949552116090410993 26779921462164087067808245)
        ·
          refine ⟨2510617637077883162607023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26779921462164087067808245 2510617637077883162607023)
          ·
            refine ⟨3765926455616824743910535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510617637077883162607023 3765926455616824743910535)
            ·
              refine ⟨5648889683425237115865803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765926455616824743910535 5648889683425237115865803)
              ·
                refine ⟨8473334525137855673798705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648889683425237115865803 8473334525137855673798705)
                ·
                  refine ⟨6355000893853391755349029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8473334525137855673798705 6355000893853391755349029)
                  ·
                    refine ⟨1191562667597510954127943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355000893853391755349029 1191562667597510954127943)
                    ·
                      rfl

theorem cell22_3480840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_3480840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480840 prefixEnd_3480840 := by exact prefixLift 3480840
  have htrace : WordTrace (prefixWord ++ tailWord_3480840) baseStart_3480840 baseEnd_3480840 := by
    simpa [prefixWord, tailWord_3480840, baseEnd_3480840] using wordTrace_append hprefix tailTrace_3480840
  have hstable : (prefixWord ++ tailWord_3480840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480840).length < 2 ^ (prefixWord ++ tailWord_3480840).sum := by decide
  have hdescent : baseEnd_3480840 < baseStart_3480840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480849 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 7]
def baseStart_3480849 : Nat := 118140960795 + 3480849 * 2 ^ 59
def prefixEnd_3480849 : Nat := 4983230072969 + 3 ^ 40 * 3480849 * 2
def baseEnd_3480849 : Nat := 397188582827145976884305

theorem tailTrace_3480849 : CollatzResearch.WordTrace tailWord_3480849 prefixEnd_3480849 397188582827145976884305 := by
  unfold tailWord_3480849
  simp only [CollatzResearch.WordTrace]
  refine ⟨126956992966486029525205601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84637995310990686350137067 126956992966486029525205601)
  ·
    refine ⟨95217744724864522143904201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126956992966486029525205601 95217744724864522143904201)
    ·
      refine ⟨71413308543648391607928151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95217744724864522143904201 71413308543648391607928151)
      ·
        refine ⟨107119962815472587411892227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71413308543648391607928151 107119962815472587411892227)
        ·
          refine ⟨160679944223208881117838341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107119962815472587411892227 160679944223208881117838341)
          ·
            refine ⟨30127489541851665209594689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160679944223208881117838341 30127489541851665209594689)
            ·
              refine ⟨22595617156388748907196017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30127489541851665209594689 22595617156388748907196017)
              ·
                refine ⟨16946712867291561680397013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22595617156388748907196017 16946712867291561680397013)
                ·
                  refine ⟨397188582827145976884305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16946712867291561680397013 397188582827145976884305)
                  ·
                    rfl

theorem cell22_3480849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_3480849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480849 prefixEnd_3480849 := by exact prefixLift 3480849
  have htrace : WordTrace (prefixWord ++ tailWord_3480849) baseStart_3480849 baseEnd_3480849 := by
    simpa [prefixWord, tailWord_3480849, baseEnd_3480849] using wordTrace_append hprefix tailTrace_3480849
  have hstable : (prefixWord ++ tailWord_3480849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480849).length < 2 ^ (prefixWord ++ tailWord_3480849).sum := by decide
  have hdescent : baseEnd_3480849 < baseStart_3480849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480881 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3480881 : Nat := 118140960795 + 3480881 * 2 ^ 59
def prefixEnd_3480881 : Nat := 4983230072969 + 3 ^ 40 * 3480881 * 2
def baseEnd_3480881 : Nat := 1191576702735400513852817

theorem tailTrace_3480881 : CollatzResearch.WordTrace tailWord_3480881 prefixEnd_3480881 1191576702735400513852817 := by
  unfold tailWord_3480881
  simp only [CollatzResearch.WordTrace]
  refine ⟨126958160102370098990370497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84638773401580065993580331 126958160102370098990370497)
  ·
    refine ⟨95218620076777574242777873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126958160102370098990370497 95218620076777574242777873)
    ·
      refine ⟨71413965057583180682083405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95218620076777574242777873 71413965057583180682083405)
      ·
        refine ⟨26780236896593692755781277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71413965057583180682083405 26780236896593692755781277)
        ·
          refine ⟨10042588836222634783417979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26780236896593692755781277 10042588836222634783417979)
          ·
            refine ⟨15063883254333952175126969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042588836222634783417979 15063883254333952175126969)
            ·
              refine ⟨11297912440750464131345227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15063883254333952175126969 11297912440750464131345227)
              ·
                refine ⟨16946868661125696197017841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11297912440750464131345227 16946868661125696197017841)
                ·
                  refine ⟨12710151495844272147763381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16946868661125696197017841 12710151495844272147763381)
                  ·
                    refine ⟨1191576702735400513852817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12710151495844272147763381 1191576702735400513852817)
                    ·
                      rfl

theorem cell22_3480881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3480881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480881 prefixEnd_3480881 := by exact prefixLift 3480881
  have htrace : WordTrace (prefixWord ++ tailWord_3480881) baseStart_3480881 baseEnd_3480881 := by
    simpa [prefixWord, tailWord_3480881, baseEnd_3480881] using wordTrace_append hprefix tailTrace_3480881
  have hstable : (prefixWord ++ tailWord_3480881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480881).length < 2 ^ (prefixWord ++ tailWord_3480881).sum := by decide
  have hdescent : baseEnd_3480881 < baseStart_3480881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480883 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 5]
def baseStart_3480883 : Nat := 118140960795 + 3480883 * 2 ^ 59
def prefixEnd_3480883 : Nat := 4983230072969 + 3 ^ 40 * 3480883 * 2
def baseEnd_3480883 : Nat := 397192462458757725100937

theorem tailTrace_3480883 : CollatzResearch.WordTrace tailWord_3480883 prefixEnd_3480883 397192462458757725100937 := by
  unfold tailWord_3480883
  simp only [CollatzResearch.WordTrace]
  refine ⟨126958233048362853331943303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84638822032241902221295535 126958233048362853331943303)
  ·
    refine ⟨190437349572544279997914955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126958233048362853331943303 190437349572544279997914955)
    ·
      refine ⟨285656024358816419996872433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190437349572544279997914955 285656024358816419996872433)
      ·
        refine ⟨214242018269112314997654325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285656024358816419996872433 214242018269112314997654325)
        ·
          refine ⟨20085189212729279531030093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214242018269112314997654325 20085189212729279531030093)
          ·
            refine ⟨7531945954773479824136285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20085189212729279531030093 7531945954773479824136285)
            ·
              refine ⟨2824479733040054934051107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7531945954773479824136285 2824479733040054934051107)
              ·
                refine ⟨4236719599560082401076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824479733040054934051107 4236719599560082401076661)
                ·
                  refine ⟨397192462458757725100937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236719599560082401076661 397192462458757725100937)
                  ·
                    rfl

theorem cell22_3480883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 5].length) (baseStart_3480883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480883 prefixEnd_3480883 := by exact prefixLift 3480883
  have htrace : WordTrace (prefixWord ++ tailWord_3480883) baseStart_3480883 baseEnd_3480883 := by
    simpa [prefixWord, tailWord_3480883, baseEnd_3480883] using wordTrace_append hprefix tailTrace_3480883
  have hstable : (prefixWord ++ tailWord_3480883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480883).length < 2 ^ (prefixWord ++ tailWord_3480883).sum := by decide
  have hdescent : baseEnd_3480883 < baseStart_3480883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480928 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_3480928 : Nat := 118140960795 + 3480928 * 2 ^ 59
def prefixEnd_3480928 : Nat := 4983230072969 + 3 ^ 40 * 3480928 * 2
def baseEnd_3480928 : Nat := 397197597265302685975891

theorem tailTrace_3480928 : CollatzResearch.WordTrace tailWord_3480928 prefixEnd_3480928 397197597265302685975891 := by
  unfold tailWord_3480928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63479937166599913008665719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84639916222133217344887625 63479937166599913008665719)
  ·
    refine ⟨95219905749899869512998579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63479937166599913008665719 95219905749899869512998579)
    ·
      refine ⟨142829858624849804269497869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95219905749899869512998579 142829858624849804269497869)
      ·
        refine ⟨53561196984318676601061701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142829858624849804269497869 53561196984318676601061701)
        ·
          refine ⟨10042724434559751862699069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53561196984318676601061701 10042724434559751862699069)
          ·
            refine ⟨3766021662959906948512151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10042724434559751862699069 3766021662959906948512151)
            ·
              refine ⟨5649032494439860422768227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766021662959906948512151 5649032494439860422768227)
              ·
                refine ⟨8473548741659790634152341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649032494439860422768227 8473548741659790634152341)
                ·
                  refine ⟨397197597265302685975891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8473548741659790634152341 397197597265302685975891)
                  ·
                    rfl

theorem cell22_3480928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_3480928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480928 prefixEnd_3480928 := by exact prefixLift 3480928
  have htrace : WordTrace (prefixWord ++ tailWord_3480928) baseStart_3480928 baseEnd_3480928 := by
    simpa [prefixWord, tailWord_3480928, baseEnd_3480928] using wordTrace_append hprefix tailTrace_3480928
  have hstable : (prefixWord ++ tailWord_3480928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480928).length < 2 ^ (prefixWord ++ tailWord_3480928).sum := by decide
  have hdescent : baseEnd_3480928 < baseStart_3480928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480943 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 2, 3]
def baseStart_3480943 : Nat := 118140960795 + 3480943 * 2 ^ 59
def prefixEnd_3480943 : Nat := 4983230072969 + 3 ^ 40 * 3480943 * 2
def baseEnd_3480943 : Nat := 1191597926602453018802627

theorem tailTrace_3480943 : CollatzResearch.WordTrace tailWord_3480943 prefixEnd_3480943 1191597926602453018802627 := by
  unfold tailWord_3480943
  simp only [CollatzResearch.WordTrace]
  refine ⟨126960421428145483579127483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84640280952096989052751655 126960421428145483579127483)
  ·
    refine ⟨190440632142218225368691225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126960421428145483579127483 190440632142218225368691225)
    ·
      refine ⟨142830474106663669026518419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190440632142218225368691225 142830474106663669026518419)
      ·
        refine ⟨214245711159995503539777629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142830474106663669026518419 214245711159995503539777629)
        ·
          refine ⟨80342141684998313827416611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214245711159995503539777629 80342141684998313827416611)
          ·
            refine ⟨120513212527497470741124917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80342141684998313827416611 120513212527497470741124917)
            ·
              refine ⟨11298113674452887881980461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120513212527497470741124917 11298113674452887881980461)
              ·
                refine ⟨4236792627919832955742673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11298113674452887881980461 4236792627919832955742673)
                ·
                  refine ⟨3177594470939874716807005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236792627919832955742673 3177594470939874716807005)
                  ·
                    refine ⟨1191597926602453018802627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177594470939874716807005 1191597926602453018802627)
                    ·
                      rfl

theorem cell22_3480943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_3480943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480943 prefixEnd_3480943 := by exact prefixLift 3480943
  have htrace : WordTrace (prefixWord ++ tailWord_3480943) baseStart_3480943 baseEnd_3480943 := by
    simpa [prefixWord, tailWord_3480943, baseEnd_3480943] using wordTrace_append hprefix tailTrace_3480943
  have hstable : (prefixWord ++ tailWord_3480943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480943).length < 2 ^ (prefixWord ++ tailWord_3480943).sum := by decide
  have hdescent : baseEnd_3480943 < baseStart_3480943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3480986 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_3480986 : Nat := 118140960795 + 3480986 * 2 ^ 59
def prefixEnd_3480986 : Nat := 4983230072969 + 3 ^ 40 * 3480986 * 2
def baseEnd_3480986 : Nat := 1191612646381215239977495

theorem tailTrace_3480986 : CollatzResearch.WordTrace tailWord_3480986 prefixEnd_3480986 1191612646381215239977495 := by
  unfold tailWord_3480986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31740497441747425480735703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84641326511326467948628541 31740497441747425480735703)
  ·
    refine ⟨47610746162621138221103555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31740497441747425480735703 47610746162621138221103555)
    ·
      refine ⟨71416119243931707331655333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47610746162621138221103555 71416119243931707331655333)
      ·
        refine ⟨13390522358237195124685375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71416119243931707331655333 13390522358237195124685375)
        ·
          refine ⟨20085783537355792687028063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390522358237195124685375 20085783537355792687028063)
          ·
            refine ⟨30128675306033689030542095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20085783537355792687028063 30128675306033689030542095)
            ·
              refine ⟨45193012959050533545813143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30128675306033689030542095 45193012959050533545813143)
              ·
                refine ⟨67789519438575800318719715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45193012959050533545813143 67789519438575800318719715)
                ·
                  refine ⟨101684279157863700478079573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67789519438575800318719715 101684279157863700478079573)
                  ·
                    refine ⟨1191612646381215239977495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101684279157863700478079573 1191612646381215239977495)
                    ·
                      rfl

theorem cell22_3480986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_3480986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3480986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3480986 prefixEnd_3480986 := by exact prefixLift 3480986
  have htrace : WordTrace (prefixWord ++ tailWord_3480986) baseStart_3480986 baseEnd_3480986 := by
    simpa [prefixWord, tailWord_3480986, baseEnd_3480986] using wordTrace_append hprefix tailTrace_3480986
  have hstable : (prefixWord ++ tailWord_3480986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3480986).length < 2 ^ (prefixWord ++ tailWord_3480986).sum := by decide
  have hdescent : baseEnd_3480986 < baseStart_3480986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3480986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481005 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3481005 : Nat := 118140960795 + 3481005 * 2 ^ 59
def prefixEnd_3481005 : Nat := 4983230072969 + 3 ^ 40 * 3481005 * 2
def baseEnd_3481005 : Nat := 1191619150469505523752437

theorem tailTrace_3481005 : CollatzResearch.WordTrace tailWord_3481005 prefixEnd_3481005 1191619150469505523752437 := by
  unfold tailWord_3481005
  simp only [CollatzResearch.WordTrace]
  refine ⟨126962682753920868167884469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84641788502613912111922979 126962682753920868167884469)
  ·
    refine ⟨11902751508180081390739169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126962682753920868167884469 11902751508180081390739169)
    ·
      refine ⟨8927063631135061043054377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11902751508180081390739169 8927063631135061043054377)
      ·
        refine ⟨6695297723351295782290783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8927063631135061043054377 6695297723351295782290783)
        ·
          refine ⟨10042946585026943673436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695297723351295782290783 10042946585026943673436175)
          ·
            refine ⟨15064419877540415510154263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042946585026943673436175 15064419877540415510154263)
            ·
              refine ⟨22596629816310623265231395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15064419877540415510154263 22596629816310623265231395)
              ·
                refine ⟨33894944724465934897847093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22596629816310623265231395 33894944724465934897847093)
                ·
                  refine ⟨3177651067918681396673165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33894944724465934897847093 3177651067918681396673165)
                  ·
                    refine ⟨1191619150469505523752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177651067918681396673165 1191619150469505523752437)
                    ·
                      rfl

theorem cell22_3481005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3481005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481005 prefixEnd_3481005 := by exact prefixLift 3481005
  have htrace : WordTrace (prefixWord ++ tailWord_3481005) baseStart_3481005 baseEnd_3481005 := by
    simpa [prefixWord, tailWord_3481005, baseEnd_3481005] using wordTrace_append hprefix tailTrace_3481005
  have hstable : (prefixWord ++ tailWord_3481005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481005).length < 2 ^ (prefixWord ++ tailWord_3481005).sum := by decide
  have hdescent : baseEnd_3481005 < baseStart_3481005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481063 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 6]
def baseStart_3481063 : Nat := 118140960795 + 3481063 * 2 ^ 59
def prefixEnd_3481063 : Nat := 4983230072969 + 3 ^ 40 * 3481063 * 2
def baseEnd_3481063 : Nat := 397213001684937568600753

theorem tailTrace_3481063 : CollatzResearch.WordTrace tailWord_3481063 prefixEnd_3481063 397213001684937568600753 := by
  unfold tailWord_3481063
  simp only [CollatzResearch.WordTrace]
  refine ⟨126964798187710744073495843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84643198791807162715663895 126964798187710744073495843)
  ·
    refine ⟨190447197281566116110243765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126964798187710744073495843 190447197281566116110243765)
    ·
      refine ⟨17854424745146823385335353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190447197281566116110243765 17854424745146823385335353)
      ·
        refine ⟨13390818558860117539001515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17854424745146823385335353 13390818558860117539001515)
        ·
          refine ⟨20086227838290176308502273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390818558860117539001515 20086227838290176308502273)
          ·
            refine ⟨15064670878717632231376705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20086227838290176308502273 15064670878717632231376705)
            ·
              refine ⟨11298503159038224173532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15064670878717632231376705 11298503159038224173532529)
              ·
                refine ⟨8473877369278668130149397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11298503159038224173532529 8473877369278668130149397)
                ·
                  refine ⟨397213001684937568600753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8473877369278668130149397 397213001684937568600753)
                  ·
                    rfl

theorem cell22_3481063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_3481063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481063 prefixEnd_3481063 := by exact prefixLift 3481063
  have htrace : WordTrace (prefixWord ++ tailWord_3481063) baseStart_3481063 baseEnd_3481063 := by
    simpa [prefixWord, tailWord_3481063, baseEnd_3481063] using wordTrace_append hprefix tailTrace_3481063
  have hstable : (prefixWord ++ tailWord_3481063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481063).length < 2 ^ (prefixWord ++ tailWord_3481063).sum := by decide
  have hdescent : baseEnd_3481063 < baseStart_3481063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481080 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_3481080 : Nat := 118140960795 + 3481080 * 2 ^ 59
def prefixEnd_3481080 : Nat := 4983230072969 + 3 ^ 40 * 3481080 * 2
def baseEnd_3481080 : Nat := 397214941500743442709069

theorem tailTrace_3481080 : CollatzResearch.WordTrace tailWord_3481080 prefixEnd_3481080 397214941500743442709069 := by
  unfold tailWord_3481080
  simp only [CollatzResearch.WordTrace]
  refine ⟨63482709114324577988432347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84643612152432770651243129 63482709114324577988432347)
  ·
    refine ⟨95224063671486866982648521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63482709114324577988432347 95224063671486866982648521)
    ·
      refine ⟨71418047753615150236986391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95224063671486866982648521 71418047753615150236986391)
      ·
        refine ⟨107127071630422725355479587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71418047753615150236986391 107127071630422725355479587)
        ·
          refine ⟨160690607445634088033219381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107127071630422725355479587 160690607445634088033219381)
          ·
            refine ⟨15064744448028195753114317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160690607445634088033219381 15064744448028195753114317)
            ·
              refine ⟨5649279168010573407417869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15064744448028195753114317 5649279168010573407417869)
              ·
                refine ⟨2118479688003965027781701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5649279168010573407417869 2118479688003965027781701)
                ·
                  refine ⟨397214941500743442709069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118479688003965027781701 397214941500743442709069)
                  ·
                    rfl

theorem cell22_3481080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_3481080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481080 prefixEnd_3481080 := by exact prefixLift 3481080
  have htrace : WordTrace (prefixWord ++ tailWord_3481080) baseStart_3481080 baseEnd_3481080 := by
    simpa [prefixWord, tailWord_3481080, baseEnd_3481080] using wordTrace_append hprefix tailTrace_3481080
  have hstable : (prefixWord ++ tailWord_3481080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481080).length < 2 ^ (prefixWord ++ tailWord_3481080).sum := by decide
  have hdescent : baseEnd_3481080 < baseStart_3481080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481095 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3481095 : Nat := 118140960795 + 3481095 * 2 ^ 59
def prefixEnd_3481095 : Nat := 4983230072969 + 3 ^ 40 * 3481095 * 2
def baseEnd_3481095 : Nat := 1191649959308775289002161

theorem tailTrace_3481095 : CollatzResearch.WordTrace tailWord_3481095 prefixEnd_3481095 1191649959308775289002161 := by
  unfold tailWord_3481095
  simp only [CollatzResearch.WordTrace]
  refine ⟨126965965323594813538660739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84643976882396542359107159 126965965323594813538660739)
  ·
    refine ⟨190448947985392220307991109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126965965323594813538660739 190448947985392220307991109)
    ·
      refine ⟨35709177747261041307748333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190448947985392220307991109 35709177747261041307748333)
      ·
        refine ⟨13390941655222890490405625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35709177747261041307748333 13390941655222890490405625)
        ·
          refine ⟨10043206241417167867804219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13390941655222890490405625 10043206241417167867804219)
          ·
            refine ⟨15064809362125751801706329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043206241417167867804219 15064809362125751801706329)
            ·
              refine ⟨11298607021594313851279747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15064809362125751801706329 11298607021594313851279747)
              ·
                refine ⟨16947910532391470776919621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11298607021594313851279747 16947910532391470776919621)
                ·
                  refine ⟨3177733224823400770672429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16947910532391470776919621 3177733224823400770672429)
                  ·
                    refine ⟨1191649959308775289002161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177733224823400770672429 1191649959308775289002161)
                    ·
                      rfl

theorem cell22_3481095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3481095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481095 prefixEnd_3481095 := by exact prefixLift 3481095
  have htrace : WordTrace (prefixWord ++ tailWord_3481095) baseStart_3481095 baseEnd_3481095 := by
    simpa [prefixWord, tailWord_3481095, baseEnd_3481095] using wordTrace_append hprefix tailTrace_3481095
  have hstable : (prefixWord ++ tailWord_3481095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481095).length < 2 ^ (prefixWord ++ tailWord_3481095).sum := by decide
  have hdescent : baseEnd_3481095 < baseStart_3481095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481112 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_3481112 : Nat := 118140960795 + 3481112 * 2 ^ 59
def prefixEnd_3481112 : Nat := 4983230072969 + 3 ^ 40 * 3481112 * 2
def baseEnd_3481112 : Nat := 1191655778756192911327109

theorem tailTrace_3481112 : CollatzResearch.WordTrace tailWord_3481112 prefixEnd_3481112 1191655778756192911327109 := by
  unfold tailWord_3481112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63483292682266612721014795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84644390243022150294686393 63483292682266612721014795)
  ·
    refine ⟨95224939023399919081522193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63483292682266612721014795 95224939023399919081522193)
    ·
      refine ⟨71418704267549939311141645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95224939023399919081522193 71418704267549939311141645)
      ·
        refine ⟨26782014100331227241678117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71418704267549939311141645 26782014100331227241678117)
        ·
          refine ⟨5021627643812105107814647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26782014100331227241678117 5021627643812105107814647)
          ·
            refine ⟨7532441465718157661721971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021627643812105107814647 7532441465718157661721971)
            ·
              refine ⟨11298662198577236492582957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7532441465718157661721971 11298662198577236492582957)
              ·
                refine ⟨4236998324466463684718609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11298662198577236492582957 4236998324466463684718609)
                ·
                  refine ⟨3177748743349847763538957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236998324466463684718609 3177748743349847763538957)
                  ·
                    refine ⟨1191655778756192911327109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177748743349847763538957 1191655778756192911327109)
                    ·
                      rfl

theorem cell22_3481112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_3481112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481112 prefixEnd_3481112 := by exact prefixLift 3481112
  have htrace : WordTrace (prefixWord ++ tailWord_3481112) baseStart_3481112 baseEnd_3481112 := by
    simpa [prefixWord, tailWord_3481112, baseEnd_3481112] using wordTrace_append hprefix tailTrace_3481112
  have hstable : (prefixWord ++ tailWord_3481112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481112).length < 2 ^ (prefixWord ++ tailWord_3481112).sum := by decide
  have hdescent : baseEnd_3481112 < baseStart_3481112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481157 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_3481157 : Nat := 118140960795 + 3481157 * 2 ^ 59
def prefixEnd_3481157 : Nat := 4983230072969 + 3 ^ 40 * 3481157 * 2
def baseEnd_3481157 : Nat := 1191671183175827793951971

theorem tailTrace_3481157 : CollatzResearch.WordTrace tailWord_3481157 prefixEnd_3481157 1191671183175827793951971 := by
  unfold tailWord_3481157
  simp only [CollatzResearch.WordTrace]
  refine ⟨126968226649370198127417725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84645484432913465418278483 126968226649370198127417725)
  ·
    refine ⟨47613084993513824297781647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126968226649370198127417725 47613084993513824297781647)
    ·
      refine ⟨71419627490270736446672471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47613084993513824297781647 71419627490270736446672471)
      ·
        refine ⟨107129441235406104670008707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71419627490270736446672471 107129441235406104670008707)
        ·
          refine ⟨160694161853109157005013061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107129441235406104670008707 160694161853109157005013061)
          ·
            refine ⟨30130155347457966938439949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160694161853109157005013061 30130155347457966938439949)
            ·
              refine ⟨11298808255296737601914981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30130155347457966938439949 11298808255296737601914981)
              ·
                refine ⟨2118526547868138300359059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11298808255296737601914981 2118526547868138300359059)
                ·
                  refine ⟨3177789821802207450538589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118526547868138300359059 3177789821802207450538589)
                  ·
                    refine ⟨1191671183175827793951971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3177789821802207450538589 1191671183175827793951971)
                    ·
                      rfl

theorem cell22_3481157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_3481157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481157 prefixEnd_3481157 := by exact prefixLift 3481157
  have htrace : WordTrace (prefixWord ++ tailWord_3481157) baseStart_3481157 baseEnd_3481157 := by
    simpa [prefixWord, tailWord_3481157, baseEnd_3481157] using wordTrace_append hprefix tailTrace_3481157
  have hstable : (prefixWord ++ tailWord_3481157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481157).length < 2 ^ (prefixWord ++ tailWord_3481157).sum := by decide
  have hdescent : baseEnd_3481157 < baseStart_3481157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481168 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_3481168 : Nat := 118140960795 + 3481168 * 2 ^ 59
def prefixEnd_3481168 : Nat := 4983230072969 + 3 ^ 40 * 3481168 * 2
def baseEnd_3481168 : Nat := 1191674948700627431926937

theorem tailTrace_3481168 : CollatzResearch.WordTrace tailWord_3481168 prefixEnd_3481168 1191674948700627431926937 := by
  unfold tailWord_3481168
  simp only [CollatzResearch.WordTrace]
  refine ⟨63484313926165173503034079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84645751901553564670712105 63484313926165173503034079)
  ·
    refine ⟨95226470889247760254551119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63484313926165173503034079 95226470889247760254551119)
    ·
      refine ⟨142839706333871640381826679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95226470889247760254551119 142839706333871640381826679)
      ·
        refine ⟨214259559500807460572740019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142839706333871640381826679 214259559500807460572740019)
        ·
          refine ⟨321389339251211190859110029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214259559500807460572740019 321389339251211190859110029)
          ·
            refine ⟨120521002219204196572166261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321389339251211190859110029 120521002219204196572166261)
            ·
              refine ⟨11298843958050393428640587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120521002219204196572166261 11298843958050393428640587)
              ·
                refine ⟨16948265937075590142960881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11298843958050393428640587 16948265937075590142960881)
                ·
                  refine ⟨12711199452806692607220661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16948265937075590142960881 12711199452806692607220661)
                  ·
                    refine ⟨1191674948700627431926937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12711199452806692607220661 1191674948700627431926937)
                    ·
                      rfl

theorem cell22_3481168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_3481168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481168 prefixEnd_3481168 := by exact prefixLift 3481168
  have htrace : WordTrace (prefixWord ++ tailWord_3481168) baseStart_3481168 baseEnd_3481168 := by
    simpa [prefixWord, tailWord_3481168, baseEnd_3481168] using wordTrace_append hprefix tailTrace_3481168
  have hstable : (prefixWord ++ tailWord_3481168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481168).length < 2 ^ (prefixWord ++ tailWord_3481168).sum := by decide
  have hdescent : baseEnd_3481168 < baseStart_3481168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481170 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3481170 : Nat := 118140960795 + 3481170 * 2 ^ 59
def prefixEnd_3481170 : Nat := 4983230072969 + 3 ^ 40 * 3481170 * 2
def baseEnd_3481170 : Nat := 397225211113833364458977

theorem tailTrace_3481170 : CollatzResearch.WordTrace tailWord_3481170 prefixEnd_3481170 397225211113833364458977 := by
  unfold tailWord_3481170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742175199580775336910241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84645800532215400898427309 31742175199580775336910241)
  ·
    refine ⟨23806631399685581502682681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31742175199580775336910241 23806631399685581502682681)
    ·
      refine ⟨17854973549764186127012011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23806631399685581502682681 17854973549764186127012011)
      ·
        refine ⟨26782460324646279190518017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17854973549764186127012011 26782460324646279190518017)
        ·
          refine ⟨20086845243484709392888513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26782460324646279190518017 20086845243484709392888513)
          ·
            refine ⟨15065133932613532044666385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20086845243484709392888513 15065133932613532044666385)
            ·
              refine ⟨11298850449460149033499789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15065133932613532044666385 11298850449460149033499789)
              ·
                refine ⟨4237068918547555887562421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11298850449460149033499789 4237068918547555887562421)
                ·
                  refine ⟨397225211113833364458977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237068918547555887562421 397225211113833364458977)
                  ·
                    rfl

theorem cell22_3481170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3481170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481170 prefixEnd_3481170 := by exact prefixLift 3481170
  have htrace : WordTrace (prefixWord ++ tailWord_3481170) baseStart_3481170 baseEnd_3481170 := by
    simpa [prefixWord, tailWord_3481170, baseEnd_3481170] using wordTrace_append hprefix tailTrace_3481170
  have hstable : (prefixWord ++ tailWord_3481170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481170).length < 2 ^ (prefixWord ++ tailWord_3481170).sum := by decide
  have hdescent : baseEnd_3481170 < baseStart_3481170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481228 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3481228 : Nat := 118140960795 + 3481228 * 2 ^ 59
def prefixEnd_3481228 : Nat := 4983230072969 + 3 ^ 40 * 3481228 * 2
def baseEnd_3481228 : Nat := 1191695487926807275426753

theorem tailTrace_3481228 : CollatzResearch.WordTrace tailWord_3481228 prefixEnd_3481228 1191695487926807275426753 := by
  unfold tailWord_3481228
  simp only [CollatzResearch.WordTrace]
  refine ⟨63485408116056488626626169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84647210821408651502168225 63485408116056488626626169)
  ·
    refine ⟨47614056087042366469969627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63485408116056488626626169 47614056087042366469969627)
    ·
      refine ⟨71421084130563549704954441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47614056087042366469969627 71421084130563549704954441)
      ·
        refine ⟨53565813097922662278715831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71421084130563549704954441 53565813097922662278715831)
        ·
          refine ⟨80348719646883993418073747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53565813097922662278715831 80348719646883993418073747)
          ·
            refine ⟨120523079470325990127110621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80348719646883993418073747 120523079470325990127110621)
            ·
              refine ⟨45196154801372246297666483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120523079470325990127110621 45196154801372246297666483)
              ·
                refine ⟨67794232202058369446499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45196154801372246297666483 67794232202058369446499725)
                ·
                  refine ⟨25422837075771888542437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67794232202058369446499725 25422837075771888542437397)
                  ·
                    refine ⟨1191695487926807275426753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25422837075771888542437397 1191695487926807275426753)
                    ·
                      rfl

theorem cell22_3481228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3481228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481228 prefixEnd_3481228 := by exact prefixLift 3481228
  have htrace : WordTrace (prefixWord ++ tailWord_3481228) baseStart_3481228 baseEnd_3481228 := by
    simpa [prefixWord, tailWord_3481228, baseEnd_3481228] using wordTrace_append hprefix tailTrace_3481228
  have hstable : (prefixWord ++ tailWord_3481228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481228).length < 2 ^ (prefixWord ++ tailWord_3481228).sum := by decide
  have hdescent : baseEnd_3481228 < baseStart_3481228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481234 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3481234 : Nat := 118140960795 + 3481234 * 2 ^ 59
def prefixEnd_3481234 : Nat := 4983230072969 + 3 ^ 40 * 3481234 * 2
def baseEnd_3481234 : Nat := 1191697541849425259776735

theorem tailTrace_3481234 : CollatzResearch.WordTrace tailWord_3481234 prefixEnd_3481234 1191697541849425259776735 := by
  unfold tailWord_3481234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742758767522810069492689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84647356713394160185313837 31742758767522810069492689)
  ·
    refine ⟨23807069075642107552119517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31742758767522810069492689 23807069075642107552119517)
    ·
      refine ⟨8927650903365790332044819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23807069075642107552119517 8927650903365790332044819)
      ·
        refine ⟨13391476355048685498067229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927650903365790332044819 13391476355048685498067229)
        ·
          refine ⟨5021803633143257061775211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13391476355048685498067229 5021803633143257061775211)
          ·
            refine ⟨7532705449714885592662817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021803633143257061775211 7532705449714885592662817)
            ·
              refine ⟨5649529087286164194497113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532705449714885592662817 5649529087286164194497113)
              ·
                refine ⟨4237146815464623145872835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5649529087286164194497113 4237146815464623145872835)
                ·
                  refine ⟨6355720223196934718809253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237146815464623145872835 6355720223196934718809253)
                  ·
                    refine ⟨1191697541849425259776735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355720223196934718809253 1191697541849425259776735)
                    ·
                      rfl

theorem cell22_3481234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3481234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481234 prefixEnd_3481234 := by exact prefixLift 3481234
  have htrace : WordTrace (prefixWord ++ tailWord_3481234) baseStart_3481234 baseEnd_3481234 := by
    simpa [prefixWord, tailWord_3481234, baseEnd_3481234] using wordTrace_append hprefix tailTrace_3481234
  have hstable : (prefixWord ++ tailWord_3481234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481234).length < 2 ^ (prefixWord ++ tailWord_3481234).sum := by decide
  have hdescent : baseEnd_3481234 < baseStart_3481234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481245 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3481245 : Nat := 118140960795 + 3481245 * 2 ^ 59
def prefixEnd_3481245 : Nat := 4983230072969 + 3 ^ 40 * 3481245 * 2
def baseEnd_3481245 : Nat := 1191701307374224897751701

theorem tailTrace_3481245 : CollatzResearch.WordTrace tailWord_3481245 prefixEnd_3481245 1191701307374224897751701 := by
  unfold tailWord_3481245
  simp only [CollatzResearch.WordTrace]
  refine ⟨126971436273051389156621189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84647624182034259437747459 126971436273051389156621189)
  ·
    refine ⟨23807144301197135466866473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126971436273051389156621189 23807144301197135466866473)
    ·
      refine ⟨17855358225897851600149855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23807144301197135466866473 17855358225897851600149855)
      ·
        refine ⟨26783037338846777400224783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17855358225897851600149855 26783037338846777400224783)
        ·
          refine ⟨40174556008270166100337175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26783037338846777400224783 40174556008270166100337175)
          ·
            refine ⟨60261834012405249150505763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40174556008270166100337175 60261834012405249150505763)
            ·
              refine ⟨90392751018607873725758645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60261834012405249150505763 90392751018607873725758645)
              ·
                refine ⟨8474320407994488161789873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90392751018607873725758645 8474320407994488161789873)
                ·
                  refine ⟨6355740305995866121342405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8474320407994488161789873 6355740305995866121342405)
                  ·
                    refine ⟨1191701307374224897751701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355740305995866121342405 1191701307374224897751701)
                    ·
                      rfl

theorem cell22_3481245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3481245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481245 prefixEnd_3481245 := by exact prefixLift 3481245
  have htrace : WordTrace (prefixWord ++ tailWord_3481245) baseStart_3481245 baseEnd_3481245 := by
    simpa [prefixWord, tailWord_3481245, baseEnd_3481245] using wordTrace_append hprefix tailTrace_3481245
  have hstable : (prefixWord ++ tailWord_3481245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481245).length < 2 ^ (prefixWord ++ tailWord_3481245).sum := by decide
  have hdescent : baseEnd_3481245 < baseStart_3481245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481249 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 4]
def baseStart_3481249 : Nat := 118140960795 + 3481249 * 2 ^ 59
def prefixEnd_3481249 : Nat := 4983230072969 + 3 ^ 40 * 3481249 * 2
def baseEnd_3481249 : Nat := 397234225551990073550563

theorem tailTrace_3481249 : CollatzResearch.WordTrace tailWord_3481249 prefixEnd_3481249 397234225551990073550563 := by
  unfold tailWord_3481249
  simp only [CollatzResearch.WordTrace]
  refine ⟨126971582165036897839766801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84647721443357931893177867 126971582165036897839766801)
  ·
    refine ⟨95228686623777673379825101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126971582165036897839766801 95228686623777673379825101)
    ·
      refine ⟨35710757483916627517434413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95228686623777673379825101 35710757483916627517434413)
      ·
        refine ⟨13391534056468735319037905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35710757483916627517434413 13391534056468735319037905)
        ·
          refine ⟨10043650542351551489278429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13391534056468735319037905 10043650542351551489278429)
          ·
            refine ⟨3766368953381831808479411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10043650542351551489278429 3766368953381831808479411)
            ·
              refine ⟨5649553430072747712719117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766368953381831808479411 5649553430072747712719117)
              ·
                refine ⟨2118582536277280392269669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5649553430072747712719117 2118582536277280392269669)
                ·
                  refine ⟨397234225551990073550563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118582536277280392269669 397234225551990073550563)
                  ·
                    rfl

theorem cell22_3481249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_3481249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481249 prefixEnd_3481249 := by exact prefixLift 3481249
  have htrace : WordTrace (prefixWord ++ tailWord_3481249) baseStart_3481249 baseEnd_3481249 := by
    simpa [prefixWord, tailWord_3481249, baseEnd_3481249] using wordTrace_append hprefix tailTrace_3481249
  have hstable : (prefixWord ++ tailWord_3481249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481249).length < 2 ^ (prefixWord ++ tailWord_3481249).sum := by decide
  have hdescent : baseEnd_3481249 < baseStart_3481249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481335 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3481335 : Nat := 118140960795 + 3481335 * 2 ^ 59
def prefixEnd_3481335 : Nat := 4983230072969 + 3 ^ 40 * 3481335 * 2
def baseEnd_3481335 : Nat := 1191732116213494663001425

theorem tailTrace_3481335 : CollatzResearch.WordTrace tailWord_3481335 prefixEnd_3481335 1191732116213494663001425 := by
  unfold tailWord_3481335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126974718842725334527397459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84649812561816889684931639 126974718842725334527397459)
  ·
    refine ⟨190462078264088001791096189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126974718842725334527397459 190462078264088001791096189)
    ·
      refine ⟨71423279349033000671661071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190462078264088001791096189 71423279349033000671661071)
      ·
        refine ⟨107134919023549501007491607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71423279349033000671661071 107134919023549501007491607)
        ·
          refine ⟨160702378535324251511237411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107134919023549501007491607 160702378535324251511237411)
          ·
            refine ⟨241053567802986377266856117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160702378535324251511237411 241053567802986377266856117)
            ·
              refine ⟨22598771981529972868767761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241053567802986377266856117 22598771981529972868767761)
              ·
                refine ⟨16949078986147479651575821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22598771981529972868767761 16949078986147479651575821)
                ·
                  refine ⟨6355904619805304869340933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16949078986147479651575821 6355904619805304869340933)
                  ·
                    refine ⟨1191732116213494663001425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355904619805304869340933 1191732116213494663001425)
                    ·
                      rfl

theorem cell22_3481335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3481335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481335 prefixEnd_3481335 := by exact prefixLift 3481335
  have htrace : WordTrace (prefixWord ++ tailWord_3481335) baseStart_3481335 baseEnd_3481335 := by
    simpa [prefixWord, tailWord_3481335, baseEnd_3481335] using wordTrace_append hprefix tailTrace_3481335
  have hstable : (prefixWord ++ tailWord_3481335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481335).length < 2 ^ (prefixWord ++ tailWord_3481335).sum := by decide
  have hdescent : baseEnd_3481335 < baseStart_3481335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481352 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3481352 : Nat := 118140960795 + 3481352 * 2 ^ 59
def prefixEnd_3481352 : Nat := 4983230072969 + 3 ^ 40 * 3481352 * 2
def baseEnd_3481352 : Nat := 1191737935660912285326373

theorem tailTrace_3481352 : CollatzResearch.WordTrace tailWord_3481352 prefixEnd_3481352 1191737935660912285326373 := by
  unfold tailWord_3481352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487669441831873215383155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84650225922442497620510873 63487669441831873215383155)
  ·
    refine ⟨95231504162747809823074733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63487669441831873215383155 95231504162747809823074733)
    ·
      refine ⟨35711814061030428683653025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95231504162747809823074733 35711814061030428683653025)
      ·
        refine ⟨26783860545772821512739769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35711814061030428683653025 26783860545772821512739769)
        ·
          refine ⟨20087895409329616134554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26783860545772821512739769 20087895409329616134554827)
          ·
            refine ⟨30131843113994424201832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20087895409329616134554827 30131843113994424201832241)
            ·
              refine ⟨22598882335495818151374181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30131843113994424201832241 22598882335495818151374181)
              ·
                refine ⟨4237290437905465903382659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22598882335495818151374181 4237290437905465903382659)
                ·
                  refine ⟨6355935656858198855073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4237290437905465903382659 6355935656858198855073989)
                  ·
                    refine ⟨1191737935660912285326373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6355935656858198855073989 1191737935660912285326373)
                    ·
                      rfl

theorem cell22_3481352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3481352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481352 prefixEnd_3481352 := by exact prefixLift 3481352
  have htrace : WordTrace (prefixWord ++ tailWord_3481352) baseStart_3481352 baseEnd_3481352 := by
    simpa [prefixWord, tailWord_3481352, baseEnd_3481352] using wordTrace_append hprefix tailTrace_3481352
  have hstable : (prefixWord ++ tailWord_3481352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481352).length < 2 ^ (prefixWord ++ tailWord_3481352).sum := by decide
  have hdescent : baseEnd_3481352 < baseStart_3481352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481384 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_3481384 : Nat := 118140960795 + 3481384 * 2 ^ 59
def prefixEnd_3481384 : Nat := 4983230072969 + 3 ^ 40 * 3481384 * 2
def baseEnd_3481384 : Nat := 397249629971624956175425

theorem tailTrace_3481384 : CollatzResearch.WordTrace tailWord_3481384 prefixEnd_3481384 397249629971624956175425 := by
  unfold tailWord_3481384
  simp only [CollatzResearch.WordTrace]
  refine ⟨63488253009773907947965603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84651004013031877263954137 63488253009773907947965603)
  ·
    refine ⟨95232379514660861921948405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63488253009773907947965603 95232379514660861921948405)
    ·
      refine ⟨8928035579499455805182663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95232379514660861921948405 8928035579499455805182663)
      ·
        refine ⟨13392053369249183707773995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928035579499455805182663 13392053369249183707773995)
        ·
          refine ⟨20088080053873775561660993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13392053369249183707773995 20088080053873775561660993)
          ·
            refine ⟨15066060040405331671245745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20088080053873775561660993 15066060040405331671245745)
            ·
              refine ⟨11299545030303998753434309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066060040405331671245745 11299545030303998753434309)
              ·
                refine ⟨2118664693181999766268933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11299545030303998753434309 2118664693181999766268933)
                ·
                  refine ⟨397249629971624956175425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118664693181999766268933 397249629971624956175425)
                  ·
                    rfl

theorem cell22_3481384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_3481384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481384 prefixEnd_3481384 := by exact prefixLift 3481384
  have htrace : WordTrace (prefixWord ++ tailWord_3481384) baseStart_3481384 baseEnd_3481384 := by
    simpa [prefixWord, tailWord_3481384, baseEnd_3481384] using wordTrace_append hprefix tailTrace_3481384
  have hstable : (prefixWord ++ tailWord_3481384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481384).length < 2 ^ (prefixWord ++ tailWord_3481384).sum := by decide
  have hdescent : baseEnd_3481384 < baseStart_3481384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481450 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3481450 : Nat := 118140960795 + 3481450 * 2 ^ 59
def prefixEnd_3481450 : Nat := 4983230072969 + 3 ^ 40 * 3481450 * 2
def baseEnd_3481450 : Nat := 1191771483063672696376073

theorem tailTrace_3481450 : CollatzResearch.WordTrace tailWord_3481450 prefixEnd_3481450 1191771483063672696376073 := by
  unfold tailWord_3481450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744728309327177291958451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84652608824872472778555869 31744728309327177291958451)
  ·
    refine ⟨47617092463990765937937677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31744728309327177291958451 47617092463990765937937677)
    ·
      refine ⟨17856409673996537226726629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47617092463990765937937677 17856409673996537226726629)
      ·
        refine ⟨3348076813874350730011243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17856409673996537226726629 3348076813874350730011243)
        ·
          refine ⟨5022115220811526095016865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348076813874350730011243 5022115220811526095016865)
          ·
            refine ⟨3766586415608644571262649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022115220811526095016865 3766586415608644571262649)
            ·
              refine ⟨2824939811706483428446987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766586415608644571262649 2824939811706483428446987)
              ·
                refine ⟨4237409717559725142670481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824939811706483428446987 4237409717559725142670481)
                ·
                  refine ⟨3178057288169793857002861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237409717559725142670481 3178057288169793857002861)
                  ·
                    refine ⟨1191771483063672696376073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178057288169793857002861 1191771483063672696376073)
                    ·
                      rfl

theorem cell22_3481450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3481450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481450 prefixEnd_3481450 := by exact prefixLift 3481450
  have htrace : WordTrace (prefixWord ++ tailWord_3481450) baseStart_3481450 baseEnd_3481450 := by
    simpa [prefixWord, tailWord_3481450, baseEnd_3481450] using wordTrace_append hprefix tailTrace_3481450
  have hstable : (prefixWord ++ tailWord_3481450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481450).length < 2 ^ (prefixWord ++ tailWord_3481450).sum := by decide
  have hdescent : baseEnd_3481450 < baseStart_3481450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481457 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 5]
def baseStart_3481457 : Nat := 118140960795 + 3481457 * 2 ^ 59
def prefixEnd_3481457 : Nat := 4983230072969 + 3 ^ 40 * 3481457 * 2
def baseEnd_3481457 : Nat := 397257959768909003817017

theorem tailTrace_3481457 : CollatzResearch.WordTrace tailWord_3481457 prefixEnd_3481457 397257959768909003817017 := by
  unfold tailWord_3481457
  simp only [CollatzResearch.WordTrace]
  refine ⟨126979168548283349363338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84652779032188899575559083 126979168548283349363338625)
  ·
    refine ⟨95234376411212512022503969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126979168548283349363338625 95234376411212512022503969)
    ·
      refine ⟨71425782308409384016877977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95234376411212512022503969 71425782308409384016877977)
      ·
        refine ⟨53569336731307038012658483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71425782308409384016877977 53569336731307038012658483)
        ·
          refine ⟨80354005096960557018987725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53569336731307038012658483 80354005096960557018987725)
          ·
            refine ⟨30132751911360208882120397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80354005096960557018987725 30132751911360208882120397)
            ·
              refine ⟨11299781966760078330795149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30132751911360208882120397 11299781966760078330795149)
              ·
                refine ⟨4237418237535029374048181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11299781966760078330795149 4237418237535029374048181)
                ·
                  refine ⟨397257959768909003817017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237418237535029374048181 397257959768909003817017)
                  ·
                    rfl

theorem cell22_3481457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_3481457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481457 prefixEnd_3481457 := by exact prefixLift 3481457
  have htrace : WordTrace (prefixWord ++ tailWord_3481457) baseStart_3481457 baseEnd_3481457 := by
    simpa [prefixWord, tailWord_3481457, baseEnd_3481457] using wordTrace_append hprefix tailTrace_3481457
  have hstable : (prefixWord ++ tailWord_3481457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481457).length < 2 ^ (prefixWord ++ tailWord_3481457).sum := by decide
  have hdescent : baseEnd_3481457 < baseStart_3481457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481534 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3481534 : Nat := 118140960795 + 3481534 * 2 ^ 59
def prefixEnd_3481534 : Nat := 4983230072969 + 3 ^ 40 * 3481534 * 2
def baseEnd_3481534 : Nat := 1191800237980324477275815

theorem tailTrace_3481534 : CollatzResearch.WordTrace tailWord_3481534 prefixEnd_3481534 1191800237980324477275815 := by
  unfold tailWord_3481534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872747121125548939236457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84654651312669594342594437 15872747121125548939236457)
  ·
    refine ⟨11904560340844161704427343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15872747121125548939236457 11904560340844161704427343)
    ·
      refine ⟨17856840511266242556641015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904560340844161704427343 17856840511266242556641015)
      ·
        refine ⟨26785260766899363834961523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17856840511266242556641015 26785260766899363834961523)
        ·
          refine ⟨40177891150349045752442285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785260766899363834961523 40177891150349045752442285)
          ·
            refine ⟨15066709181380892157165857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40177891150349045752442285 15066709181380892157165857)
            ·
              refine ⟨11300031886035669117874393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15066709181380892157165857 11300031886035669117874393)
              ·
                refine ⟨8475023914526751838405795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11300031886035669117874393 8475023914526751838405795)
                ·
                  refine ⟨12712535871790127757608693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8475023914526751838405795 12712535871790127757608693)
                  ·
                    refine ⟨1191800237980324477275815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12712535871790127757608693 1191800237980324477275815)
                    ·
                      rfl

theorem cell22_3481534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3481534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481534 prefixEnd_3481534 := by exact prefixLift 3481534
  have htrace : WordTrace (prefixWord ++ tailWord_3481534) baseStart_3481534 baseEnd_3481534 := by
    simpa [prefixWord, tailWord_3481534, baseEnd_3481534] using wordTrace_append hprefix tailTrace_3481534
  have hstable : (prefixWord ++ tailWord_3481534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481534).length < 2 ^ (prefixWord ++ tailWord_3481534).sum := by decide
  have hdescent : baseEnd_3481534 < baseStart_3481534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481581 : List Nat := [1, 5, 1, 4, 1, 1, 1, 8]
def baseStart_3481581 : Nat := 118140960795 + 3481581 * 2 ^ 59
def prefixEnd_3481581 : Nat := 4983230072969 + 3 ^ 40 * 3481581 * 2
def baseEnd_3481581 : Nat := 132424036337870224594519

theorem tailTrace_3481581 : CollatzResearch.WordTrace tailWord_3481581 prefixEnd_3481581 132424036337870224594519 := by
  unfold tailWord_3481581
  simp only [CollatzResearch.WordTrace]
  refine ⟨126983691199834118540852597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84655794133222745693901731 126983691199834118540852597)
  ·
    refine ⟨11904721049984448613204931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126983691199834118540852597 11904721049984448613204931)
    ·
      refine ⟨17857081574976672919807397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904721049984448613204931 17857081574976672919807397)
      ·
        refine ⟨3348202795308126172463887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17857081574976672919807397 3348202795308126172463887)
        ·
          refine ⟨5022304192962189258695831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348202795308126172463887 5022304192962189258695831)
          ·
            refine ⟨7533456289443283888043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022304192962189258695831 7533456289443283888043747)
            ·
              refine ⟨11300184434164925832065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533456289443283888043747 11300184434164925832065621)
              ·
                refine ⟨132424036337870224594519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11300184434164925832065621 132424036337870224594519)
                ·
                  rfl

theorem cell22_3481581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 8].length) (baseStart_3481581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481581 prefixEnd_3481581 := by exact prefixLift 3481581
  have htrace : WordTrace (prefixWord ++ tailWord_3481581) baseStart_3481581 baseEnd_3481581 := by
    simpa [prefixWord, tailWord_3481581, baseEnd_3481581] using wordTrace_append hprefix tailTrace_3481581
  have hstable : (prefixWord ++ tailWord_3481581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481581).length < 2 ^ (prefixWord ++ tailWord_3481581).sum := by decide
  have hdescent : baseEnd_3481581 < baseStart_3481581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481592 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_3481592 : Nat := 118140960795 + 3481592 * 2 ^ 59
def prefixEnd_3481592 : Nat := 4983230072969 + 3 ^ 40 * 3481592 * 2
def baseEnd_3481592 : Nat := 397273364188543886441879

theorem tailTrace_3481592 : CollatzResearch.WordTrace tailWord_3481592 prefixEnd_3481592 397273364188543886441879 := by
  unfold tailWord_3481592
  simp only [CollatzResearch.WordTrace]
  refine ⟨63492046201397133709751515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84656061601862844946335353 63492046201397133709751515)
  ·
    refine ⟨95238069302095700564627273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63492046201397133709751515 95238069302095700564627273)
    ·
      refine ⟨71428551976571775423470455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95238069302095700564627273 71428551976571775423470455)
      ·
        refine ⟨107142827964857663135205683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71428551976571775423470455 107142827964857663135205683)
        ·
          refine ⟨160714241947286494702808525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107142827964857663135205683 160714241947286494702808525)
          ·
            refine ⟨60267840730232435513553197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160714241947286494702808525 60267840730232435513553197)
            ·
              refine ⟨22600440273837163317582449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60267840730232435513553197 22600440273837163317582449)
              ·
                refine ⟨16950330205377872488186837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22600440273837163317582449 16950330205377872488186837)
                ·
                  refine ⟨397273364188543886441879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16950330205377872488186837 397273364188543886441879)
                  ·
                    rfl

theorem cell22_3481592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_3481592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481592 prefixEnd_3481592 := by exact prefixLift 3481592
  have htrace : WordTrace (prefixWord ++ tailWord_3481592) baseStart_3481592 baseEnd_3481592 := by
    simpa [prefixWord, tailWord_3481592, baseEnd_3481592] using wordTrace_append hprefix tailTrace_3481592
  have hstable : (prefixWord ++ tailWord_3481592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481592).length < 2 ^ (prefixWord ++ tailWord_3481592).sum := by decide
  have hdescent : baseEnd_3481592 < baseStart_3481592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481626 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_3481626 : Nat := 118140960795 + 3481626 * 2 ^ 59
def prefixEnd_3481626 : Nat := 4983230072969 + 3 ^ 40 * 3481626 * 2
def baseEnd_3481626 : Nat := 397277243820155634658511

theorem tailTrace_3481626 : CollatzResearch.WordTrace tailWord_3481626 prefixEnd_3481626 397277243820155634658511 := by
  unfold tailWord_3481626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746333121167772806560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84656888323114060817493821 31746333121167772806560183)
  ·
    refine ⟨47619499681751659209840275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31746333121167772806560183 47619499681751659209840275)
    ·
      refine ⟨71429249522627488814760413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47619499681751659209840275 71429249522627488814760413)
      ·
        refine ⟨26785968570985308305535155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71429249522627488814760413 26785968570985308305535155)
        ·
          refine ⟨40178952856477962458302733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785968570985308305535155 40178952856477962458302733)
          ·
            refine ⟨15067107321179235921863525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40178952856477962458302733 15067107321179235921863525)
            ·
              refine ⟨2825082622721106735349411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15067107321179235921863525 2825082622721106735349411)
              ·
                refine ⟨4237623934081660103024117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825082622721106735349411 4237623934081660103024117)
                ·
                  refine ⟨397277243820155634658511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237623934081660103024117 397277243820155634658511)
                  ·
                    rfl

theorem cell22_3481626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_3481626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481626 prefixEnd_3481626 := by exact prefixLift 3481626
  have htrace : WordTrace (prefixWord ++ tailWord_3481626) baseStart_3481626 baseEnd_3481626 := by
    simpa [prefixWord, tailWord_3481626, baseEnd_3481626] using wordTrace_append hprefix tailTrace_3481626
  have hstable : (prefixWord ++ tailWord_3481626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481626).length < 2 ^ (prefixWord ++ tailWord_3481626).sum := by decide
  have hdescent : baseEnd_3481626 < baseStart_3481626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481671 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 4]
def baseStart_3481671 : Nat := 118140960795 + 3481671 * 2 ^ 59
def prefixEnd_3481671 : Nat := 4983230072969 + 3 ^ 40 * 3481671 * 2
def baseEnd_3481671 : Nat := 397282378626700595533465

theorem tailTrace_3481671 : CollatzResearch.WordTrace tailWord_3481671 prefixEnd_3481671 397282378626700595533465 := by
  unfold tailWord_3481671
  simp only [CollatzResearch.WordTrace]
  refine ⟨126986973769508063911628867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84657982513005375941085911 126986973769508063911628867)
  ·
    refine ⟨190480460654262095867443301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126986973769508063911628867 190480460654262095867443301)
    ·
      refine ⟨35715086372674142975145619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190480460654262095867443301 35715086372674142975145619)
      ·
        refine ⟨53572629559011214462718429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35715086372674142975145619 53572629559011214462718429)
        ·
          refine ⟨20089736084629205423519411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53572629559011214462718429 20089736084629205423519411)
          ·
            refine ⟨30134604126943808135279117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20089736084629205423519411 30134604126943808135279117)
            ·
              refine ⟨11300476547603928050729669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30134604126943808135279117 11300476547603928050729669)
              ·
                refine ⟨2118839352675736509511813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11300476547603928050729669 2118839352675736509511813)
                ·
                  refine ⟨397282378626700595533465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118839352675736509511813 397282378626700595533465)
                  ·
                    rfl

theorem cell22_3481671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 4].length) (baseStart_3481671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481671 prefixEnd_3481671 := by exact prefixLift 3481671
  have htrace : WordTrace (prefixWord ++ tailWord_3481671) baseStart_3481671 baseEnd_3481671 := by
    simpa [prefixWord, tailWord_3481671, baseEnd_3481671] using wordTrace_append hprefix tailTrace_3481671
  have hstable : (prefixWord ++ tailWord_3481671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481671).length < 2 ^ (prefixWord ++ tailWord_3481671).sum := by decide
  have hdescent : baseEnd_3481671 < baseStart_3481671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481684 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3481684 : Nat := 118140960795 + 3481684 * 2 ^ 59
def prefixEnd_3481684 : Nat := 4983230072969 + 3 ^ 40 * 3481684 * 2
def baseEnd_3481684 : Nat := 1191851586045774086025355

theorem tailTrace_3481684 : CollatzResearch.WordTrace tailWord_3481684 prefixEnd_3481684 1191851586045774086025355 := by
  unfold tailWord_3481684
  simp only [CollatzResearch.WordTrace]
  refine ⟨63493723959230483565926053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84658298612307311421234737 63493723959230483565926053)
  ·
    refine ⟨11905073242355715668611135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63493723959230483565926053 11905073242355715668611135)
    ·
      refine ⟨17857609863533573502916703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11905073242355715668611135 17857609863533573502916703)
      ·
        refine ⟨26786414795300360254375055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17857609863533573502916703 26786414795300360254375055)
        ·
          refine ⟨40179622192950540381562583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26786414795300360254375055 40179622192950540381562583)
          ·
            refine ⟨60269433289425810572343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40179622192950540381562583 60269433289425810572343875)
            ·
              refine ⟨90404149934138715858515813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60269433289425810572343875 90404149934138715858515813)
              ·
                refine ⟨16950778112651009223471715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90404149934138715858515813 16950778112651009223471715)
                ·
                  refine ⟨25426167168976513835207573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16950778112651009223471715 25426167168976513835207573)
                  ·
                    refine ⟨1191851586045774086025355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25426167168976513835207573 1191851586045774086025355)
                    ·
                      rfl

theorem cell22_3481684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3481684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481684 prefixEnd_3481684 := by exact prefixLift 3481684
  have htrace : WordTrace (prefixWord ++ tailWord_3481684) baseStart_3481684 baseEnd_3481684 := by
    simpa [prefixWord, tailWord_3481684, baseEnd_3481684] using wordTrace_append hprefix tailTrace_3481684
  have hstable : (prefixWord ++ tailWord_3481684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481684).length < 2 ^ (prefixWord ++ tailWord_3481684).sum := by decide
  have hdescent : baseEnd_3481684 < baseStart_3481684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481701 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3481701 : Nat := 118140960795 + 3481701 * 2 ^ 59
def prefixEnd_3481701 : Nat := 4983230072969 + 3 ^ 40 * 3481701 * 2
def baseEnd_3481701 : Nat := 1191857405493191708350303

theorem tailTrace_3481701 : CollatzResearch.WordTrace tailWord_3481701 prefixEnd_3481701 1191857405493191708350303 := by
  unfold tailWord_3481701
  simp only [CollatzResearch.WordTrace]
  refine ⟨126988067959399379035220957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84658711972932919356813971 126988067959399379035220957)
  ·
    refine ⟨47620525484774767138207859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126988067959399379035220957 47620525484774767138207859)
    ·
      refine ⟨71430788227162150707311789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47620525484774767138207859 71430788227162150707311789)
      ·
        refine ⟨26786545585185806515241921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71430788227162150707311789 26786545585185806515241921)
        ·
          refine ⟨20089909188889354886431441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26786545585185806515241921 20089909188889354886431441)
          ·
            refine ⟨15067431891667016164823581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20089909188889354886431441 15067431891667016164823581)
            ·
              refine ⟨5650286959375131061808843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15067431891667016164823581 5650286959375131061808843)
              ·
                refine ⟨8475430439062696592713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650286959375131061808843 8475430439062696592713265)
                ·
                  refine ⟨6356572829297022444534949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8475430439062696592713265 6356572829297022444534949)
                  ·
                    refine ⟨1191857405493191708350303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356572829297022444534949 1191857405493191708350303)
                    ·
                      rfl

theorem cell22_3481701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3481701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481701 prefixEnd_3481701 := by exact prefixLift 3481701
  have htrace : WordTrace (prefixWord ++ tailWord_3481701) baseStart_3481701 baseEnd_3481701 := by
    simpa [prefixWord, tailWord_3481701, baseEnd_3481701] using wordTrace_append hprefix tailTrace_3481701
  have hstable : (prefixWord ++ tailWord_3481701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481701).length < 2 ^ (prefixWord ++ tailWord_3481701).sum := by decide
  have hdescent : baseEnd_3481701 < baseStart_3481701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481731 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 3, 3]
def baseStart_3481731 : Nat := 118140960795 + 3481731 * 2 ^ 59
def prefixEnd_3481731 : Nat := 4983230072969 + 3 ^ 40 * 3481731 * 2
def baseEnd_3481731 : Nat := 1191867675106281630100211

theorem tailTrace_3481731 : CollatzResearch.WordTrace tailWord_3481731 prefixEnd_3481731 1191867675106281630100211 := by
  unfold tailWord_3481731
  simp only [CollatzResearch.WordTrace]
  refine ⟨126989162149290694158813047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84659441432860462772542031 126989162149290694158813047)
  ·
    refine ⟨190483743223936041238219571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126989162149290694158813047 190483743223936041238219571)
    ·
      refine ⟨285725614835904061857329357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190483743223936041238219571 285725614835904061857329357)
      ·
        refine ⟨107147105563464023196498509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285725614835904061857329357 107147105563464023196498509)
        ·
          refine ⟨40180164586299008698686941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107147105563464023196498509 40180164586299008698686941)
          ·
            refine ⟨15067561719862128262007603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40180164586299008698686941 15067561719862128262007603)
            ·
              refine ⟨22601342579793192393011405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067561719862128262007603 22601342579793192393011405)
              ·
                refine ⟨8475503467422447147379277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22601342579793192393011405 8475503467422447147379277)
                ·
                  refine ⟨3178313800283417680267229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8475503467422447147379277 3178313800283417680267229)
                  ·
                    refine ⟨1191867675106281630100211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178313800283417680267229 1191867675106281630100211)
                    ·
                      rfl

theorem cell22_3481731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 3].length) (baseStart_3481731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481731 prefixEnd_3481731 := by exact prefixLift 3481731
  have htrace : WordTrace (prefixWord ++ tailWord_3481731) baseStart_3481731 baseEnd_3481731 := by
    simpa [prefixWord, tailWord_3481731, baseEnd_3481731] using wordTrace_append hprefix tailTrace_3481731
  have hstable : (prefixWord ++ tailWord_3481731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481731).length < 2 ^ (prefixWord ++ tailWord_3481731).sum := by decide
  have hdescent : baseEnd_3481731 < baseStart_3481731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481836 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3481836 : Nat := 118140960795 + 3481836 * 2 ^ 59
def prefixEnd_3481836 : Nat := 4983230072969 + 3 ^ 40 * 3481836 * 2
def baseEnd_3481836 : Nat := 1191903618752096356224889

theorem tailTrace_3481836 : CollatzResearch.WordTrace tailWord_3481836 prefixEnd_3481836 1191903618752096356224889 := by
  unfold tailWord_3481836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63496495906955148545692681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84661994542606864727590241 63496495906955148545692681)
  ·
    refine ⟨47622371930216361409269511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63496495906955148545692681 47622371930216361409269511)
    ·
      refine ⟨71433557895324542113904267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47622371930216361409269511 71433557895324542113904267)
      ·
        refine ⟨107150336842986813170856401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71433557895324542113904267 107150336842986813170856401)
        ·
          refine ⟨80362752632240109878142301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107150336842986813170856401 80362752632240109878142301)
          ·
            refine ⟨30136032237090041204303363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80362752632240109878142301 30136032237090041204303363)
            ·
              refine ⟨45204048355635061806455045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30136032237090041204303363 45204048355635061806455045)
              ·
                refine ⟨8475759066681574088710321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45204048355635061806455045 8475759066681574088710321)
                ·
                  refine ⟨6356819300011180566532741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8475759066681574088710321 6356819300011180566532741)
                  ·
                    refine ⟨1191903618752096356224889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6356819300011180566532741 1191903618752096356224889)
                    ·
                      rfl

theorem cell22_3481836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3481836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481836 prefixEnd_3481836 := by exact prefixLift 3481836
  have htrace : WordTrace (prefixWord ++ tailWord_3481836) baseStart_3481836 baseEnd_3481836 := by
    simpa [prefixWord, tailWord_3481836, baseEnd_3481836] using wordTrace_append hprefix tailTrace_3481836
  have hstable : (prefixWord ++ tailWord_3481836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481836).length < 2 ^ (prefixWord ++ tailWord_3481836).sum := by decide
  have hdescent : baseEnd_3481836 < baseStart_3481836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481900 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_3481900 : Nat := 118140960795 + 3481900 * 2 ^ 59
def prefixEnd_3481900 : Nat := 4983230072969 + 3 ^ 40 * 3481900 * 2
def baseEnd_3481900 : Nat := 1191925527260021522624693

theorem tailTrace_3481900 : CollatzResearch.WordTrace tailWord_3481900 prefixEnd_3481900 1191925527260021522624693 := by
  unfold tailWord_3481900
  simp only [CollatzResearch.WordTrace]
  refine ⟨63497663042839218010857577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84663550723785624014476769 63497663042839218010857577)
  ·
    refine ⟨47623247282129413508143183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63497663042839218010857577 47623247282129413508143183)
    ·
      refine ⟨71434870923194120262214775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47623247282129413508143183 71434870923194120262214775)
      ·
        refine ⟨107152306384791180393322163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71434870923194120262214775 107152306384791180393322163)
        ·
          refine ⟨160728459577186770589983245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107152306384791180393322163 160728459577186770589983245)
          ·
            refine ⟨60273172341445038971243717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160728459577186770589983245 60273172341445038971243717)
            ·
              refine ⟨11301219814020944807108197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60273172341445038971243717 11301219814020944807108197)
              ·
                refine ⟨2118978715128927151332787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11301219814020944807108197 2118978715128927151332787)
                ·
                  refine ⟨3178468072693390726999181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2118978715128927151332787 3178468072693390726999181)
                  ·
                    refine ⟨1191925527260021522624693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178468072693390726999181 1191925527260021522624693)
                    ·
                      rfl

theorem cell22_3481900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_3481900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481900 prefixEnd_3481900 := by exact prefixLift 3481900
  have htrace : WordTrace (prefixWord ++ tailWord_3481900) baseStart_3481900 baseEnd_3481900 := by
    simpa [prefixWord, tailWord_3481900, baseEnd_3481900] using wordTrace_append hprefix tailTrace_3481900
  have hstable : (prefixWord ++ tailWord_3481900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481900).length < 2 ^ (prefixWord ++ tailWord_3481900).sum := by decide
  have hdescent : baseEnd_3481900 < baseStart_3481900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481943 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 1, 4]
def baseStart_3481943 : Nat := 118140960795 + 3481943 * 2 ^ 59
def prefixEnd_3481943 : Nat := 4983230072969 + 3 ^ 40 * 3481943 * 2
def baseEnd_3481943 : Nat := 1191940247038783743799561

theorem tailTrace_3481943 : CollatzResearch.WordTrace tailWord_3481943 prefixEnd_3481943 1191940247038783743799561 := by
  unfold tailWord_3481943
  simp only [CollatzResearch.WordTrace]
  refine ⟨126996894424522654365530483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84664596283015102910353655 126996894424522654365530483)
  ·
    refine ⟨190495341636783981548295725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126996894424522654365530483 190495341636783981548295725)
    ·
      refine ⟨71435753113793993080610897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190495341636783981548295725 71435753113793993080610897)
      ·
        refine ⟨53576814835345494810458173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71435753113793993080610897 53576814835345494810458173)
        ·
          refine ⟨20091305563254560553921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53576814835345494810458173 20091305563254560553921815)
          ·
            refine ⟨30136958344881840830882723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20091305563254560553921815 30136958344881840830882723)
            ·
              refine ⟨45205437517322761246324085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30136958344881840830882723 45205437517322761246324085)
              ·
                refine ⟨4238009767249008866842883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45205437517322761246324085 4238009767249008866842883)
                ·
                  refine ⟨6357014650873513300264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238009767249008866842883 6357014650873513300264325)
                  ·
                    refine ⟨1191940247038783743799561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357014650873513300264325 1191940247038783743799561)
                    ·
                      rfl

theorem cell22_3481943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_3481943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481943 prefixEnd_3481943 := by exact prefixLift 3481943
  have htrace : WordTrace (prefixWord ++ tailWord_3481943) baseStart_3481943 baseEnd_3481943 := by
    simpa [prefixWord, tailWord_3481943, baseEnd_3481943] using wordTrace_append hprefix tailTrace_3481943
  have hstable : (prefixWord ++ tailWord_3481943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481943).length < 2 ^ (prefixWord ++ tailWord_3481943).sum := by decide
  have hdescent : baseEnd_3481943 < baseStart_3481943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3481994 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3481994 : Nat := 118140960795 + 3481994 * 2 ^ 59
def prefixEnd_3481994 : Nat := 4983230072969 + 3 ^ 40 * 3481994 * 2
def baseEnd_3481994 : Nat := 1191957705381036610774405

theorem tailTrace_3481994 : CollatzResearch.WordTrace tailWord_3481994 prefixEnd_3481994 1191957705381036610774405 := by
  unfold tailWord_3481994
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749688636834472518909259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84665836364891926717091357 31749688636834472518909259)
  ·
    refine ⟨47624532955251708778363889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31749688636834472518909259 47624532955251708778363889)
    ·
      refine ⟨35718399716438781583772917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47624532955251708778363889 35718399716438781583772917)
      ·
        refine ⟨3348599973416135773478711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35718399716438781583772917 3348599973416135773478711)
        ·
          refine ⟨5022899960124203660218067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348599973416135773478711 5022899960124203660218067)
          ·
            refine ⟨7534349940186305490327101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022899960124203660218067 7534349940186305490327101)
            ·
              refine ⟨2825381227569864558872663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7534349940186305490327101 2825381227569864558872663)
              ·
                refine ⟨4238071841354796838308995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825381227569864558872663 4238071841354796838308995)
                ·
                  refine ⟨6357107762032195257463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238071841354796838308995 6357107762032195257463493)
                  ·
                    refine ⟨1191957705381036610774405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357107762032195257463493 1191957705381036610774405)
                    ·
                      rfl

theorem cell22_3481994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3481994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3481994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3481994 prefixEnd_3481994 := by exact prefixLift 3481994
  have htrace : WordTrace (prefixWord ++ tailWord_3481994) baseStart_3481994 baseEnd_3481994 := by
    simpa [prefixWord, tailWord_3481994, baseEnd_3481994] using wordTrace_append hprefix tailTrace_3481994
  have hstable : (prefixWord ++ tailWord_3481994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3481994).length < 2 ^ (prefixWord ++ tailWord_3481994).sum := by decide
  have hdescent : baseEnd_3481994 < baseStart_3481994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3481994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482031 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 11]
def baseStart_3482031 : Nat := 118140960795 + 3482031 * 2 ^ 59
def prefixEnd_3482031 : Nat := 4983230072969 + 3 ^ 40 * 3482031 * 2
def baseEnd_3482031 : Nat := 397323457079060282533097

theorem tailTrace_3482031 : CollatzResearch.WordTrace tailWord_3482031 prefixEnd_3482031 397323457079060282533097 := by
  unfold tailWord_3482031
  simp only [CollatzResearch.WordTrace]
  refine ⟨127000104048203845394733947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84666736032135896929822631 127000104048203845394733947)
  ·
    refine ⟨190500156072305768092100921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127000104048203845394733947 190500156072305768092100921)
    ·
      refine ⟨142875117054229326069075691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190500156072305768092100921 142875117054229326069075691)
      ·
        refine ⟨214312675581343989103613537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142875117054229326069075691 214312675581343989103613537)
        ·
          refine ⟨160734506686007991827710153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214312675581343989103613537 160734506686007991827710153)
          ·
            refine ⟨120550880014505993870782615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160734506686007991827710153 120550880014505993870782615)
            ·
              refine ⟨180826320021758990806173923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120550880014505993870782615 180826320021758990806173923)
              ·
                refine ⟨271239480032638486209260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180826320021758990806173923 271239480032638486209260885)
                ·
                  refine ⟨397323457079060282533097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 271239480032638486209260885 397323457079060282533097)
                  ·
                    rfl

theorem cell22_3482031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_3482031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482031 prefixEnd_3482031 := by exact prefixLift 3482031
  have htrace : WordTrace (prefixWord ++ tailWord_3482031) baseStart_3482031 baseEnd_3482031 := by
    simpa [prefixWord, tailWord_3482031, baseEnd_3482031] using wordTrace_append hprefix tailTrace_3482031
  have hstable : (prefixWord ++ tailWord_3482031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482031).length < 2 ^ (prefixWord ++ tailWord_3482031).sum := by decide
  have hdescent : baseEnd_3482031 < baseStart_3482031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482108 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3482108 : Nat := 118140960795 + 3482108 * 2 ^ 59
def prefixEnd_3482108 : Nat := 4983230072969 + 3 ^ 40 * 3482108 * 2
def baseEnd_3482108 : Nat := 1191996729910778313424055

theorem tailTrace_3482108 : CollatzResearch.WordTrace tailWord_3482108 prefixEnd_3482108 1191996729910778313424055 := by
  unfold tailWord_3482108
  simp only [CollatzResearch.WordTrace]
  refine ⟨63501456234462443772643489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84668608312616591696857985 63501456234462443772643489)
  ·
    refine ⟨47626092175846832829482617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63501456234462443772643489 47626092175846832829482617)
    ·
      refine ⟨35719569131885124622111963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47626092175846832829482617 35719569131885124622111963)
      ·
        refine ⟨53579353697827686933167945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35719569131885124622111963 53579353697827686933167945)
        ·
          refine ⟨40184515273370765199875959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53579353697827686933167945 40184515273370765199875959)
          ·
            refine ⟨60276772910056147799813939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40184515273370765199875959 60276772910056147799813939)
            ·
              refine ⟨90415159365084221699720909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60276772910056147799813939 90415159365084221699720909)
              ·
                refine ⟨33905684761906583137395341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90415159365084221699720909 33905684761906583137395341)
                ·
                  refine ⟨12714631785714968676523253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33905684761906583137395341 12714631785714968676523253)
                  ·
                    refine ⟨1191996729910778313424055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12714631785714968676523253 1191996729910778313424055)
                    ·
                      rfl

theorem cell22_3482108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3482108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482108 prefixEnd_3482108 := by exact prefixLift 3482108
  have htrace : WordTrace (prefixWord ++ tailWord_3482108) baseStart_3482108 baseEnd_3482108 := by
    simpa [prefixWord, tailWord_3482108, baseEnd_3482108] using wordTrace_append hprefix tailTrace_3482108
  have hstable : (prefixWord ++ tailWord_3482108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482108).length < 2 ^ (prefixWord ++ tailWord_3482108).sum := by decide
  have hdescent : baseEnd_3482108 < baseStart_3482108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482138 : List Nat := [3, 1, 1, 3, 1, 1, 3, 9]
def baseStart_3482138 : Nat := 118140960795 + 3482138 * 2 ^ 59
def prefixEnd_3482138 : Nat := 4983230072969 + 3 ^ 40 * 3482138 * 2
def baseEnd_3482138 : Nat := 132445222169318692797107

theorem tailTrace_3482138 : CollatzResearch.WordTrace tailWord_3482138 prefixEnd_3482138 132445222169318692797107 := by
  unfold tailWord_3482138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751001664704050667219767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84669337772544135112586045 31751001664704050667219767)
  ·
    refine ⟨47626502497056076000829651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31751001664704050667219767 47626502497056076000829651)
    ·
      refine ⟨71439753745584114001244477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47626502497056076000829651 71439753745584114001244477)
      ·
        refine ⟨26789907654594042750466679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71439753745584114001244477 26789907654594042750466679)
        ·
          refine ⟨40184861481891064125700019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26789907654594042750466679 40184861481891064125700019)
          ·
            refine ⟨60277292222836596188550029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40184861481891064125700019 60277292222836596188550029)
            ·
              refine ⟨22603984583563723570706261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60277292222836596188550029 22603984583563723570706261)
              ·
                refine ⟨132445222169318692797107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22603984583563723570706261 132445222169318692797107)
                ·
                  rfl

theorem cell22_3482138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_3482138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482138 prefixEnd_3482138 := by exact prefixLift 3482138
  have htrace : WordTrace (prefixWord ++ tailWord_3482138) baseStart_3482138 baseEnd_3482138 := by
    simpa [prefixWord, tailWord_3482138, baseEnd_3482138] using wordTrace_append hprefix tailTrace_3482138
  have hstable : (prefixWord ++ tailWord_3482138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482138).length < 2 ^ (prefixWord ++ tailWord_3482138).sum := by decide
  have hdescent : baseEnd_3482138 < baseStart_3482138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482200 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_3482200 : Nat := 118140960795 + 3482200 * 2 ^ 59
def prefixEnd_3482200 : Nat := 4983230072969 + 3 ^ 40 * 3482200 * 2
def baseEnd_3482200 : Nat := 397342741130306913374591

theorem tailTrace_3482200 : CollatzResearch.WordTrace tailWord_3482200 prefixEnd_3482200 397342741130306913374591 := by
  unfold tailWord_3482200
  simp only [CollatzResearch.WordTrace]
  refine ⟨63503133992295793628818027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84670845323061058171757369 63503133992295793628818027)
  ·
    refine ⟨95254700988443690443227041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63503133992295793628818027 95254700988443690443227041)
    ·
      refine ⟨71441025741332767832420281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95254700988443690443227041 71441025741332767832420281)
      ·
        refine ⟨53580769305999575874315211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71441025741332767832420281 53580769305999575874315211)
        ·
          refine ⟨80371153958999363811472817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53580769305999575874315211 80371153958999363811472817)
          ·
            refine ⟨60278365469249522858604613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80371153958999363811472817 60278365469249522858604613)
            ·
              refine ⟨11302193525484285535988365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60278365469249522858604613 11302193525484285535988365)
              ·
                refine ⟨4238322572056607075995637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302193525484285535988365 4238322572056607075995637)
                ·
                  refine ⟨397342741130306913374591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238322572056607075995637 397342741130306913374591)
                  ·
                    rfl

theorem cell22_3482200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_3482200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482200 prefixEnd_3482200 := by exact prefixLift 3482200
  have htrace : WordTrace (prefixWord ++ tailWord_3482200) baseStart_3482200 baseEnd_3482200 := by
    simpa [prefixWord, tailWord_3482200, baseEnd_3482200] using wordTrace_append hprefix tailTrace_3482200
  have hstable : (prefixWord ++ tailWord_3482200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482200).length < 2 ^ (prefixWord ++ tailWord_3482200).sum := by decide
  have hdescent : baseEnd_3482200 < baseStart_3482200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482204 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3482204 : Nat := 118140960795 + 3482204 * 2 ^ 59
def prefixEnd_3482204 : Nat := 4983230072969 + 3 ^ 40 * 3482204 * 2
def baseEnd_3482204 : Nat := 1192029592672666063023761

theorem tailTrace_3482204 : CollatzResearch.WordTrace tailWord_3482204 prefixEnd_3482204 1192029592672666063023761 := by
  unfold tailWord_3482204
  simp only [CollatzResearch.WordTrace]
  refine ⟨63503206938288547970390833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84670942584384730627187777 63503206938288547970390833)
  ·
    refine ⟨47627405203716410977793125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63503206938288547970390833 47627405203716410977793125)
    ·
      refine ⟨8930138475696827058336211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47627405203716410977793125 8930138475696827058336211)
      ·
        refine ⟨13395207713545240587504317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930138475696827058336211 13395207713545240587504317)
        ·
          refine ⟨5023202892579465220314119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13395207713545240587504317 5023202892579465220314119)
          ·
            refine ⟨7534804338869197830471179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023202892579465220314119 7534804338869197830471179)
            ·
              refine ⟨11302206508303796745706769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534804338869197830471179 11302206508303796745706769)
              ·
                refine ⟨8476654881227847559280077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11302206508303796745706769 8476654881227847559280077)
                ·
                  refine ⟨3178745580460442834730029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8476654881227847559280077 3178745580460442834730029)
                  ·
                    refine ⟨1192029592672666063023761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178745580460442834730029 1192029592672666063023761)
                    ·
                      rfl

theorem cell22_3482204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3482204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482204 prefixEnd_3482204 := by exact prefixLift 3482204
  have htrace : WordTrace (prefixWord ++ tailWord_3482204) baseStart_3482204 baseEnd_3482204 := by
    simpa [prefixWord, tailWord_3482204, baseEnd_3482204] using wordTrace_append hprefix tailTrace_3482204
  have hstable : (prefixWord ++ tailWord_3482204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482204).length < 2 ^ (prefixWord ++ tailWord_3482204).sum := by decide
  have hdescent : baseEnd_3482204 < baseStart_3482204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482221 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3482221 : Nat := 118140960795 + 3482221 * 2 ^ 59
def prefixEnd_3482221 : Nat := 4983230072969 + 3 ^ 40 * 3482221 * 2
def baseEnd_3482221 : Nat := 1192035412120083685348709

theorem tailTrace_3482221 : CollatzResearch.WordTrace tailWord_3482221 prefixEnd_3482221 1192035412120083685348709 := by
  unfold tailWord_3482221
  simp only [CollatzResearch.WordTrace]
  refine ⟨127007033917515507844150517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84671355945010338562767011 127007033917515507844150517)
  ·
    refine ⟨11906909429767078860389111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127007033917515507844150517 11906909429767078860389111)
    ·
      refine ⟨17860364144650618290583667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11906909429767078860389111 17860364144650618290583667)
      ·
        refine ⟨26790546216975927435875501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17860364144650618290583667 26790546216975927435875501)
        ·
          refine ⟨10046454831365972788453313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26790546216975927435875501 10046454831365972788453313)
          ·
            refine ⟨7534841123524479591339985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10046454831365972788453313 7534841123524479591339985)
            ·
              refine ⟨5651130842643359693504989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534841123524479591339985 5651130842643359693504989)
              ·
                refine ⟨2119174065991259885064371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5651130842643359693504989 2119174065991259885064371)
                ·
                  refine ⟨3178761098986889827596557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119174065991259885064371 3178761098986889827596557)
                  ·
                    refine ⟨1192035412120083685348709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3178761098986889827596557 1192035412120083685348709)
                    ·
                      rfl

theorem cell22_3482221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3482221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482221 prefixEnd_3482221 := by exact prefixLift 3482221
  have htrace : WordTrace (prefixWord ++ tailWord_3482221) baseStart_3482221 baseEnd_3482221 := by
    simpa [prefixWord, tailWord_3482221, baseEnd_3482221] using wordTrace_append hprefix tailTrace_3482221
  have hstable : (prefixWord ++ tailWord_3482221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482221).length < 2 ^ (prefixWord ++ tailWord_3482221).sum := by decide
  have hdescent : baseEnd_3482221 < baseStart_3482221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482245 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 6]
def baseStart_3482245 : Nat := 118140960795 + 3482245 * 2 ^ 59
def prefixEnd_3482245 : Nat := 4983230072969 + 3 ^ 40 * 3482245 * 2
def baseEnd_3482245 : Nat := 397347875936851874249545

theorem tailTrace_3482245 : CollatzResearch.WordTrace tailWord_3482245 prefixEnd_3482245 397347875936851874249545 := by
  unfold tailWord_3482245
  simp only [CollatzResearch.WordTrace]
  refine ⟨127007909269428559943024189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84671939512952373295349459 127007909269428559943024189)
  ·
    refine ⟨47627965976035709978634071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127007909269428559943024189 47627965976035709978634071)
    ·
      refine ⟨71441948964053564967951107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47627965976035709978634071 71441948964053564967951107)
      ·
        refine ⟨107162923446080347451926661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71441948964053564967951107 107162923446080347451926661)
        ·
          refine ⟨20093048146140065147236249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107162923446080347451926661 20093048146140065147236249)
          ·
            refine ⟨15069786109605048860427187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20093048146140065147236249 15069786109605048860427187)
            ·
              refine ⟨22604679164407573290640781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15069786109605048860427187 22604679164407573290640781)
              ·
                refine ⟨8476754686652839983990293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22604679164407573290640781 8476754686652839983990293)
                ·
                  refine ⟨397347875936851874249545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8476754686652839983990293 397347875936851874249545)
                  ·
                    rfl

theorem cell22_3482245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_3482245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482245 prefixEnd_3482245 := by exact prefixLift 3482245
  have htrace : WordTrace (prefixWord ++ tailWord_3482245) baseStart_3482245 baseEnd_3482245 := by
    simpa [prefixWord, tailWord_3482245, baseEnd_3482245] using wordTrace_append hprefix tailTrace_3482245
  have hstable : (prefixWord ++ tailWord_3482245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482245).length < 2 ^ (prefixWord ++ tailWord_3482245).sum := by decide
  have hdescent : baseEnd_3482245 < baseStart_3482245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482352 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_3482352 : Nat := 118140960795 + 3482352 * 2 ^ 59
def prefixEnd_3482352 : Nat := 4983230072969 + 3 ^ 40 * 3482352 * 2
def baseEnd_3482352 : Nat := 397360085365747670107769

theorem tailTrace_3482352 : CollatzResearch.WordTrace tailWord_3482352 prefixEnd_3482352 397360085365747670107769 := by
  unfold tailWord_3482352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63505905940020458608584655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84674541253360611478112873 63505905940020458608584655)
  ·
    refine ⟨95258858910030687912876983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63505905940020458608584655 95258858910030687912876983)
    ·
      refine ⟨142888288365046031869315475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95258858910030687912876983 142888288365046031869315475)
      ·
        refine ⟨214332432547569047803973213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142888288365046031869315475 214332432547569047803973213)
        ·
          refine ⟨80374662205338392926489955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214332432547569047803973213 80374662205338392926489955)
          ·
            refine ⟨120561993308007589389734933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80374662205338392926489955 120561993308007589389734933)
            ·
              refine ⟨5651343436312855752643825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120561993308007589389734933 5651343436312855752643825)
              ·
                refine ⟨4238507577234641814482869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651343436312855752643825 4238507577234641814482869)
                ·
                  refine ⟨397360085365747670107769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238507577234641814482869 397360085365747670107769)
                  ·
                    rfl

theorem cell22_3482352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_3482352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482352 prefixEnd_3482352 := by exact prefixLift 3482352
  have htrace : WordTrace (prefixWord ++ tailWord_3482352) baseStart_3482352 baseEnd_3482352 := by
    simpa [prefixWord, tailWord_3482352, baseEnd_3482352] using wordTrace_append hprefix tailTrace_3482352
  have hstable : (prefixWord ++ tailWord_3482352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482352).length < 2 ^ (prefixWord ++ tailWord_3482352).sum := by decide
  have hdescent : baseEnd_3482352 < baseStart_3482352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482399 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 1, 4]
def baseStart_3482399 : Nat := 118140960795 + 3482399 * 2 ^ 59
def prefixEnd_3482399 : Nat := 4983230072969 + 3 ^ 40 * 3482399 * 2
def baseEnd_3482399 : Nat := 1192096345157750554398163

theorem tailTrace_3482399 : CollatzResearch.WordTrace tailWord_3482399 prefixEnd_3482399 1192096345157750554398163 := by
  unfold tailWord_3482399
  simp only [CollatzResearch.WordTrace]
  refine ⟨127013526110870644244130251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84675684073913762829420167 127013526110870644244130251)
  ·
    refine ⟨190520289166305966366195377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127013526110870644244130251 190520289166305966366195377)
    ·
      refine ⟨142890216874729474774646533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190520289166305966366195377 142890216874729474774646533)
      ·
        refine ⟨26791915664011776520246225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142890216874729474774646533 26791915664011776520246225)
        ·
          refine ⟨20093936748008832390184669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26791915664011776520246225 20093936748008832390184669)
          ·
            refine ⟨7535226280503312146319251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20093936748008832390184669 7535226280503312146319251)
            ·
              refine ⟨11302839420754968219478877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7535226280503312146319251 11302839420754968219478877)
              ·
                refine ⟨4238564782783113082304579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11302839420754968219478877 4238564782783113082304579)
                ·
                  refine ⟨6357847174174669623456869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238564782783113082304579 6357847174174669623456869)
                  ·
                    refine ⟨1192096345157750554398163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357847174174669623456869 1192096345157750554398163)
                    ·
                      rfl

theorem cell22_3482399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_3482399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482399 prefixEnd_3482399 := by exact prefixLift 3482399
  have htrace : WordTrace (prefixWord ++ tailWord_3482399) baseStart_3482399 baseEnd_3482399 := by
    simpa [prefixWord, tailWord_3482399, baseEnd_3482399] using wordTrace_append hprefix tailTrace_3482399
  have hstable : (prefixWord ++ tailWord_3482399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482399).length < 2 ^ (prefixWord ++ tailWord_3482399).sum := by decide
  have hdescent : baseEnd_3482399 < baseStart_3482399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482414 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_3482414 : Nat := 118140960795 + 3482414 * 2 ^ 59
def prefixEnd_3482414 : Nat := 4983230072969 + 3 ^ 40 * 3482414 * 2
def baseEnd_3482414 : Nat := 397367159988098505091039

theorem tailTrace_3482414 : CollatzResearch.WordTrace tailWord_3482414 prefixEnd_3482414 397367159988098505091039 := by
  unfold tailWord_3482414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876759150727037725740787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84676048803877534537284197 15876759150727037725740787)
  ·
    refine ⟨23815138726090556588611181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15876759150727037725740787 23815138726090556588611181)
    ·
      refine ⟨8930677022283958720729193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23815138726090556588611181 8930677022283958720729193)
      ·
        refine ⟨6698007766712969040546895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8930677022283958720729193 6698007766712969040546895)
        ·
          refine ⟨10047011650069453560820343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6698007766712969040546895 10047011650069453560820343)
          ·
            refine ⟨15070517475104180341230515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047011650069453560820343 15070517475104180341230515)
            ·
              refine ⟨22605776212656270511845773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15070517475104180341230515 22605776212656270511845773)
              ·
                refine ⟨8477166079746101441942165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22605776212656270511845773 8477166079746101441942165)
                ·
                  refine ⟨397367159988098505091039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8477166079746101441942165 397367159988098505091039)
                  ·
                    rfl

theorem cell22_3482414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_3482414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482414 prefixEnd_3482414 := by exact prefixLift 3482414
  have htrace : WordTrace (prefixWord ++ tailWord_3482414) baseStart_3482414 baseEnd_3482414 := by
    simpa [prefixWord, tailWord_3482414, baseEnd_3482414] using wordTrace_append hprefix tailTrace_3482414
  have hstable : (prefixWord ++ tailWord_3482414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482414).length < 2 ^ (prefixWord ++ tailWord_3482414).sum := by decide
  have hdescent : baseEnd_3482414 < baseStart_3482414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482433 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3482433 : Nat := 118140960795 + 3482433 * 2 ^ 59
def prefixEnd_3482433 : Nat := 4983230072969 + 3 ^ 40 * 3482433 * 2
def baseEnd_3482433 : Nat := 1192107984052585799048059

theorem tailTrace_3482433 : CollatzResearch.WordTrace tailWord_3482433 prefixEnd_3482433 1192107984052585799048059 := by
  unfold tailWord_3482433
  simp only [CollatzResearch.WordTrace]
  refine ⟨127014766192747468050867953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84676510795164978700578635 127014766192747468050867953)
  ·
    refine ⟨95261074644560601038150965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127014766192747468050867953 95261074644560601038150965)
    ·
      refine ⟨8930725747927556347326653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95261074644560601038150965 8930725747927556347326653)
      ·
        refine ⟨3349022155472833630247495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8930725747927556347326653 3349022155472833630247495)
        ·
          refine ⟨5023533233209250445371243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349022155472833630247495 5023533233209250445371243)
          ·
            refine ⟨7535299849813875668056865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5023533233209250445371243 7535299849813875668056865)
            ·
              refine ⟨5651474887360406751042649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7535299849813875668056865 5651474887360406751042649)
              ·
                refine ⟨4238606165520305063281987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651474887360406751042649 4238606165520305063281987)
                ·
                  refine ⟨6357909248280457594922981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4238606165520305063281987 6357909248280457594922981)
                  ·
                    refine ⟨1192107984052585799048059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6357909248280457594922981 1192107984052585799048059)
                    ·
                      rfl

theorem cell22_3482433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3482433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482433 prefixEnd_3482433 := by exact prefixLift 3482433
  have htrace : WordTrace (prefixWord ++ tailWord_3482433) baseStart_3482433 baseEnd_3482433 := by
    simpa [prefixWord, tailWord_3482433, baseEnd_3482433] using wordTrace_append hprefix tailTrace_3482433
  have hstable : (prefixWord ++ tailWord_3482433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482433).length < 2 ^ (prefixWord ++ tailWord_3482433).sum := by decide
  have hdescent : baseEnd_3482433 < baseStart_3482433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482549 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 6]
def baseStart_3482549 : Nat := 118140960795 + 3482549 * 2 ^ 59
def prefixEnd_3482549 : Nat := 4983230072969 + 3 ^ 40 * 3482549 * 2
def baseEnd_3482549 : Nat := 397382564407733387715901

theorem tailTrace_3482549 : CollatzResearch.WordTrace tailWord_3482549 prefixEnd_3482549 397382564407733387715901 := by
  unfold tailWord_3482549
  simp only [CollatzResearch.WordTrace]
  refine ⟨127018997060327219862090701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84679331373551479908060467 127018997060327219862090701)
  ·
    refine ⟨47632123897622707448284013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127018997060327219862090701 47632123897622707448284013)
    ·
      refine ⟨17862046461608515293106505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47632123897622707448284013 17862046461608515293106505)
      ·
        refine ⟨13396534846206386469829879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17862046461608515293106505 13396534846206386469829879)
        ·
          refine ⟨20094802269309579704744819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396534846206386469829879 20094802269309579704744819)
          ·
            refine ⟨30142203403964369557117229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20094802269309579704744819 30142203403964369557117229)
            ·
              refine ⟨11303326276486638583918961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30142203403964369557117229 11303326276486638583918961)
              ·
                refine ⟨8477494707364978937939221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11303326276486638583918961 8477494707364978937939221)
                ·
                  refine ⟨397382564407733387715901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8477494707364978937939221 397382564407733387715901)
                  ·
                    rfl

theorem cell22_3482549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_3482549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482549 prefixEnd_3482549 := by exact prefixLift 3482549
  have htrace : WordTrace (prefixWord ++ tailWord_3482549) baseStart_3482549 baseEnd_3482549 := by
    simpa [prefixWord, tailWord_3482549, baseEnd_3482549] using wordTrace_append hprefix tailTrace_3482549
  have hstable : (prefixWord ++ tailWord_3482549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482549).length < 2 ^ (prefixWord ++ tailWord_3482549).sum := by decide
  have hdescent : baseEnd_3482549 < baseStart_3482549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482577 : List Nat := [1, 2, 2, 1, 2, 1, 13]
def baseStart_3482577 : Nat := 118140960795 + 3482577 * 2 ^ 59
def prefixEnd_3482577 : Nat := 4983230072969 + 3 ^ 40 * 3482577 * 2
def baseEnd_3482577 : Nat := 44153973266496941609171

theorem tailTrace_3482577 : CollatzResearch.WordTrace tailWord_3482577 prefixEnd_3482577 44153973266496941609171 := by
  unfold tailWord_3482577
  simp only [CollatzResearch.WordTrace]
  refine ⟨127020018304225780644109985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84680012202817187096073323 127020018304225780644109985)
  ·
    refine ⟨95265013728169335483082489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127020018304225780644109985 95265013728169335483082489)
    ·
      refine ⟨71448760296127001612311867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95265013728169335483082489 71448760296127001612311867)
      ·
        refine ⟨107173140444190502418467801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71448760296127001612311867 107173140444190502418467801)
        ·
          refine ⟨80379855333142876813850851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107173140444190502418467801 80379855333142876813850851)
          ·
            refine ⟨120569782999714315220776277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80379855333142876813850851 120569782999714315220776277)
            ·
              refine ⟨44153973266496941609171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 120569782999714315220776277 44153973266496941609171)
              ·
                rfl

theorem cell22_3482577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 13].length) (baseStart_3482577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482577 prefixEnd_3482577 := by exact prefixLift 3482577
  have htrace : WordTrace (prefixWord ++ tailWord_3482577) baseStart_3482577 baseEnd_3482577 := by
    simpa [prefixWord, tailWord_3482577, baseEnd_3482577] using wordTrace_append hprefix tailTrace_3482577
  have hstable : (prefixWord ++ tailWord_3482577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482577).length < 2 ^ (prefixWord ++ tailWord_3482577).sum := by decide
  have hdescent : baseEnd_3482577 < baseStart_3482577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482694 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3482694 : Nat := 118140960795 + 3482694 * 2 ^ 59
def prefixEnd_3482694 : Nat := 4983230072969 + 3 ^ 40 * 3482694 * 2
def baseEnd_3482694 : Nat := 1192197329686468118272259

theorem tailTrace_3482694 : CollatzResearch.WordTrace tailWord_3482694 prefixEnd_3482694 1192197329686468118272259 := by
  unfold tailWord_3482694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969508926400059675816223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84682857096534606417412757 3969508926400059675816223)
  ·
    refine ⟨5954263389600089513724335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3969508926400059675816223 5954263389600089513724335)
    ·
      refine ⟨8931395084400134270586503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954263389600089513724335 8931395084400134270586503)
      ·
        refine ⟨13397092626600201405879755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931395084400134270586503 13397092626600201405879755)
        ·
          refine ⟨20095638939900302108819633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397092626600201405879755 20095638939900302108819633)
          ·
            refine ⟨15071729204925226581614725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20095638939900302108819633 15071729204925226581614725)
            ·
              refine ⟨2825949225923479984052761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15071729204925226581614725 2825949225923479984052761)
              ·
                refine ⟨2119461919442609988039571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825949225923479984052761 2119461919442609988039571)
                ·
                  refine ⟨3179192879163914982059357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2119461919442609988039571 3179192879163914982059357)
                  ·
                    refine ⟨1192197329686468118272259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179192879163914982059357 1192197329686468118272259)
                    ·
                      rfl

theorem cell22_3482694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3482694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482694 prefixEnd_3482694 := by exact prefixLift 3482694
  have htrace : WordTrace (prefixWord ++ tailWord_3482694) baseStart_3482694 baseEnd_3482694 := by
    simpa [prefixWord, tailWord_3482694, baseEnd_3482694] using wordTrace_append hprefix tailTrace_3482694
  have hstable : (prefixWord ++ tailWord_3482694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482694).length < 2 ^ (prefixWord ++ tailWord_3482694).sum := by decide
  have hdescent : baseEnd_3482694 < baseStart_3482694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482818 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3482818 : Nat := 118140960795 + 3482818 * 2 ^ 59
def prefixEnd_3482818 : Nat := 4983230072969 + 3 ^ 40 * 3482818 * 2
def baseEnd_3482818 : Nat := 1192239777420573128171879

theorem tailTrace_3482818 : CollatzResearch.WordTrace tailWord_3482818 prefixEnd_3482818 1192239777420573128171879 := by
  unfold tailWord_3482818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757202074088169700908277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84685872197568452535755405 31757202074088169700908277)
  ·
    refine ⟨2977237694445765909460151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31757202074088169700908277 2977237694445765909460151)
    ·
      refine ⟨4465856541668648864190227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977237694445765909460151 4465856541668648864190227)
      ·
        refine ⟨6698784812502973296285341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465856541668648864190227 6698784812502973296285341)
        ·
          refine ⟨2512044304688614986107003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6698784812502973296285341 2512044304688614986107003)
          ·
            refine ⟨3768066457032922479160505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512044304688614986107003 3768066457032922479160505)
            ·
              refine ⟨2826049842774691859370379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768066457032922479160505 2826049842774691859370379)
              ·
                refine ⟨4239074764162037789055569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826049842774691859370379 4239074764162037789055569)
                ·
                  refine ⟨3179306073121528341791677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239074764162037789055569 3179306073121528341791677)
                  ·
                    refine ⟨1192239777420573128171879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179306073121528341791677 1192239777420573128171879)
                    ·
                      rfl

theorem cell22_3482818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3482818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482818 prefixEnd_3482818 := by exact prefixLift 3482818
  have htrace : WordTrace (prefixWord ++ tailWord_3482818) baseStart_3482818 baseEnd_3482818 := by
    simpa [prefixWord, tailWord_3482818, baseEnd_3482818] using wordTrace_append hprefix tailTrace_3482818
  have hstable : (prefixWord ++ tailWord_3482818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482818).length < 2 ^ (prefixWord ++ tailWord_3482818).sum := by decide
  have hdescent : baseEnd_3482818 < baseStart_3482818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482821 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3482821 : Nat := 118140960795 + 3482821 * 2 ^ 59
def prefixEnd_3482821 : Nat := 4983230072969 + 3 ^ 40 * 3482821 * 2
def baseEnd_3482821 : Nat := 1192240804381882120346869

theorem tailTrace_3482821 : CollatzResearch.WordTrace tailWord_3482821 prefixEnd_3482821 1192240804381882120346869 := by
  unfold tailWord_3482821
  simp only [CollatzResearch.WordTrace]
  refine ⟨127028917715341810315992317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84685945143561206877328211 127028917715341810315992317)
  ·
    refine ⟨47635844143253178868497119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127028917715341810315992317 47635844143253178868497119)
    ·
      refine ⟨71453766214879768302745679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47635844143253178868497119 71453766214879768302745679)
      ·
        refine ⟨107180649322319652454118519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71453766214879768302745679 107180649322319652454118519)
        ·
          refine ⟨160770973983479478681177779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107180649322319652454118519 160770973983479478681177779)
          ·
            refine ⟨241156460975219218021766669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160770973983479478681177779 241156460975219218021766669)
            ·
              refine ⟨90433672865707206758162501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241156460975219218021766669 90433672865707206758162501)
              ·
                refine ⟨16956313662320101267155469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90433672865707206758162501 16956313662320101267155469)
                ·
                  refine ⟨6358617623370037975183301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16956313662320101267155469 6358617623370037975183301)
                  ·
                    refine ⟨1192240804381882120346869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6358617623370037975183301 1192240804381882120346869)
                    ·
                      rfl

theorem cell22_3482821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3482821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482821 prefixEnd_3482821 := by exact prefixLift 3482821
  have htrace : WordTrace (prefixWord ++ tailWord_3482821) baseStart_3482821 baseEnd_3482821 := by
    simpa [prefixWord, tailWord_3482821, baseEnd_3482821] using wordTrace_append hprefix tailTrace_3482821
  have hstable : (prefixWord ++ tailWord_3482821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482821).length < 2 ^ (prefixWord ++ tailWord_3482821).sum := by decide
  have hdescent : baseEnd_3482821 < baseStart_3482821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482913 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3482913 : Nat := 118140960795 + 3482913 * 2 ^ 59
def prefixEnd_3482913 : Nat := 4983230072969 + 3 ^ 40 * 3482913 * 2
def baseEnd_3482913 : Nat := 1192272297862024547046587

theorem tailTrace_3482913 : CollatzResearch.WordTrace tailWord_3482913 prefixEnd_3482913 1192272297862024547046587 := by
  unfold tailWord_3482913
  simp only [CollatzResearch.WordTrace]
  refine ⟨127032273231008510028341393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84688182154005673352227595 127032273231008510028341393)
  ·
    refine ⟨95274204923256382521256045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127032273231008510028341393 95274204923256382521256045)
    ·
      refine ⟨35727826846221143445471017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95274204923256382521256045 35727826846221143445471017)
      ·
        refine ⟨26795870134665857584103263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35727826846221143445471017 26795870134665857584103263)
        ·
          refine ⟨40193805201998786376154895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26795870134665857584103263 40193805201998786376154895)
          ·
            refine ⟨60290707802998179564232343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40193805201998786376154895 60290707802998179564232343)
            ·
              refine ⟨90436061704497269346348515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60290707802998179564232343 90436061704497269346348515)
              ·
                refine ⟨135654092556745904019522773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90436061704497269346348515 135654092556745904019522773)
                ·
                  refine ⟨3179392794298732125457565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 135654092556745904019522773 3179392794298732125457565)
                  ·
                    refine ⟨1192272297862024547046587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179392794298732125457565 1192272297862024547046587)
                    ·
                      rfl

theorem cell22_3482913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3482913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482913 prefixEnd_3482913 := by exact prefixLift 3482913
  have htrace : WordTrace (prefixWord ++ tailWord_3482913) baseStart_3482913 baseEnd_3482913 := by
    simpa [prefixWord, tailWord_3482913, baseEnd_3482913] using wordTrace_append hprefix tailTrace_3482913
  have hstable : (prefixWord ++ tailWord_3482913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482913).length < 2 ^ (prefixWord ++ tailWord_3482913).sum := by decide
  have hdescent : baseEnd_3482913 < baseStart_3482913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482930 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_3482930 : Nat := 118140960795 + 3482930 * 2 ^ 59
def prefixEnd_3482930 : Nat := 4983230072969 + 3 ^ 40 * 3482930 * 2
def baseEnd_3482930 : Nat := 1192278117309442169371535

theorem tailTrace_3482930 : CollatzResearch.WordTrace tailWord_3482930 prefixEnd_3482930 1192278117309442169371535 := by
  unfold tailWord_3482930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31758223317986730482927561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84688595514631281287806829 31758223317986730482927561)
  ·
    refine ⟨23818667488490047862195671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31758223317986730482927561 23818667488490047862195671)
    ·
      refine ⟨35728001232735071793293507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23818667488490047862195671 35728001232735071793293507)
      ·
        refine ⟨53592001849102607689940261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35728001232735071793293507 53592001849102607689940261)
        ·
          refine ⟨10048500346706738941863799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53592001849102607689940261 10048500346706738941863799)
          ·
            refine ⟨15072750520060108412795699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048500346706738941863799 15072750520060108412795699)
            ·
              refine ⟨22609125780090162619193549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15072750520060108412795699 22609125780090162619193549)
              ·
                refine ⟨8478422167533810982197581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609125780090162619193549 8478422167533810982197581)
                ·
                  refine ⟨3179408312825179118324093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8478422167533810982197581 3179408312825179118324093)
                  ·
                    refine ⟨1192278117309442169371535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179408312825179118324093 1192278117309442169371535)
                    ·
                      rfl

theorem cell22_3482930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_3482930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482930 prefixEnd_3482930 := by exact prefixLift 3482930
  have htrace : WordTrace (prefixWord ++ tailWord_3482930) baseStart_3482930 baseEnd_3482930 := by
    simpa [prefixWord, tailWord_3482930, baseEnd_3482930] using wordTrace_append hprefix tailTrace_3482930
  have hstable : (prefixWord ++ tailWord_3482930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482930).length < 2 ^ (prefixWord ++ tailWord_3482930).sum := by decide
  have hdescent : baseEnd_3482930 < baseStart_3482930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3482966 : List Nat := [5, 2, 3, 1, 2, 1, 8]
def baseStart_3482966 : Nat := 118140960795 + 3482966 * 2 ^ 59
def prefixEnd_3482966 : Nat := 4983230072969 + 3 ^ 40 * 3482966 * 2
def baseEnd_3482966 : Nat := 44158905216487039832275

theorem tailTrace_3482966 : CollatzResearch.WordTrace tailWord_3482966 prefixEnd_3482966 44158905216487039832275 := by
  unfold tailWord_3482966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939637893738531255001297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84689470866544333386680501 7939637893738531255001297)
  ·
    refine ⟨5954728420303898441250973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7939637893738531255001297 5954728420303898441250973)
    ·
      refine ⟨2233023157613961915469115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5954728420303898441250973 2233023157613961915469115)
      ·
        refine ⟨3349534736420942873203673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233023157613961915469115 3349534736420942873203673)
        ·
          refine ⟨2512151052315707154902755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349534736420942873203673 2512151052315707154902755)
          ·
            refine ⟨3768226578473560732354133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512151052315707154902755 3768226578473560732354133)
            ·
              refine ⟨44158905216487039832275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3768226578473560732354133 44158905216487039832275)
              ·
                rfl

theorem cell22_3482966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 8].length) (baseStart_3482966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3482966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3482966 prefixEnd_3482966 := by exact prefixLift 3482966
  have htrace : WordTrace (prefixWord ++ tailWord_3482966) baseStart_3482966 baseEnd_3482966 := by
    simpa [prefixWord, tailWord_3482966, baseEnd_3482966] using wordTrace_append hprefix tailTrace_3482966
  have hstable : (prefixWord ++ tailWord_3482966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3482966).length < 2 ^ (prefixWord ++ tailWord_3482966).sum := by decide
  have hdescent : baseEnd_3482966 < baseStart_3482966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3482966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483003 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_3483003 : Nat := 118140960795 + 3483003 * 2 ^ 59
def prefixEnd_3483003 : Nat := 4983230072969 + 3 ^ 40 * 3483003 * 2
def baseEnd_3483003 : Nat := 1192303106701294312296311

theorem tailTrace_3483003 : CollatzResearch.WordTrace tailWord_3483003 prefixEnd_3483003 1192303106701294312296311 := by
  unfold tailWord_3483003
  simp only [CollatzResearch.WordTrace]
  refine ⟨127035555800682455399117663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84690370533788303599411775 127035555800682455399117663)
  ·
    refine ⟨190553333701023683098676495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127035555800682455399117663 190553333701023683098676495)
    ·
      refine ⟨285830000551535524648014743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190553333701023683098676495 285830000551535524648014743)
      ·
        refine ⟨428745000827303286972022115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285830000551535524648014743 428745000827303286972022115)
        ·
          refine ⟨643117501240954930458033173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428745000827303286972022115 643117501240954930458033173)
          ·
            refine ⟨30146132870669762365220305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 643117501240954930458033173 30146132870669762365220305)
            ·
              refine ⟨22609599653002321773915229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30146132870669762365220305 22609599653002321773915229)
              ·
                refine ⟨8478599869875870665218211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22609599653002321773915229 8478599869875870665218211)
                ·
                  refine ⟨12717899804813805997827317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8478599869875870665218211 12717899804813805997827317)
                  ·
                    refine ⟨1192303106701294312296311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12717899804813805997827317 1192303106701294312296311)
                    ·
                      rfl

theorem cell22_3483003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_3483003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483003 prefixEnd_3483003 := by exact prefixLift 3483003
  have htrace : WordTrace (prefixWord ++ tailWord_3483003) baseStart_3483003 baseEnd_3483003 := by
    simpa [prefixWord, tailWord_3483003, baseEnd_3483003] using wordTrace_append hprefix tailTrace_3483003
  have hstable : (prefixWord ++ tailWord_3483003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483003).length < 2 ^ (prefixWord ++ tailWord_3483003).sum := by decide
  have hdescent : baseEnd_3483003 < baseStart_3483003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483037 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_3483037 : Nat := 118140960795 + 3483037 * 2 ^ 59
def prefixEnd_3483037 : Nat := 4983230072969 + 3 ^ 40 * 3483037 * 2
def baseEnd_3483037 : Nat := 1192314745596129556946207

theorem tailTrace_3483037 : CollatzResearch.WordTrace tailWord_3483037 prefixEnd_3483037 1192314745596129556946207 := by
  unfold tailWord_3483037
  simp only [CollatzResearch.WordTrace]
  refine ⟨127036795882559279205855365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84691197255039519470570243 127036795882559279205855365)
  ·
    refine ⟨23819399227979864851097881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127036795882559279205855365 23819399227979864851097881)
    ·
      refine ⟨17864549420984898638323411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23819399227979864851097881 17864549420984898638323411)
      ·
        refine ⟨26796824131477347957485117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17864549420984898638323411 26796824131477347957485117)
        ·
          refine ⟨10048809049304005484056919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26796824131477347957485117 10048809049304005484056919)
          ·
            refine ⟨15073213573956008226085379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10048809049304005484056919 15073213573956008226085379)
            ·
              refine ⟨22609820360934012339128069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073213573956008226085379 22609820360934012339128069)
              ·
                refine ⟨4239341317675127313586513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22609820360934012339128069 4239341317675127313586513)
                ·
                  refine ⟨3179505988256345485189885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239341317675127313586513 3179505988256345485189885)
                  ·
                    refine ⟨1192314745596129556946207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179505988256345485189885 1192314745596129556946207)
                    ·
                      rfl

theorem cell22_3483037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_3483037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483037 prefixEnd_3483037 := by exact prefixLift 3483037
  have htrace : WordTrace (prefixWord ++ tailWord_3483037) baseStart_3483037 baseEnd_3483037 := by
    simpa [prefixWord, tailWord_3483037, baseEnd_3483037] using wordTrace_append hprefix tailTrace_3483037
  have hstable : (prefixWord ++ tailWord_3483037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483037).length < 2 ^ (prefixWord ++ tailWord_3483037).sum := by decide
  have hdescent : baseEnd_3483037 < baseStart_3483037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483039 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 4]
def baseStart_3483039 : Nat := 118140960795 + 3483039 * 2 ^ 59
def prefixEnd_3483039 : Nat := 4983230072969 + 3 ^ 40 * 3483039 * 2
def baseEnd_3483039 : Nat := 397438476745667406132067

theorem tailTrace_3483039 : CollatzResearch.WordTrace tailWord_3483039 prefixEnd_3483039 397438476745667406132067 := by
  unfold tailWord_3483039
  simp only [CollatzResearch.WordTrace]
  refine ⟨127036868828552033547428171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84691245885701355698285447 127036868828552033547428171)
  ·
    refine ⟨190555303242828050321142257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127036868828552033547428171 190555303242828050321142257)
    ·
      refine ⟨142916477432121037740856693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190555303242828050321142257 142916477432121037740856693)
      ·
        refine ⟨13398419759261347288205315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142916477432121037740856693 13398419759261347288205315)
        ·
          refine ⟨20097629638892020932307973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13398419759261347288205315 20097629638892020932307973)
          ·
            refine ⟨3768305557292253924807745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20097629638892020932307973 3768305557292253924807745)
            ·
              refine ⟨2826229167969190443605809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768305557292253924807745 2826229167969190443605809)
              ·
                refine ⟨2119671875976892832704357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2826229167969190443605809 2119671875976892832704357)
                ·
                  refine ⟨397438476745667406132067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119671875976892832704357 397438476745667406132067)
                  ·
                    rfl

theorem cell22_3483039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 4].length) (baseStart_3483039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483039 prefixEnd_3483039 := by exact prefixLift 3483039
  have htrace : WordTrace (prefixWord ++ tailWord_3483039) baseStart_3483039 baseEnd_3483039 := by
    simpa [prefixWord, tailWord_3483039, baseEnd_3483039] using wordTrace_append hprefix tailTrace_3483039
  have hstable : (prefixWord ++ tailWord_3483039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483039).length < 2 ^ (prefixWord ++ tailWord_3483039).sum := by decide
  have hdescent : baseEnd_3483039 < baseStart_3483039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483063 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3483063 : Nat := 118140960795 + 3483063 * 2 ^ 59
def prefixEnd_3483063 : Nat := 4983230072969 + 3 ^ 40 * 3483063 * 2
def baseEnd_3483063 : Nat := 1192323645927474155796127

theorem tailTrace_3483063 : CollatzResearch.WordTrace tailWord_3483063 prefixEnd_3483063 1192323645927474155796127 := by
  unfold tailWord_3483063
  simp only [CollatzResearch.WordTrace]
  refine ⟨127037744180465085646301843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84691829453643390430867895 127037744180465085646301843)
  ·
    refine ⟨190556616270697628469452765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127037744180465085646301843 190556616270697628469452765)
    ·
      refine ⟨71458731101511610676044787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190556616270697628469452765 71458731101511610676044787)
      ·
        refine ⟨107188096652267416014067181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71458731101511610676044787 107188096652267416014067181)
        ·
          refine ⟨40195536244600281005275193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107188096652267416014067181 40195536244600281005275193)
          ·
            refine ⟨30146652183450210753956395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40195536244600281005275193 30146652183450210753956395)
            ·
              refine ⟨45219978275175316130934593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30146652183450210753956395 45219978275175316130934593)
              ·
                refine ⟨33914983706381487098200945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45219978275175316130934593 33914983706381487098200945)
                ·
                  refine ⟨25436237779786115323650709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33914983706381487098200945 25436237779786115323650709)
                  ·
                    refine ⟨1192323645927474155796127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25436237779786115323650709 1192323645927474155796127)
                    ·
                      rfl

theorem cell22_3483063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3483063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483063 prefixEnd_3483063 := by exact prefixLift 3483063
  have htrace : WordTrace (prefixWord ++ tailWord_3483063) baseStart_3483063 baseEnd_3483063 := by
    simpa [prefixWord, tailWord_3483063, baseEnd_3483063] using wordTrace_append hprefix tailTrace_3483063
  have hstable : (prefixWord ++ tailWord_3483063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483063).length < 2 ^ (prefixWord ++ tailWord_3483063).sum := by decide
  have hdescent : baseEnd_3483063 < baseStart_3483063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483112 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_3483112 : Nat := 118140960795 + 3483112 * 2 ^ 59
def prefixEnd_3483112 : Nat := 4983230072969 + 3 ^ 40 * 3483112 * 2
def baseEnd_3483112 : Nat := 397446806542951453773659

theorem tailTrace_3483112 : CollatzResearch.WordTrace tailWord_3483112 prefixEnd_3483112 397446806542951453773659 := by
  unfold tailWord_3483112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63519765678643783507417795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84693020904858378009890393 63519765678643783507417795)
  ·
    refine ⟨95279648517965675261126693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63519765678643783507417795 95279648517965675261126693)
    ·
      refine ⟨17864934097118564111461255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95279648517965675261126693 17864934097118564111461255)
      ·
        refine ⟨26797401145677846167191883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17864934097118564111461255 26797401145677846167191883)
        ·
          refine ⟨40196101718516769250787825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26797401145677846167191883 40196101718516769250787825)
          ·
            refine ⟨30147076288887576938090869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40196101718516769250787825 30147076288887576938090869)
            ·
              refine ⟨2826288402083210337946019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30147076288887576938090869 2826288402083210337946019)
              ·
                refine ⟨4239432603124815506919029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826288402083210337946019 4239432603124815506919029)
                ·
                  refine ⟨397446806542951453773659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239432603124815506919029 397446806542951453773659)
                  ·
                    rfl

theorem cell22_3483112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_3483112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483112 prefixEnd_3483112 := by exact prefixLift 3483112
  have htrace : WordTrace (prefixWord ++ tailWord_3483112) baseStart_3483112 baseEnd_3483112 := by
    simpa [prefixWord, tailWord_3483112, baseEnd_3483112] using wordTrace_append hprefix tailTrace_3483112
  have hstable : (prefixWord ++ tailWord_3483112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483112).length < 2 ^ (prefixWord ++ tailWord_3483112).sum := by decide
  have hdescent : baseEnd_3483112 < baseStart_3483112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483123 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 8]
def baseStart_3483123 : Nat := 118140960795 + 3483123 * 2 ^ 59
def prefixEnd_3483123 : Nat := 4983230072969 + 3 ^ 40 * 3483123 * 2
def baseEnd_3483123 : Nat := 397448061717884666431981

theorem tailTrace_3483123 : CollatzResearch.WordTrace tailWord_3483123 prefixEnd_3483123 397448061717884666431981 := by
  unfold tailWord_3483123
  simp only [CollatzResearch.WordTrace]
  refine ⟨127039932560247715893486023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84693288373498477262324015 127039932560247715893486023)
  ·
    refine ⟨190559898840371573840229035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127039932560247715893486023 190559898840371573840229035)
    ·
      refine ⟨285839848260557360760343553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190559898840371573840229035 285839848260557360760343553)
      ·
        refine ⟨214379886195418020570257665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285839848260557360760343553 214379886195418020570257665)
        ·
          refine ⟨160784914646563515427693249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214379886195418020570257665 160784914646563515427693249)
          ·
            refine ⟨120588685984922636570769937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160784914646563515427693249 120588685984922636570769937)
            ·
              refine ⟨90441514488691977428077453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120588685984922636570769937 90441514488691977428077453)
              ·
                refine ⟨33915567933259491535529045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90441514488691977428077453 33915567933259491535529045)
                ·
                  refine ⟨397448061717884666431981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33915567933259491535529045 397448061717884666431981)
                  ·
                    rfl

theorem cell22_3483123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_3483123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483123 prefixEnd_3483123 := by exact prefixLift 3483123
  have htrace : WordTrace (prefixWord ++ tailWord_3483123) baseStart_3483123 baseEnd_3483123 := by
    simpa [prefixWord, tailWord_3483123, baseEnd_3483123] using wordTrace_append hprefix tailTrace_3483123
  have hstable : (prefixWord ++ tailWord_3483123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483123).length < 2 ^ (prefixWord ++ tailWord_3483123).sum := by decide
  have hdescent : baseEnd_3483123 < baseStart_3483123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483157 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 6]
def baseStart_3483157 : Nat := 118140960795 + 3483157 * 2 ^ 59
def prefixEnd_3483157 : Nat := 4983230072969 + 3 ^ 40 * 3483157 * 2
def baseEnd_3483157 : Nat := 397451941349496414648613

theorem tailTrace_3483157 : CollatzResearch.WordTrace tailWord_3483157 prefixEnd_3483157 397451941349496414648613 := by
  unfold tailWord_3483157
  simp only [CollatzResearch.WordTrace]
  refine ⟨127041172642124539700223725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84694115094749693133482483 127041172642124539700223725)
  ·
    refine ⟨47640439740796702387583897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127041172642124539700223725 47640439740796702387583897)
    ·
      refine ⟨35730329805597526790687923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47640439740796702387583897 35730329805597526790687923)
      ·
        refine ⟨53595494708396290186031885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35730329805597526790687923 53595494708396290186031885)
        ·
          refine ⟨20098310515648608819761957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53595494708396290186031885 20098310515648608819761957)
          ·
            refine ⟨3768433221684114153705367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20098310515648608819761957 3768433221684114153705367)
            ·
              refine ⟨5652649832526171230558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768433221684114153705367 5652649832526171230558051)
              ·
                refine ⟨8478974748789256845837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5652649832526171230558051 8478974748789256845837077)
                ·
                  refine ⟨397451941349496414648613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8478974748789256845837077 397451941349496414648613)
                  ·
                    rfl

theorem cell22_3483157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_3483157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483157 prefixEnd_3483157 := by exact prefixLift 3483157
  have htrace : WordTrace (prefixWord ++ tailWord_3483157) baseStart_3483157 baseEnd_3483157 := by
    simpa [prefixWord, tailWord_3483157, baseEnd_3483157] using wordTrace_append hprefix tailTrace_3483157
  have hstable : (prefixWord ++ tailWord_3483157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483157).length < 2 ^ (prefixWord ++ tailWord_3483157).sum := by decide
  have hdescent : baseEnd_3483157 < baseStart_3483157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483170 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3483170 : Nat := 118140960795 + 3483170 * 2 ^ 59
def prefixEnd_3483170 : Nat := 4983230072969 + 3 ^ 40 * 3483170 * 2
def baseEnd_3483170 : Nat := 1192360274214161543370799

theorem tailTrace_3483170 : CollatzResearch.WordTrace tailWord_3483170 prefixEnd_3483170 1192360274214161543370799 := by
  unfold tailWord_3483170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31760411697769360730111741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84694431194051628613631309 31760411697769360730111741)
  ·
    refine ⟨11910154386663510273791903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31760411697769360730111741 11910154386663510273791903)
    ·
      refine ⟨17865231579995265410687855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11910154386663510273791903 17865231579995265410687855)
      ·
        refine ⟨26797847369992898116031783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17865231579995265410687855 26797847369992898116031783)
        ·
          refine ⟨40196771054989347174047675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26797847369992898116031783 40196771054989347174047675)
          ·
            refine ⟨60295156582484020761071513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40196771054989347174047675 60295156582484020761071513)
            ·
              refine ⟨45221367436863015570803635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60295156582484020761071513 45221367436863015570803635)
              ·
                refine ⟨67832051155294523356205453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45221367436863015570803635 67832051155294523356205453)
                ·
                  refine ⟨25437019183235446258577045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67832051155294523356205453 25437019183235446258577045)
                  ·
                    refine ⟨1192360274214161543370799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25437019183235446258577045 1192360274214161543370799)
                    ·
                      rfl

theorem cell22_3483170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3483170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483170 prefixEnd_3483170 := by exact prefixLift 3483170
  have htrace : WordTrace (prefixWord ++ tailWord_3483170) baseStart_3483170 baseEnd_3483170 := by
    simpa [prefixWord, tailWord_3483170, baseEnd_3483170] using wordTrace_append hprefix tailTrace_3483170
  have hstable : (prefixWord ++ tailWord_3483170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483170).length < 2 ^ (prefixWord ++ tailWord_3483170).sum := by decide
  have hdescent : baseEnd_3483170 < baseStart_3483170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483176 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3483176 : Nat := 118140960795 + 3483176 * 2 ^ 59
def prefixEnd_3483176 : Nat := 4983230072969 + 3 ^ 40 * 3483176 * 2
def baseEnd_3483176 : Nat := 1192362328136779527720781

theorem tailTrace_3483176 : CollatzResearch.WordTrace tailWord_3483176 prefixEnd_3483176 1192362328136779527720781 := by
  unfold tailWord_3483176
  simp only [CollatzResearch.WordTrace]
  refine ⟨63520932814527852972582691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84694577086037137296776921 63520932814527852972582691)
  ·
    refine ⟨95281399221791779458874037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63520932814527852972582691 95281399221791779458874037)
    ·
      refine ⟨8932631177042979324269441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95281399221791779458874037 8932631177042979324269441)
      ·
        refine ⟨6699473382782234493202081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8932631177042979324269441 6699473382782234493202081)
        ·
          refine ⟨5024605037086675869901561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699473382782234493202081 5024605037086675869901561)
          ·
            refine ⟨3768453777815006902426171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5024605037086675869901561 3768453777815006902426171)
            ·
              refine ⟨5652680666722510353639257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768453777815006902426171 5652680666722510353639257)
              ·
                refine ⟨4239510500041882765229443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5652680666722510353639257 4239510500041882765229443)
                ·
                  refine ⟨6359265750062824147844165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4239510500041882765229443 6359265750062824147844165)
                  ·
                    refine ⟨1192362328136779527720781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359265750062824147844165 1192362328136779527720781)
                    ·
                      rfl

theorem cell22_3483176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3483176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483176 prefixEnd_3483176 := by exact prefixLift 3483176
  have htrace : WordTrace (prefixWord ++ tailWord_3483176) baseStart_3483176 baseEnd_3483176 := by
    simpa [prefixWord, tailWord_3483176, baseEnd_3483176] using wordTrace_append hprefix tailTrace_3483176
  have hstable : (prefixWord ++ tailWord_3483176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483176).length < 2 ^ (prefixWord ++ tailWord_3483176).sum := by decide
  have hdescent : baseEnd_3483176 < baseStart_3483176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483187 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_3483187 : Nat := 118140960795 + 3483187 * 2 ^ 59
def prefixEnd_3483187 : Nat := 4983230072969 + 3 ^ 40 * 3483187 * 2
def baseEnd_3483187 : Nat := 1192366093661579165695747

theorem tailTrace_3483187 : CollatzResearch.WordTrace tailWord_3483187 prefixEnd_3483187 1192366093661579165695747 := by
  unfold tailWord_3483187
  simp only [CollatzResearch.WordTrace]
  refine ⟨127042266832015854823815815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84694844554677236549210543 127042266832015854823815815)
  ·
    refine ⟨190563400248023782235723723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127042266832015854823815815 190563400248023782235723723)
    ·
      refine ⟨285845100372035673353585585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190563400248023782235723723 285845100372035673353585585)
      ·
        refine ⟨214383825279026755015189189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285845100372035673353585585 214383825279026755015189189)
        ·
          refine ⟨40196967239817516565347973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214383825279026755015189189 40196967239817516565347973)
          ·
            refine ⟨7536931357465784356002745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40196967239817516565347973 7536931357465784356002745)
            ·
              refine ⟨5652698518099338267002059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536931357465784356002745 5652698518099338267002059)
              ·
                refine ⟨8479047777149007400503089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5652698518099338267002059 8479047777149007400503089)
                ·
                  refine ⟨6359285832861755550377317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479047777149007400503089 6359285832861755550377317)
                  ·
                    refine ⟨1192366093661579165695747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359285832861755550377317 1192366093661579165695747)
                    ·
                      rfl

theorem cell22_3483187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_3483187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483187 prefixEnd_3483187 := by exact prefixLift 3483187
  have htrace : WordTrace (prefixWord ++ tailWord_3483187) baseStart_3483187 baseEnd_3483187 := by
    simpa [prefixWord, tailWord_3483187, baseEnd_3483187] using wordTrace_append hprefix tailTrace_3483187
  have hstable : (prefixWord ++ tailWord_3483187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483187).length < 2 ^ (prefixWord ++ tailWord_3483187).sum := by decide
  have hdescent : baseEnd_3483187 < baseStart_3483187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483217 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_3483217 : Nat := 118140960795 + 3483217 * 2 ^ 59
def prefixEnd_3483217 : Nat := 4983230072969 + 3 ^ 40 * 3483217 * 2
def baseEnd_3483217 : Nat := 1192376363274669087445655

theorem tailTrace_3483217 : CollatzResearch.WordTrace tailWord_3483217 prefixEnd_3483217 1192376363274669087445655 := by
  unfold tailWord_3483217
  simp only [CollatzResearch.WordTrace]
  refine ⟨127043361021907169947407905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84695574014604779964938603 127043361021907169947407905)
  ·
    refine ⟨95282520766430377460555929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127043361021907169947407905 95282520766430377460555929)
    ·
      refine ⟨71461890574822783095416947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95282520766430377460555929 71461890574822783095416947)
      ·
        refine ⟨107192835862234174643125421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71461890574822783095416947 107192835862234174643125421)
        ·
          refine ⟨40197313448337815491172033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107192835862234174643125421 40197313448337815491172033)
          ·
            refine ⟨30147985086253361618379025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40197313448337815491172033 30147985086253361618379025)
            ·
              refine ⟨22610988814690021213784269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30147985086253361618379025 22610988814690021213784269)
              ·
                refine ⟨8479120805508757955169101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22610988814690021213784269 8479120805508757955169101)
                ·
                  refine ⟨3179670302065784233188413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8479120805508757955169101 3179670302065784233188413)
                  ·
                    refine ⟨1192376363274669087445655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179670302065784233188413 1192376363274669087445655)
                    ·
                      rfl

theorem cell22_3483217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_3483217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483217 prefixEnd_3483217 := by exact prefixLift 3483217
  have htrace : WordTrace (prefixWord ++ tailWord_3483217) baseStart_3483217 baseEnd_3483217 := by
    simpa [prefixWord, tailWord_3483217, baseEnd_3483217] using wordTrace_append hprefix tailTrace_3483217
  have hstable : (prefixWord ++ tailWord_3483217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483217).length < 2 ^ (prefixWord ++ tailWord_3483217).sum := by decide
  have hdescent : baseEnd_3483217 < baseStart_3483217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483305 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_3483305 : Nat := 118140960795 + 3483305 * 2 ^ 59
def prefixEnd_3483305 : Nat := 4983230072969 + 3 ^ 40 * 3483305 * 2
def baseEnd_3483305 : Nat := 1192406487473066191245385

theorem tailTrace_3483305 : CollatzResearch.WordTrace tailWord_3483305 prefixEnd_3483305 1192406487473066191245385 := by
  unfold tailWord_3483305
  simp only [CollatzResearch.WordTrace]
  refine ⟨127046570645588360976611369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84697713763725573984407579 127046570645588360976611369)
  ·
    refine ⟨95284927984191270732458527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127046570645588360976611369 95284927984191270732458527)
    ·
      refine ⟨142927391976286906098687791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95284927984191270732458527 142927391976286906098687791)
      ·
        refine ⟨214391087964430359148031687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142927391976286906098687791 214391087964430359148031687)
        ·
          refine ⟨321586631946645538722047531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214391087964430359148031687 321586631946645538722047531)
          ·
            refine ⟨482379947919968308083071297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321586631946645538722047531 482379947919968308083071297)
            ·
              refine ⟨361784960939976231062303473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482379947919968308083071297 361784960939976231062303473)
              ·
                refine ⟨271338720704982173296727605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361784960939976231062303473 271338720704982173296727605)
                ·
                  refine ⟨25438005066092078746568213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271338720704982173296727605 25438005066092078746568213)
                  ·
                    refine ⟨1192406487473066191245385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25438005066092078746568213 1192406487473066191245385)
                    ·
                      rfl

theorem cell22_3483305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_3483305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483305 prefixEnd_3483305 := by exact prefixLift 3483305
  have htrace : WordTrace (prefixWord ++ tailWord_3483305) baseStart_3483305 baseEnd_3483305 := by
    simpa [prefixWord, tailWord_3483305, baseEnd_3483305] using wordTrace_append hprefix tailTrace_3483305
  have hstable : (prefixWord ++ tailWord_3483305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483305).length < 2 ^ (prefixWord ++ tailWord_3483305).sum := by decide
  have hdescent : baseEnd_3483305 < baseStart_3483305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483322 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_3483322 : Nat := 118140960795 + 3483322 * 2 ^ 59
def prefixEnd_3483322 : Nat := 4983230072969 + 3 ^ 40 * 3483322 * 2
def baseEnd_3483322 : Nat := 1192412306920483813570333

theorem tailTrace_3483322 : CollatzResearch.WordTrace tailWord_3483322 prefixEnd_3483322 1192412306920483813570333 := by
  unfold tailWord_3483322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31761797671631693219995055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84698127124351181919986813 31761797671631693219995055)
  ·
    refine ⟨47642696507447539829992583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31761797671631693219995055 47642696507447539829992583)
    ·
      refine ⟨71464044761171309744988875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47642696507447539829992583 71464044761171309744988875)
      ·
        refine ⟨107196067141756964617483313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71464044761171309744988875 107196067141756964617483313)
        ·
          refine ⟨80397050356317723463112485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107196067141756964617483313 80397050356317723463112485)
          ·
            refine ⟨15074446941809573149333591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80397050356317723463112485 15074446941809573149333591)
            ·
              refine ⟨22611670412714359724000387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15074446941809573149333591 22611670412714359724000387)
              ·
                refine ⟨33917505619071539586000581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22611670412714359724000387 33917505619071539586000581)
                ·
                  refine ⟨6359532303575913672375109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33917505619071539586000581 6359532303575913672375109)
                  ·
                    refine ⟨1192412306920483813570333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359532303575913672375109 1192412306920483813570333)
                    ·
                      rfl

theorem cell22_3483322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_3483322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483322 prefixEnd_3483322 := by exact prefixLift 3483322
  have htrace : WordTrace (prefixWord ++ tailWord_3483322) baseStart_3483322 baseEnd_3483322 := by
    simpa [prefixWord, tailWord_3483322, baseEnd_3483322] using wordTrace_append hprefix tailTrace_3483322
  have hstable : (prefixWord ++ tailWord_3483322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483322).length < 2 ^ (prefixWord ++ tailWord_3483322).sum := by decide
  have hdescent : baseEnd_3483322 < baseStart_3483322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483324 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_3483324 : Nat := 118140960795 + 3483324 * 2 ^ 59
def prefixEnd_3483324 : Nat := 4983230072969 + 3 ^ 40 * 3483324 * 2
def baseEnd_3483324 : Nat := 1192412991561356475020327

theorem tailTrace_3483324 : CollatzResearch.WordTrace tailWord_3483324 prefixEnd_3483324 1192412991561356475020327 := by
  unfold tailWord_3483324
  simp only [CollatzResearch.WordTrace]
  refine ⟨63523631816259763610776513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84698175755013018147702017 63523631816259763610776513)
  ·
    refine ⟨47642723862194822708082385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63523631816259763610776513 47642723862194822708082385)
    ·
      refine ⟨35732042896646117031061789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47642723862194822708082385 35732042896646117031061789)
      ·
        refine ⟨13399516086242293886648171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35732042896646117031061789 13399516086242293886648171)
        ·
          refine ⟨20099274129363440829972257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13399516086242293886648171 20099274129363440829972257)
          ·
            refine ⟨15074455597022580622479193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20099274129363440829972257 15074455597022580622479193)
            ·
              refine ⟨11305841697766935466859395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15074455597022580622479193 11305841697766935466859395)
              ·
                refine ⟨16958762546650403200289093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11305841697766935466859395 16958762546650403200289093)
                ·
                  refine ⟨3179767977496950600054205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16958762546650403200289093 3179767977496950600054205)
                  ·
                    refine ⟨1192412991561356475020327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179767977496950600054205 1192412991561356475020327)
                    ·
                      rfl

theorem cell22_3483324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_3483324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483324 prefixEnd_3483324 := by exact prefixLift 3483324
  have htrace : WordTrace (prefixWord ++ tailWord_3483324) baseStart_3483324 baseEnd_3483324 := by
    simpa [prefixWord, tailWord_3483324, baseEnd_3483324] using wordTrace_append hprefix tailTrace_3483324
  have hstable : (prefixWord ++ tailWord_3483324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483324).length < 2 ^ (prefixWord ++ tailWord_3483324).sum := by decide
  have hdescent : baseEnd_3483324 < baseStart_3483324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483459 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_3483459 : Nat := 118140960795 + 3483459 * 2 ^ 59
def prefixEnd_3483459 : Nat := 4983230072969 + 3 ^ 40 * 3483459 * 2
def baseEnd_3483459 : Nat := 1192459204820261122894913

theorem tailTrace_3483459 : CollatzResearch.WordTrace tailWord_3483459 prefixEnd_3483459 1192459204820261122894913 := by
  unfold tailWord_3483459
  simp only [CollatzResearch.WordTrace]
  refine ⟨127052187487030445277717431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84701458324686963518478287 127052187487030445277717431)
  ·
    refine ⟨190578281230545667916576147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127052187487030445277717431 190578281230545667916576147)
    ·
      refine ⟨285867421845818501874864221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190578281230545667916576147 285867421845818501874864221)
      ·
        refine ⟨107200283192181938203074083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285867421845818501874864221 107200283192181938203074083)
        ·
          refine ⟨160800424788272907304611125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107200283192181938203074083 160800424788272907304611125)
          ·
            refine ⟨15075039823900585059807293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160800424788272907304611125 15075039823900585059807293)
            ·
              refine ⟨5653139933962719397427735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15075039823900585059807293 5653139933962719397427735)
              ·
                refine ⟨8479709900944079096141603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653139933962719397427735 8479709900944079096141603)
                ·
                  refine ⟨12719564851416118644212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8479709900944079096141603 12719564851416118644212405)
                  ·
                    refine ⟨1192459204820261122894913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12719564851416118644212405 1192459204820261122894913)
                    ·
                      rfl

theorem cell22_3483459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_3483459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483459 prefixEnd_3483459 := by exact prefixLift 3483459
  have htrace : WordTrace (prefixWord ++ tailWord_3483459) baseStart_3483459 baseEnd_3483459 := by
    simpa [prefixWord, tailWord_3483459, baseEnd_3483459] using wordTrace_append hprefix tailTrace_3483459
  have hstable : (prefixWord ++ tailWord_3483459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483459).length < 2 ^ (prefixWord ++ tailWord_3483459).sum := by decide
  have hdescent : baseEnd_3483459 < baseStart_3483459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483474 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3483474 : Nat := 118140960795 + 3483474 * 2 ^ 59
def prefixEnd_3483474 : Nat := 4983230072969 + 3 ^ 40 * 3483474 * 2
def baseEnd_3483474 : Nat := 1192464339626806083769867

theorem tailTrace_3483474 : CollatzResearch.WordTrace tailWord_3483474 prefixEnd_3483474 1192464339626806083769867 := by
  unfold tailWord_3483474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763183645494025709878369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84701823054650735226342317 31763183645494025709878369)
  ·
    refine ⟨23822387734120519282408777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31763183645494025709878369 23822387734120519282408777)
    ·
      refine ⟨17866790800590389461806583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23822387734120519282408777 17866790800590389461806583)
      ·
        refine ⟨26800186200885584192709875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17866790800590389461806583 26800186200885584192709875)
        ·
          refine ⟨40200279301328376289064813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26800186200885584192709875 40200279301328376289064813)
          ·
            refine ⟨15075104737998141108399305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40200279301328376289064813 15075104737998141108399305)
            ·
              refine ⟨11306328553498605831299479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075104737998141108399305 11306328553498605831299479)
              ·
                refine ⟨16959492830247908746949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306328553498605831299479 16959492830247908746949219)
                ·
                  refine ⟨25439239245371863120423829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16959492830247908746949219 25439239245371863120423829)
                  ·
                    refine ⟨1192464339626806083769867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25439239245371863120423829 1192464339626806083769867)
                    ·
                      rfl

theorem cell22_3483474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3483474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483474 prefixEnd_3483474 := by exact prefixLift 3483474
  have htrace : WordTrace (prefixWord ++ tailWord_3483474) baseStart_3483474 baseEnd_3483474 := by
    simpa [prefixWord, tailWord_3483474, baseEnd_3483474] using wordTrace_append hprefix tailTrace_3483474
  have hstable : (prefixWord ++ tailWord_3483474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483474).length < 2 ^ (prefixWord ++ tailWord_3483474).sum := by decide
  have hdescent : baseEnd_3483474 < baseStart_3483474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483476 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3483476 : Nat := 118140960795 + 3483476 * 2 ^ 59
def prefixEnd_3483476 : Nat := 4983230072969 + 3 ^ 40 * 3483476 * 2
def baseEnd_3483476 : Nat := 1192465024267678745219861

theorem tailTrace_3483476 : CollatzResearch.WordTrace tailWord_3483476 prefixEnd_3483476 1192465024267678745219861 := by
  unfold tailWord_3483476
  simp only [CollatzResearch.WordTrace]
  refine ⟨63526403763984428590543141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84701871685312571454057521 63526403763984428590543141)
  ·
    refine ⟨11911200705747080360726839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63526403763984428590543141 11911200705747080360726839)
    ·
      refine ⟨17866801058620620541090259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911200705747080360726839 17866801058620620541090259)
      ·
        refine ⟨26800201587930930811635389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17866801058620620541090259 26800201587930930811635389)
        ·
          refine ⟨10050075595474099054363271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26800201587930930811635389 10050075595474099054363271)
          ·
            refine ⟨15075113393211148581544907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050075595474099054363271 15075113393211148581544907)
            ·
              refine ⟨22612670089816722872317361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15075113393211148581544907 22612670089816722872317361)
              ·
                refine ⟨16959502567362542154238021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22612670089816722872317361 16959502567362542154238021)
                ·
                  refine ⟨3179906731380476653919629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16959502567362542154238021 3179906731380476653919629)
                  ·
                    refine ⟨1192465024267678745219861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179906731380476653919629 1192465024267678745219861)
                    ·
                      rfl

theorem cell22_3483476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3483476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483476 prefixEnd_3483476 := by exact prefixLift 3483476
  have htrace : WordTrace (prefixWord ++ tailWord_3483476) baseStart_3483476 baseEnd_3483476 := by
    simpa [prefixWord, tailWord_3483476, baseEnd_3483476] using wordTrace_append hprefix tailTrace_3483476
  have hstable : (prefixWord ++ tailWord_3483476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483476).length < 2 ^ (prefixWord ++ tailWord_3483476).sum := by decide
  have hdescent : baseEnd_3483476 < baseStart_3483476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483491 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_3483491 : Nat := 118140960795 + 3483491 * 2 ^ 59
def prefixEnd_3483491 : Nat := 4983230072969 + 3 ^ 40 * 3483491 * 2
def baseEnd_3483491 : Nat := 1192470159074223706094815

theorem tailTrace_3483491 : CollatzResearch.WordTrace tailWord_3483491 prefixEnd_3483491 1192470159074223706094815 := by
  unfold tailWord_3483491
  simp only [CollatzResearch.WordTrace]
  refine ⟨127053354622914514742882327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84702236415276343161921551 127053354622914514742882327)
  ·
    refine ⟨190580031934371772114323491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127053354622914514742882327 190580031934371772114323491)
    ·
      refine ⟨285870047901557658171485237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190580031934371772114323491 285870047901557658171485237)
      ·
        refine ⟨26800316990771030453576741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285870047901557658171485237 26800316990771030453576741)
        ·
          refine ⟨5025059435769568210045639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26800316990771030453576741 5025059435769568210045639)
          ·
            refine ⟨7537589153654352315068459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025059435769568210045639 7537589153654352315068459)
            ·
              refine ⟨11306383730481528472602689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537589153654352315068459 11306383730481528472602689)
              ·
                refine ⟨8479787797861146354452017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11306383730481528472602689 8479787797861146354452017)
                ·
                  refine ⟨6359840848395859765839013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8479787797861146354452017 6359840848395859765839013)
                  ·
                    refine ⟨1192470159074223706094815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6359840848395859765839013 1192470159074223706094815)
                    ·
                      rfl

theorem cell22_3483491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_3483491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483491 prefixEnd_3483491 := by exact prefixLift 3483491
  have htrace : WordTrace (prefixWord ++ tailWord_3483491) baseStart_3483491 baseEnd_3483491 := by
    simpa [prefixWord, tailWord_3483491, baseEnd_3483491] using wordTrace_append hprefix tailTrace_3483491
  have hstable : (prefixWord ++ tailWord_3483491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483491).length < 2 ^ (prefixWord ++ tailWord_3483491).sum := by decide
  have hdescent : baseEnd_3483491 < baseStart_3483491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483510 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3483510 : Nat := 118140960795 + 3483510 * 2 ^ 59
def prefixEnd_3483510 : Nat := 4983230072969 + 3 ^ 40 * 3483510 * 2
def baseEnd_3483510 : Nat := 1192476663162513989869757

theorem tailTrace_3483510 : CollatzResearch.WordTrace tailWord_3483510 prefixEnd_3483510 1192476663162513989869757 := by
  unfold tailWord_3483510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940877975615355061738999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84702698406563787325215989 7940877975615355061738999)
  ·
    refine ⟨11911316963423032592608499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7940877975615355061738999 11911316963423032592608499)
    ·
      refine ⟨17866975445134548888912749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11911316963423032592608499 17866975445134548888912749)
      ·
        refine ⟨6700115791925455833342281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17866975445134548888912749 6700115791925455833342281)
        ·
          refine ⟨5025086843944091875006711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6700115791925455833342281 5025086843944091875006711)
          ·
            refine ⟨7537630265916137812510067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025086843944091875006711 7537630265916137812510067)
            ·
              refine ⟨11306445398874206718765101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537630265916137812510067 11306445398874206718765101)
              ·
                refine ⟨4239917024577827519536913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11306445398874206718765101 4239917024577827519536913)
                ·
                  refine ⟨3179937768433370639652685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4239917024577827519536913 3179937768433370639652685)
                  ·
                    refine ⟨1192476663162513989869757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3179937768433370639652685 1192476663162513989869757)
                    ·
                      rfl

theorem cell22_3483510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3483510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483510 prefixEnd_3483510 := by exact prefixLift 3483510
  have htrace : WordTrace (prefixWord ++ tailWord_3483510) baseStart_3483510 baseEnd_3483510 := by
    simpa [prefixWord, tailWord_3483510, baseEnd_3483510] using wordTrace_append hprefix tailTrace_3483510
  have hstable : (prefixWord ++ tailWord_3483510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483510).length < 2 ^ (prefixWord ++ tailWord_3483510).sum := by decide
  have hdescent : baseEnd_3483510 < baseStart_3483510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483581 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3483581 : Nat := 118140960795 + 3483581 * 2 ^ 59
def prefixEnd_3483581 : Nat := 4983230072969 + 3 ^ 40 * 3483581 * 2
def baseEnd_3483581 : Nat := 1192500967913493471344539

theorem tailTrace_3483581 : CollatzResearch.WordTrace tailWord_3483581 prefixEnd_3483581 1192500967913493471344539 := by
  unfold tailWord_3483581
  simp only [CollatzResearch.WordTrace]
  refine ⟨127056637192588460113658597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84704424795058973409105731 127056637192588460113658597)
  ·
    refine ⟨23823119473610336271310987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127056637192588460113658597 23823119473610336271310987)
    ·
      refine ⟨35734679210415504406966481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23823119473610336271310987 35734679210415504406966481)
      ·
        refine ⟨26801009407811628305224861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35734679210415504406966481 26801009407811628305224861)
        ·
          refine ⟨10050378527929360614459323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26801009407811628305224861 10050378527929360614459323)
          ·
            refine ⟨15075567791894040921688985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10050378527929360614459323 15075567791894040921688985)
            ·
              refine ⟨11306675843920530691266739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15075567791894040921688985 11306675843920530691266739)
              ·
                refine ⟨16960013765880796036900109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11306675843920530691266739 16960013765880796036900109)
                ·
                  refine ⟨6360005162205298513837541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16960013765880796036900109 6360005162205298513837541)
                  ·
                    refine ⟨1192500967913493471344539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360005162205298513837541 1192500967913493471344539)
                    ·
                      rfl

theorem cell22_3483581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3483581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483581 prefixEnd_3483581 := by exact prefixLift 3483581
  have htrace : WordTrace (prefixWord ++ tailWord_3483581) baseStart_3483581 baseEnd_3483581 := by
    simpa [prefixWord, tailWord_3483581, baseEnd_3483581] using wordTrace_append hprefix tailTrace_3483581
  have hstable : (prefixWord ++ tailWord_3483581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483581).length < 2 ^ (prefixWord ++ tailWord_3483581).sum := by decide
  have hdescent : baseEnd_3483581 < baseStart_3483581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483613 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3483613 : Nat := 118140960795 + 3483613 * 2 ^ 59
def prefixEnd_3483613 : Nat := 4983230072969 + 3 ^ 40 * 3483613 * 2
def baseEnd_3483613 : Nat := 397503974055818684848147

theorem tailTrace_3483613 : CollatzResearch.WordTrace tailWord_3483613 prefixEnd_3483613 397503974055818684848147 := by
  unfold tailWord_3483613
  simp only [CollatzResearch.WordTrace]
  refine ⟨127057804328472529578823493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84705202885648353052548995 127057804328472529578823493)
  ·
    refine ⟨23823338311588599296029405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127057804328472529578823493 23823338311588599296029405)
    ·
      refine ⟨8933751866845724736011027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23823338311588599296029405 8933751866845724736011027)
      ·
        refine ⟨13400627800268587104016541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933751866845724736011027 13400627800268587104016541)
        ·
          refine ⟨5025235425100720164006203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13400627800268587104016541 5025235425100720164006203)
          ·
            refine ⟨7537853137651080246009305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025235425100720164006203 7537853137651080246009305)
            ·
              refine ⟨5653389853238310184506979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7537853137651080246009305 5653389853238310184506979)
              ·
                refine ⟨8480084779857465276760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653389853238310184506979 8480084779857465276760469)
                ·
                  refine ⟨397503974055818684848147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8480084779857465276760469 397503974055818684848147)
                  ·
                    rfl

theorem cell22_3483613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3483613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483613 prefixEnd_3483613 := by exact prefixLift 3483613
  have htrace : WordTrace (prefixWord ++ tailWord_3483613) baseStart_3483613 baseEnd_3483613 := by
    simpa [prefixWord, tailWord_3483613, baseEnd_3483613] using wordTrace_append hprefix tailTrace_3483613
  have hstable : (prefixWord ++ tailWord_3483613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483613).length < 2 ^ (prefixWord ++ tailWord_3483613).sum := by decide
  have hdescent : baseEnd_3483613 < baseStart_3483613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483624 : List Nat := [2, 1, 4, 1, 1, 1, 1, 11]
def baseStart_3483624 : Nat := 118140960795 + 3483624 * 2 ^ 59
def prefixEnd_3483624 : Nat := 4983230072969 + 3 ^ 40 * 3483624 * 2
def baseEnd_3483624 : Nat := 132501743076917299168823

theorem tailTrace_3483624 : CollatzResearch.WordTrace tailWord_3483624 prefixEnd_3483624 132501743076917299168823 := by
  unfold tailWord_3483624
  simp only [CollatzResearch.WordTrace]
  refine ⟨63529102765716339228736963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84705470354288452304982617 63529102765716339228736963)
  ·
    refine ⟨95293654148574508843105445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63529102765716339228736963 95293654148574508843105445)
    ·
      refine ⟨17867560152857720408082271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95293654148574508843105445 17867560152857720408082271)
      ·
        refine ⟨26801340229286580612123407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17867560152857720408082271 26801340229286580612123407)
        ·
          refine ⟨40202010343929870918185111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26801340229286580612123407 40202010343929870918185111)
          ·
            refine ⟨60303015515894806377277667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40202010343929870918185111 60303015515894806377277667)
            ·
              refine ⟨90454523273842209565916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60303015515894806377277667 90454523273842209565916501)
              ·
                refine ⟨132501743076917299168823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90454523273842209565916501 132501743076917299168823)
                ·
                  rfl

theorem cell22_3483624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_3483624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483624 prefixEnd_3483624 := by exact prefixLift 3483624
  have htrace : WordTrace (prefixWord ++ tailWord_3483624) baseStart_3483624 baseEnd_3483624 := by
    simpa [prefixWord, tailWord_3483624, baseEnd_3483624] using wordTrace_append hprefix tailTrace_3483624
  have hstable : (prefixWord ++ tailWord_3483624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483624).length < 2 ^ (prefixWord ++ tailWord_3483624).sum := by decide
  have hdescent : baseEnd_3483624 < baseStart_3483624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483641 : List Nat := [1, 2, 1, 3, 1, 4, 4, 6]
def baseStart_3483641 : Nat := 118140960795 + 3483641 * 2 ^ 59
def prefixEnd_3483641 : Nat := 4983230072969 + 3 ^ 40 * 3483641 * 2
def baseEnd_3483641 : Nat := 132502389682185923871595

theorem tailTrace_3483641 : CollatzResearch.WordTrace tailWord_3483641 prefixEnd_3483641 132502389682185923871595 := by
  unfold tailWord_3483641
  simp only [CollatzResearch.WordTrace]
  refine ⟨127058825572371090360842777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84705883714914060240561851 127058825572371090360842777)
  ·
    refine ⟨95294119179278317770632083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127058825572371090360842777 95294119179278317770632083)
    ·
      refine ⟨142941178768917476655948125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95294119179278317770632083 142941178768917476655948125)
      ·
        refine ⟨53602942038344053745980547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142941178768917476655948125 53602942038344053745980547)
        ·
          refine ⟨80404413057516080618970821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53602942038344053745980547 80404413057516080618970821)
          ·
            refine ⟨15075827448284265116057029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80404413057516080618970821 15075827448284265116057029)
            ·
              refine ⟨2826717646553299709260693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15075827448284265116057029 2826717646553299709260693)
              ·
                refine ⟨132502389682185923871595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2826717646553299709260693 132502389682185923871595)
                ·
                  rfl

theorem cell22_3483641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 6].length) (baseStart_3483641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483641 prefixEnd_3483641 := by exact prefixLift 3483641
  have htrace : WordTrace (prefixWord ++ tailWord_3483641) baseStart_3483641 baseEnd_3483641 := by
    simpa [prefixWord, tailWord_3483641, baseEnd_3483641] using wordTrace_append hprefix tailTrace_3483641
  have hstable : (prefixWord ++ tailWord_3483641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483641).length < 2 ^ (prefixWord ++ tailWord_3483641).sum := by decide
  have hdescent : baseEnd_3483641 < baseStart_3483641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483658 : List Nat := [3, 1, 2, 2, 5, 1, 8]
def baseStart_3483658 : Nat := 118140960795 + 3483658 * 2 ^ 59
def prefixEnd_3483658 : Nat := 4983230072969 + 3 ^ 40 * 3483658 * 2
def baseEnd_3483658 : Nat := 44167678762484849524789

theorem tailTrace_3483658 : CollatzResearch.WordTrace tailWord_3483658 prefixEnd_3483658 44167678762484849524789 := by
  unfold tailWord_3483658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764861403327375566052907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84706297075539668176141085 31764861403327375566052907)
  ·
    refine ⟨47647292104991063349079361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31764861403327375566052907 47647292104991063349079361)
    ·
      refine ⟨35735469078743297511809521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47647292104991063349079361 35735469078743297511809521)
      ·
        refine ⟨26801601809057473133857141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35735469078743297511809521 26801601809057473133857141)
        ·
          refine ⟨2512650169599138106299107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26801601809057473133857141 2512650169599138106299107)
          ·
            refine ⟨3768975254398707159448661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512650169599138106299107 3768975254398707159448661)
            ·
              refine ⟨44167678762484849524789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3768975254398707159448661 44167678762484849524789)
              ·
                rfl

theorem cell22_3483658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 8].length) (baseStart_3483658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483658 prefixEnd_3483658 := by exact prefixLift 3483658
  have htrace : WordTrace (prefixWord ++ tailWord_3483658) baseStart_3483658 baseEnd_3483658 := by
    simpa [prefixWord, tailWord_3483658, baseEnd_3483658] using wordTrace_append hprefix tailTrace_3483658
  have hstable : (prefixWord ++ tailWord_3483658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483658).length < 2 ^ (prefixWord ++ tailWord_3483658).sum := by decide
  have hdescent : baseEnd_3483658 < baseStart_3483658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483761 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3483761 : Nat := 118140960795 + 3483761 * 2 ^ 59
def prefixEnd_3483761 : Nat := 4983230072969 + 3 ^ 40 * 3483761 * 2
def baseEnd_3483761 : Nat := 1192562585592033001843987

theorem tailTrace_3483761 : CollatzResearch.WordTrace tailWord_3483761 prefixEnd_3483761 1192562585592033001843987 := by
  unfold tailWord_3483761
  simp only [CollatzResearch.WordTrace]
  refine ⟨127063202331936350855211137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84708801554624233903474091 127063202331936350855211137)
  ·
    refine ⟨95297401748952263141408353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127063202331936350855211137 95297401748952263141408353)
    ·
      refine ⟨71473051311714197356056265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95297401748952263141408353 71473051311714197356056265)
      ·
        refine ⟨53604788483785648017042199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71473051311714197356056265 53604788483785648017042199)
        ·
          refine ⟨80407182725678472025563299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53604788483785648017042199 80407182725678472025563299)
          ·
            refine ⟨120610774088517708038344949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80407182725678472025563299 120610774088517708038344949)
            ·
              refine ⟨11307260070798535128594839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120610774088517708038344949 11307260070798535128594839)
              ·
                refine ⟨16960890106197802692892259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307260070798535128594839 16960890106197802692892259)
                ·
                  refine ⟨25441335159296704039338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16960890106197802692892259 25441335159296704039338389)
                  ·
                    refine ⟨1192562585592033001843987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25441335159296704039338389 1192562585592033001843987)
                    ·
                      rfl

theorem cell22_3483761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3483761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483761 prefixEnd_3483761 := by exact prefixLift 3483761
  have htrace : WordTrace (prefixWord ++ tailWord_3483761) baseStart_3483761 baseEnd_3483761 := by
    simpa [prefixWord, tailWord_3483761, baseEnd_3483761] using wordTrace_append hprefix tailTrace_3483761
  have hstable : (prefixWord ++ tailWord_3483761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483761).length < 2 ^ (prefixWord ++ tailWord_3483761).sum := by decide
  have hdescent : baseEnd_3483761 < baseStart_3483761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483810 : List Nat := [3, 3, 1, 3, 1, 1, 4, 6]
def baseStart_3483810 : Nat := 118140960795 + 3483810 * 2 ^ 59
def prefixEnd_3483810 : Nat := 4983230072969 + 3 ^ 40 * 3483810 * 2
def baseEnd_3483810 : Nat := 132508817699268134152093

theorem tailTrace_3483810 : CollatzResearch.WordTrace tailWord_3483810 prefixEnd_3483810 132508817699268134152093 := by
  unfold tailWord_3483810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31766247377189708055936221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84709993005839221482496589 31766247377189708055936221)
  ·
    refine ⟨11912342766446140520976083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31766247377189708055936221 11912342766446140520976083)
    ·
      refine ⟨17868514149669210781464125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912342766446140520976083 17868514149669210781464125)
      ·
        refine ⟨6700692806125954043049047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17868514149669210781464125 6700692806125954043049047)
        ·
          refine ⟨10051039209188931064573571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700692806125954043049047 10051039209188931064573571)
          ·
            refine ⟨15076558813783396596860357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10051039209188931064573571 15076558813783396596860357)
            ·
              refine ⟨2826854777584386861911317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15076558813783396596860357 2826854777584386861911317)
              ·
                refine ⟨132508817699268134152093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2826854777584386861911317 132508817699268134152093)
                ·
                  rfl

theorem cell22_3483810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_3483810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483810 prefixEnd_3483810 := by exact prefixLift 3483810
  have htrace : WordTrace (prefixWord ++ tailWord_3483810) baseStart_3483810 baseEnd_3483810 := by
    simpa [prefixWord, tailWord_3483810, baseEnd_3483810] using wordTrace_append hprefix tailTrace_3483810
  have hstable : (prefixWord ++ tailWord_3483810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483810).length < 2 ^ (prefixWord ++ tailWord_3483810).sum := by decide
  have hdescent : baseEnd_3483810 < baseStart_3483810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483915 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 2, 3]
def baseStart_3483915 : Nat := 118140960795 + 3483915 * 2 ^ 59
def prefixEnd_3483915 : Nat := 4983230072969 + 3 ^ 40 * 3483915 * 2
def baseEnd_3483915 : Nat := 1192615302939227933493515

theorem tailTrace_3483915 : CollatzResearch.WordTrace tailWord_3483915 prefixEnd_3483915 1192615302939227933493515 := by
  unfold tailWord_3483915
  simp only [CollatzResearch.WordTrace]
  refine ⟨127068819173378435156317199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84712546115585623437544799 127068819173378435156317199)
  ·
    refine ⟨190603228760067652734475799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127068819173378435156317199 190603228760067652734475799)
    ·
      refine ⟨285904843140101479101713699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190603228760067652734475799 285904843140101479101713699)
      ·
        refine ⟨428857264710152218652570549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285904843140101479101713699 428857264710152218652570549)
        ·
          refine ⟨40205368566576770498678489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428857264710152218652570549 40205368566576770498678489)
          ·
            refine ⟨30154026424932577874008867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40205368566576770498678489 30154026424932577874008867)
            ·
              refine ⟨45231039637398866811013301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30154026424932577874008867 45231039637398866811013301)
              ·
                refine ⟨4240409966006143763532497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45231039637398866811013301 4240409966006143763532497)
                ·
                  refine ⟨3180307474504607822649373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240409966006143763532497 3180307474504607822649373)
                  ·
                    refine ⟨1192615302939227933493515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180307474504607822649373 1192615302939227933493515)
                    ·
                      rfl

theorem cell22_3483915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 3].length) (baseStart_3483915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483915 prefixEnd_3483915 := by exact prefixLift 3483915
  have htrace : WordTrace (prefixWord ++ tailWord_3483915) baseStart_3483915 baseEnd_3483915 := by
    simpa [prefixWord, tailWord_3483915, baseEnd_3483915] using wordTrace_append hprefix tailTrace_3483915
  have hstable : (prefixWord ++ tailWord_3483915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483915).length < 2 ^ (prefixWord ++ tailWord_3483915).sum := by decide
  have hdescent : baseEnd_3483915 < baseStart_3483915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483930 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_3483930 : Nat := 118140960795 + 3483930 * 2 ^ 59
def prefixEnd_3483930 : Nat := 4983230072969 + 3 ^ 40 * 3483930 * 2
def baseEnd_3483930 : Nat := 1192620437745772894368469

theorem tailTrace_3483930 : CollatzResearch.WordTrace tailWord_3483930 prefixEnd_3483930 1192620437745772894368469 := by
  unfold tailWord_3483930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31767341567081023179528311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84712910845549395145408829 31767341567081023179528311)
  ·
    refine ⟨47651012350621534769292467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31767341567081023179528311 47651012350621534769292467)
    ·
      refine ⟨71476518525932302153938701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47651012350621534769292467 71476518525932302153938701)
      ·
        refine ⟨26803694447224613307727013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71476518525932302153938701 26803694447224613307727013)
        ·
          refine ⟨5025692708854614995198815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26803694447224613307727013 5025692708854614995198815)
          ·
            refine ⟨7538539063281922492798223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025692708854614995198815 7538539063281922492798223)
            ·
              refine ⟨11307808594922883739197335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538539063281922492798223 11307808594922883739197335)
              ·
                refine ⟨16961712892384325608796003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307808594922883739197335 16961712892384325608796003)
                ·
                  refine ⟨25442569338576488413194005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16961712892384325608796003 25442569338576488413194005)
                  ·
                    refine ⟨1192620437745772894368469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25442569338576488413194005 1192620437745772894368469)
                    ·
                      rfl

theorem cell22_3483930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_3483930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483930 prefixEnd_3483930 := by exact prefixLift 3483930
  have htrace : WordTrace (prefixWord ++ tailWord_3483930) baseStart_3483930 baseEnd_3483930 := by
    simpa [prefixWord, tailWord_3483930, baseEnd_3483930] using wordTrace_append hprefix tailTrace_3483930
  have hstable : (prefixWord ++ tailWord_3483930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483930).length < 2 ^ (prefixWord ++ tailWord_3483930).sum := by decide
  have hdescent : baseEnd_3483930 < baseStart_3483930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483934 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3483934 : Nat := 118140960795 + 3483934 * 2 ^ 59
def prefixEnd_3483934 : Nat := 4983230072969 + 3 ^ 40 * 3483934 * 2
def baseEnd_3483934 : Nat := 397540602342506072422819

theorem tailTrace_3483934 : CollatzResearch.WordTrace tailWord_3483934 prefixEnd_3483934 397540602342506072422819 := by
  unfold tailWord_3483934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883689020038700175157357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84713008106873067600839237 15883689020038700175157357)
  ·
    refine ⟨5956383382514512565684009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15883689020038700175157357 5956383382514512565684009)
    ·
      refine ⟨4467287536885884424263007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5956383382514512565684009 4467287536885884424263007)
      ·
        refine ⟨6700931305328826636394511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467287536885884424263007 6700931305328826636394511)
        ·
          refine ⟨10051396957993239954591767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6700931305328826636394511 10051396957993239954591767)
          ·
            refine ⟨15077095436989859931887651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10051396957993239954591767 15077095436989859931887651)
            ·
              refine ⟨22615643155484789897831477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15077095436989859931887651 22615643155484789897831477)
              ·
                refine ⟨2120216545826699052921701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22615643155484789897831477 2120216545826699052921701)
                ·
                  refine ⟨397540602342506072422819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120216545826699052921701 397540602342506072422819)
                  ·
                    rfl

theorem cell22_3483934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3483934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483934 prefixEnd_3483934 := by exact prefixLift 3483934
  have htrace : WordTrace (prefixWord ++ tailWord_3483934) baseStart_3483934 baseEnd_3483934 := by
    simpa [prefixWord, tailWord_3483934, baseEnd_3483934] using wordTrace_append hprefix tailTrace_3483934
  have hstable : (prefixWord ++ tailWord_3483934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483934).length < 2 ^ (prefixWord ++ tailWord_3483934).sum := by decide
  have hdescent : baseEnd_3483934 < baseStart_3483934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483949 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3483949 : Nat := 118140960795 + 3483949 * 2 ^ 59
def prefixEnd_3483949 : Nat := 4983230072969 + 3 ^ 40 * 3483949 * 2
def baseEnd_3483949 : Nat := 1192626941834063178143411

theorem tailTrace_3483949 : CollatzResearch.WordTrace tailWord_3483949 prefixEnd_3483949 1192626941834063178143411 := by
  unfold tailWord_3483949
  simp only [CollatzResearch.WordTrace]
  refine ⟨127070059255255258963054901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84713372836836839308703267 127070059255255258963054901)
  ·
    refine ⟨11912818055180180527786397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127070059255255258963054901 11912818055180180527786397)
    ·
      refine ⟨4467306770692567697919899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11912818055180180527786397 4467306770692567697919899)
      ·
        refine ⟨6700960156038851546879849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467306770692567697919899 6700960156038851546879849)
        ·
          refine ⟨5025720117029138660159887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6700960156038851546879849 5025720117029138660159887)
          ·
            refine ⟨7538580175543707990239831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025720117029138660159887 7538580175543707990239831)
            ·
              refine ⟨11307870263315561985359747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538580175543707990239831 11307870263315561985359747)
              ·
                refine ⟨16961805394973342978039621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11307870263315561985359747 16961805394973342978039621)
                ·
                  refine ⟨3180338511557501808382429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16961805394973342978039621 3180338511557501808382429)
                  ·
                    refine ⟨1192626941834063178143411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180338511557501808382429 1192626941834063178143411)
                    ·
                      rfl

theorem cell22_3483949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3483949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483949 prefixEnd_3483949 := by exact prefixLift 3483949
  have htrace : WordTrace (prefixWord ++ tailWord_3483949) baseStart_3483949 baseEnd_3483949 := by
    simpa [prefixWord, tailWord_3483949, baseEnd_3483949] using wordTrace_append hprefix tailTrace_3483949
  have hstable : (prefixWord ++ tailWord_3483949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483949).length < 2 ^ (prefixWord ++ tailWord_3483949).sum := by decide
  have hdescent : baseEnd_3483949 < baseStart_3483949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483960 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_3483960 : Nat := 118140960795 + 3483960 * 2 ^ 59
def prefixEnd_3483960 : Nat := 4983230072969 + 3 ^ 40 * 3483960 * 2
def baseEnd_3483960 : Nat := 1192630707358862816118377

theorem tailTrace_3483960 : CollatzResearch.WordTrace tailWord_3483960 prefixEnd_3483960 1192630707358862816118377 := by
  unfold tailWord_3483960
  simp only [CollatzResearch.WordTrace]
  refine ⟨63535230229107703920852667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84713640305476938561136889 63535230229107703920852667)
  ·
    refine ⟨95302845343661555881279001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63535230229107703920852667 95302845343661555881279001)
    ·
      refine ⟨71477134007746166910959251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95302845343661555881279001 71477134007746166910959251)
      ·
        refine ⟨107215701011619250366438877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71477134007746166910959251 107215701011619250366438877)
        ·
          refine ⟨40205887879357218887414579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107215701011619250366438877 40205887879357218887414579)
          ·
            refine ⟨60308831819035828331121869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40205887879357218887414579 60308831819035828331121869)
            ·
              refine ⟨22615811932138435624170701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60308831819035828331121869 22615811932138435624170701)
              ·
                refine ⟨8480929474551913359064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22615811932138435624170701 8480929474551913359064013)
                ·
                  refine ⟨3180348552956967509649005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8480929474551913359064013 3180348552956967509649005)
                  ·
                    refine ⟨1192630707358862816118377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180348552956967509649005 1192630707358862816118377)
                    ·
                      rfl

theorem cell22_3483960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_3483960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483960 prefixEnd_3483960 := by exact prefixLift 3483960
  have htrace : WordTrace (prefixWord ++ tailWord_3483960) baseStart_3483960 baseEnd_3483960 := by
    simpa [prefixWord, tailWord_3483960, baseEnd_3483960] using wordTrace_append hprefix tailTrace_3483960
  have hstable : (prefixWord ++ tailWord_3483960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483960).length < 2 ^ (prefixWord ++ tailWord_3483960).sum := by decide
  have hdescent : baseEnd_3483960 < baseStart_3483960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3483998 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3483998 : Nat := 118140960795 + 3483998 * 2 ^ 59
def prefixEnd_3483998 : Nat := 4983230072969 + 3 ^ 40 * 3483998 * 2
def baseEnd_3483998 : Nat := 1192643715535443383668261

theorem tailTrace_3483998 : CollatzResearch.WordTrace tailWord_3483998 prefixEnd_3483998 1192643715535443383668261 := by
  unfold tailWord_3483998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883980804009717541448581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84714564288051826887725765 15883980804009717541448581)
  ·
    refine ⟨2978246400751822039021609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15883980804009717541448581 2978246400751822039021609)
    ·
      refine ⟨2233684800563866529266207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2978246400751822039021609 2233684800563866529266207)
      ·
        refine ⟨3350527200845799793899311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233684800563866529266207 3350527200845799793899311)
        ·
          refine ⟨5025790801268699690848967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350527200845799793899311 5025790801268699690848967)
          ·
            refine ⟨7538686201903049536273451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025790801268699690848967 7538686201903049536273451)
            ·
              refine ⟨11308029302854574304410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538686201903049536273451 11308029302854574304410177)
              ·
                refine ⟨8481021977140930728307633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11308029302854574304410177 8481021977140930728307633)
                ·
                  refine ⟨6360766482855698046230725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8481021977140930728307633 6360766482855698046230725)
                  ·
                    refine ⟨1192643715535443383668261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6360766482855698046230725 1192643715535443383668261)
                    ·
                      rfl

theorem cell22_3483998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3483998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3483998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3483998 prefixEnd_3483998 := by exact prefixLift 3483998
  have htrace : WordTrace (prefixWord ++ tailWord_3483998) baseStart_3483998 baseEnd_3483998 := by
    simpa [prefixWord, tailWord_3483998, baseEnd_3483998] using wordTrace_append hprefix tailTrace_3483998
  have hstable : (prefixWord ++ tailWord_3483998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3483998).length < 2 ^ (prefixWord ++ tailWord_3483998).sum := by decide
  have hdescent : baseEnd_3483998 < baseStart_3483998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3483998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484067 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 2, 3]
def baseStart_3484067 : Nat := 118140960795 + 3484067 * 2 ^ 59
def prefixEnd_3484067 : Nat := 4983230072969 + 3 ^ 40 * 3484067 * 2
def baseEnd_3484067 : Nat := 1192667335645550203693049

theorem tailTrace_3484067 : CollatzResearch.WordTrace tailWord_3484067 prefixEnd_3484067 1192667335645550203693049 := by
  unfold tailWord_3484067
  simp only [CollatzResearch.WordTrace]
  refine ⟨127074363068827765115850455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84716242045885176743900303 127074363068827765115850455)
  ·
    refine ⟨190611544603241647673775683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127074363068827765115850455 190611544603241647673775683)
    ·
      refine ⟨285917316904862471510663525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190611544603241647673775683 285917316904862471510663525)
      ·
        refine ⟨53609496919661713408249411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285917316904862471510663525 53609496919661713408249411)
        ·
          refine ⟨80414245379492570112374117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53609496919661713408249411 80414245379492570112374117)
          ·
            refine ⟨15077671008654856896070147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80414245379492570112374117 15077671008654856896070147)
            ·
              refine ⟨22616506512982285344105221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15077671008654856896070147 22616506512982285344105221)
              ·
                refine ⟨4240594971184178502019729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22616506512982285344105221 4240594971184178502019729)
                ·
                  refine ⟨3180446228388133876514797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4240594971184178502019729 3180446228388133876514797)
                  ·
                    refine ⟨1192667335645550203693049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180446228388133876514797 1192667335645550203693049)
                    ·
                      rfl

theorem cell22_3484067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 3].length) (baseStart_3484067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484067 prefixEnd_3484067 := by exact prefixLift 3484067
  have htrace : WordTrace (prefixWord ++ tailWord_3484067) baseStart_3484067 baseEnd_3484067 := by
    simpa [prefixWord, tailWord_3484067, baseEnd_3484067] using wordTrace_append hprefix tailTrace_3484067
  have hstable : (prefixWord ++ tailWord_3484067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484067).length < 2 ^ (prefixWord ++ tailWord_3484067).sum := by decide
  have hdescent : baseEnd_3484067 < baseStart_3484067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484129 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3484129 : Nat := 118140960795 + 3484129 * 2 ^ 59
def prefixEnd_3484129 : Nat := 4983230072969 + 3 ^ 40 * 3484129 * 2
def baseEnd_3484129 : Nat := 1192688559512602708642859

theorem tailTrace_3484129 : CollatzResearch.WordTrace tailWord_3484129 prefixEnd_3484129 1192688559512602708642859 := by
  unfold tailWord_3484129
  simp only [CollatzResearch.WordTrace]
  refine ⟨127076624394603149704607441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84717749596402099803071627 127076624394603149704607441)
  ·
    refine ⟨95307468295952362278455581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127076624394603149704607441 95307468295952362278455581)
    ·
      refine ⟨35740300610982135854420843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95307468295952362278455581 35740300610982135854420843)
      ·
        refine ⟨53610450916473203781631265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35740300610982135854420843 53610450916473203781631265)
        ·
          refine ⟨40207838187354902836223449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53610450916473203781631265 40207838187354902836223449)
          ·
            refine ⟨30155878640516177127167587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40207838187354902836223449 30155878640516177127167587)
            ·
              refine ⟨45233817960774265690751381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30155878640516177127167587 45233817960774265690751381)
              ·
                refine ⟨2120335216911293704253971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45233817960774265690751381 2120335216911293704253971)
                ·
                  refine ⟨3180502825366940556380957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120335216911293704253971 3180502825366940556380957)
                  ·
                    refine ⟨1192688559512602708642859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180502825366940556380957 1192688559512602708642859)
                    ·
                      rfl

theorem cell22_3484129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3484129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484129 prefixEnd_3484129 := by exact prefixLift 3484129
  have htrace : WordTrace (prefixWord ++ tailWord_3484129) baseStart_3484129 baseEnd_3484129 := by
    simpa [prefixWord, tailWord_3484129, baseEnd_3484129] using wordTrace_append hprefix tailTrace_3484129
  have hstable : (prefixWord ++ tailWord_3484129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484129).length < 2 ^ (prefixWord ++ tailWord_3484129).sum := by decide
  have hdescent : baseEnd_3484129 < baseStart_3484129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484140 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3484140 : Nat := 118140960795 + 3484140 * 2 ^ 59
def prefixEnd_3484140 : Nat := 4983230072969 + 3 ^ 40 * 3484140 * 2
def baseEnd_3484140 : Nat := 1192692325037402346617825

theorem tailTrace_3484140 : CollatzResearch.WordTrace tailWord_3484140 prefixEnd_3484140 1192692325037402346617825 := by
  unfold tailWord_3484140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63538512798781649291628937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84718017065042199055505249 63538512798781649291628937)
  ·
    refine ⟨47653884599086236968721703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63538512798781649291628937 47653884599086236968721703)
    ·
      refine ⟨71480826898629355453082555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47653884599086236968721703 71480826898629355453082555)
      ·
        refine ⟨107221240347944033179623833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71480826898629355453082555 107221240347944033179623833)
        ·
          refine ⟨80415930260958024884717875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107221240347944033179623833 80415930260958024884717875)
          ·
            refine ⟨120623895391437037327076813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80415930260958024884717875 120623895391437037327076813)
            ·
              refine ⟨45233960771788888997653805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120623895391437037327076813 45233960771788888997653805)
              ·
                refine ⟨16962735289420833374120177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45233960771788888997653805 16962735289420833374120177)
                ·
                  refine ⟨12722051467065625030590133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16962735289420833374120177 12722051467065625030590133)
                  ·
                    refine ⟨1192692325037402346617825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12722051467065625030590133 1192692325037402346617825)
                    ·
                      rfl

theorem cell22_3484140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3484140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484140 prefixEnd_3484140 := by exact prefixLift 3484140
  have htrace : WordTrace (prefixWord ++ tailWord_3484140) baseStart_3484140 baseEnd_3484140 := by
    simpa [prefixWord, tailWord_3484140, baseEnd_3484140] using wordTrace_append hprefix tailTrace_3484140
  have hstable : (prefixWord ++ tailWord_3484140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484140).length < 2 ^ (prefixWord ++ tailWord_3484140).sum := by decide
  have hdescent : baseEnd_3484140 < baseStart_3484140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484180 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3484180 : Nat := 118140960795 + 3484180 * 2 ^ 59
def prefixEnd_3484180 : Nat := 4983230072969 + 3 ^ 40 * 3484180 * 2
def baseEnd_3484180 : Nat := 1192706017854855575617703

theorem tailTrace_3484180 : CollatzResearch.WordTrace tailWord_3484180 prefixEnd_3484180 1192706017854855575617703 := by
  unfold tailWord_3484180
  simp only [CollatzResearch.WordTrace]
  refine ⟨63539242258709192707356997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84718989678278923609809329 63539242258709192707356997)
  ·
    refine ⟨11913607923507973632629437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63539242258709192707356997 11913607923507973632629437)
    ·
      refine ⟨4467602971315490112236039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11913607923507973632629437 4467602971315490112236039)
      ·
        refine ⟨6701404456973235168354059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467602971315490112236039 6701404456973235168354059)
        ·
          refine ⟨10052106685459852752531089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701404456973235168354059 10052106685459852752531089)
          ·
            refine ⟨7539080014094889564398317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10052106685459852752531089 7539080014094889564398317)
            ·
              refine ⟨2827155005285583586649369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7539080014094889564398317 2827155005285583586649369)
              ·
                refine ⟨2120366253964187689987027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827155005285583586649369 2120366253964187689987027)
                ·
                  refine ⟨3180549380946281534980541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120366253964187689987027 3180549380946281534980541)
                  ·
                    refine ⟨1192706017854855575617703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180549380946281534980541 1192706017854855575617703)
                    ·
                      rfl

theorem cell22_3484180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3484180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484180 prefixEnd_3484180 := by exact prefixLift 3484180
  have htrace : WordTrace (prefixWord ++ tailWord_3484180) baseStart_3484180 baseEnd_3484180 := by
    simpa [prefixWord, tailWord_3484180, baseEnd_3484180] using wordTrace_append hprefix tailTrace_3484180
  have hstable : (prefixWord ++ tailWord_3484180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484180).length < 2 ^ (prefixWord ++ tailWord_3484180).sum := by decide
  have hdescent : baseEnd_3484180 < baseStart_3484180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484185 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_3484185 : Nat := 118140960795 + 3484185 * 2 ^ 59
def prefixEnd_3484185 : Nat := 4983230072969 + 3 ^ 40 * 3484185 * 2
def baseEnd_3484185 : Nat := 1192707729457037229242687

theorem tailTrace_3484185 : CollatzResearch.WordTrace tailWord_3484185 prefixEnd_3484185 1192707729457037229242687 := by
  unfold tailWord_3484185
  simp only [CollatzResearch.WordTrace]
  refine ⟨127078666882400271268646009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84719111254933514179097339 127078666882400271268646009)
  ·
    refine ⟨95309000161800203451484507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127078666882400271268646009 95309000161800203451484507)
    ·
      refine ⟨142963500242700305177226761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95309000161800203451484507 142963500242700305177226761)
      ·
        refine ⟨107222625182025228882920071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142963500242700305177226761 107222625182025228882920071)
        ·
          refine ⟨160833937773037843324380107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107222625182025228882920071 160833937773037843324380107)
          ·
            refine ⟨241250906659556764986570161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160833937773037843324380107 241250906659556764986570161)
            ·
              refine ⟨180938179994667573739927621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241250906659556764986570161 180938179994667573739927621)
              ·
                refine ⟨33925908749000170076236429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180938179994667573739927621 33925908749000170076236429)
                ·
                  refine ⟨12722215780875063778588661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33925908749000170076236429 12722215780875063778588661)
                  ·
                    refine ⟨1192707729457037229242687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12722215780875063778588661 1192707729457037229242687)
                    ·
                      rfl

theorem cell22_3484185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_3484185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484185 prefixEnd_3484185 := by exact prefixLift 3484185
  have htrace : WordTrace (prefixWord ++ tailWord_3484185) baseStart_3484185 baseEnd_3484185 := by
    simpa [prefixWord, tailWord_3484185, baseEnd_3484185] using wordTrace_append hprefix tailTrace_3484185
  have hstable : (prefixWord ++ tailWord_3484185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484185).length < 2 ^ (prefixWord ++ tailWord_3484185).sum := by decide
  have hdescent : baseEnd_3484185 < baseStart_3484185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484215 : List Nat := [1, 1, 3, 1, 2, 3, 1, 10]
def baseStart_3484215 : Nat := 118140960795 + 3484215 * 2 ^ 59
def prefixEnd_3484215 : Nat := 4983230072969 + 3 ^ 40 * 3484215 * 2
def baseEnd_3484215 : Nat := 132524222118903016776955

theorem tailTrace_3484215 : CollatzResearch.WordTrace tailWord_3484215 prefixEnd_3484215 132524222118903016776955 := by
  unfold tailWord_3484215
  simp only [CollatzResearch.WordTrace]
  refine ⟨127079761072291586392238099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84719840714861057594825399 127079761072291586392238099)
  ·
    refine ⟨190619641608437379588357149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127079761072291586392238099 190619641608437379588357149)
    ·
      refine ⟨71482365603164017345633931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190619641608437379588357149 71482365603164017345633931)
      ·
        refine ⟨107223548404746026018450897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71482365603164017345633931 107223548404746026018450897)
        ·
          refine ⟨80417661303559519513838173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107223548404746026018450897 80417661303559519513838173)
          ·
            refine ⟨30156622988834819817689315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80417661303559519513838173 30156622988834819817689315)
            ·
              refine ⟨45234934483252229726533973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30156622988834819817689315 45234934483252229726533973)
              ·
                refine ⟨132524222118903016776955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45234934483252229726533973 132524222118903016776955)
                ·
                  rfl

theorem cell22_3484215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 10].length) (baseStart_3484215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484215 prefixEnd_3484215 := by exact prefixLift 3484215
  have htrace : WordTrace (prefixWord ++ tailWord_3484215) baseStart_3484215 baseEnd_3484215 := by
    simpa [prefixWord, tailWord_3484215, baseEnd_3484215] using wordTrace_append hprefix tailTrace_3484215
  have hstable : (prefixWord ++ tailWord_3484215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484215).length < 2 ^ (prefixWord ++ tailWord_3484215).sum := by decide
  have hdescent : baseEnd_3484215 < baseStart_3484215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484281 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_3484281 : Nat := 118140960795 + 3484281 * 2 ^ 59
def prefixEnd_3484281 : Nat := 4983230072969 + 3 ^ 40 * 3484281 * 2
def baseEnd_3484281 : Nat := 1192740592218924978842393

theorem tailTrace_3484281 : CollatzResearch.WordTrace tailWord_3484281 prefixEnd_3484281 1192740592218924978842393 := by
  unfold tailWord_3484281
  simp only [CollatzResearch.WordTrace]
  refine ⟨127082168290052479664140697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84721445526701653109427131 127082168290052479664140697)
  ·
    refine ⟨95311626217539359748105523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127082168290052479664140697 95311626217539359748105523)
    ·
      refine ⟨142967439326309039622158285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95311626217539359748105523 142967439326309039622158285)
      ·
        refine ⟨53612789747365889858309357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142967439326309039622158285 53612789747365889858309357)
        ·
          refine ⟨20104796155262208696866009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53612789747365889858309357 20104796155262208696866009)
          ·
            refine ⟨15078597116446656522649507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20104796155262208696866009 15078597116446656522649507)
            ·
              refine ⟨22617895674669984783974261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15078597116446656522649507 22617895674669984783974261)
              ·
                refine ⟨2120427719500311073497587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22617895674669984783974261 2120427719500311073497587)
                ·
                  refine ⟨3180641579250466610246381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120427719500311073497587 3180641579250466610246381)
                  ·
                    refine ⟨1192740592218924978842393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180641579250466610246381 1192740592218924978842393)
                    ·
                      rfl

theorem cell22_3484281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_3484281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484281 prefixEnd_3484281 := by exact prefixLift 3484281
  have htrace : WordTrace (prefixWord ++ tailWord_3484281) baseStart_3484281 baseEnd_3484281 := by
    simpa [prefixWord, tailWord_3484281, baseEnd_3484281] using wordTrace_append hprefix tailTrace_3484281
  have hstable : (prefixWord ++ tailWord_3484281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484281).length < 2 ^ (prefixWord ++ tailWord_3484281).sum := by decide
  have hdescent : baseEnd_3484281 < baseStart_3484281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484341 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3484341 : Nat := 118140960795 + 3484341 * 2 ^ 59
def prefixEnd_3484341 : Nat := 4983230072969 + 3 ^ 40 * 3484341 * 2
def baseEnd_3484341 : Nat := 1192761131445104822342209

theorem tailTrace_3484341 : CollatzResearch.WordTrace tailWord_3484341 prefixEnd_3484341 1192761131445104822342209 := by
  unfold tailWord_3484341
  simp only [CollatzResearch.WordTrace]
  refine ⟨127084356669835109911324877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84722904446556739940883251 127084356669835109911324877)
  ·
    refine ⟨47656633751188166216746829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127084356669835109911324877 47656633751188166216746829)
    ·
      refine ⟨17871237656695562331280061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47656633751188166216746829 17871237656695562331280061)
      ·
        refine ⟨6701714121260835874230023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17871237656695562331280061 6701714121260835874230023)
        ·
          refine ⟨10052571181891253811345035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701714121260835874230023 10052571181891253811345035)
          ·
            refine ⟨15078856772836880717017553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052571181891253811345035 15078856772836880717017553)
            ·
              refine ⟨11309142579627660537763165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15078856772836880717017553 11309142579627660537763165)
              ·
                refine ⟨4240928467360372701661187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11309142579627660537763165 4240928467360372701661187)
                ·
                  refine ⟨6361392701040559052491781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4240928467360372701661187 6361392701040559052491781)
                  ·
                    refine ⟨1192761131445104822342209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361392701040559052491781 1192761131445104822342209)
                    ·
                      rfl

theorem cell22_3484341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3484341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484341 prefixEnd_3484341 := by exact prefixLift 3484341
  have htrace : WordTrace (prefixWord ++ tailWord_3484341) baseStart_3484341 baseEnd_3484341 := by
    simpa [prefixWord, tailWord_3484341, baseEnd_3484341] using wordTrace_append hprefix tailTrace_3484341
  have hstable : (prefixWord ++ tailWord_3484341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484341).length < 2 ^ (prefixWord ++ tailWord_3484341).sum := by decide
  have hdescent : baseEnd_3484341 < baseStart_3484341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484356 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3484356 : Nat := 118140960795 + 3484356 * 2 ^ 59
def prefixEnd_3484356 : Nat := 4983230072969 + 3 ^ 40 * 3484356 * 2
def baseEnd_3484356 : Nat := 397588755417216594405721

theorem tailTrace_3484356 : CollatzResearch.WordTrace tailWord_3484356 prefixEnd_3484356 397588755417216594405721 := by
  unfold tailWord_3484356
  simp only [CollatzResearch.WordTrace]
  refine ⟨63542451882390383736560461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84723269176520511648747281 63542451882390383736560461)
  ·
    refine ⟨23828419455896393901210173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63542451882390383736560461 23828419455896393901210173)
    ·
      refine ⟨8935657295961147712953815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23828419455896393901210173 8935657295961147712953815)
      ·
        refine ⟨13403485943941721569430723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935657295961147712953815 13403485943941721569430723)
        ·
          refine ⟨20105228915912582354146085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403485943941721569430723 20105228915912582354146085)
          ·
            refine ⟨3769730421733609191402391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20105228915912582354146085 3769730421733609191402391)
            ·
              refine ⟨5654595632600413787103587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769730421733609191402391 5654595632600413787103587)
              ·
                refine ⟨8481893448900620680655381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654595632600413787103587 8481893448900620680655381)
                ·
                  refine ⟨397588755417216594405721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8481893448900620680655381 397588755417216594405721)
                  ·
                    rfl

theorem cell22_3484356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3484356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484356 prefixEnd_3484356 := by exact prefixLift 3484356
  have htrace : WordTrace (prefixWord ++ tailWord_3484356) baseStart_3484356 baseEnd_3484356 := by
    simpa [prefixWord, tailWord_3484356, baseEnd_3484356] using wordTrace_append hprefix tailTrace_3484356
  have hstable : (prefixWord ++ tailWord_3484356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484356).length < 2 ^ (prefixWord ++ tailWord_3484356).sum := by decide
  have hdescent : baseEnd_3484356 < baseStart_3484356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484450 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3484450 : Nat := 118140960795 + 3484450 * 2 ^ 59
def prefixEnd_3484450 : Nat := 4983230072969 + 3 ^ 40 * 3484450 * 2
def baseEnd_3484450 : Nat := 1192798444372664871366875

theorem tailTrace_3484450 : CollatzResearch.WordTrace tailWord_3484450 prefixEnd_3484450 1192798444372664871366875 := by
  unfold tailWord_3484450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31772083056610055381760701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84725554817626814351361869 31772083056610055381760701)
  ·
    refine ⟨11914531146228770768160263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31772083056610055381760701 11914531146228770768160263)
    ·
      refine ⟨17871796719343156152240395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11914531146228770768160263 17871796719343156152240395)
      ·
        refine ⟨26807695079014734228360593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17871796719343156152240395 26807695079014734228360593)
        ·
          refine ⟨20105771309261050671270445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26807695079014734228360593 20105771309261050671270445)
          ·
            refine ⟨7539664240972894001726417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20105771309261050671270445 7539664240972894001726417)
            ·
              refine ⟨5654748180729670501294813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7539664240972894001726417 5654748180729670501294813)
              ·
                refine ⟨2120530567773626437985555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5654748180729670501294813 2120530567773626437985555)
                ·
                  refine ⟨3180795851660439656978333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120530567773626437985555 3180795851660439656978333)
                  ·
                    refine ⟨1192798444372664871366875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180795851660439656978333 1192798444372664871366875)
                    ·
                      rfl

theorem cell22_3484450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3484450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484450 prefixEnd_3484450 := by exact prefixLift 3484450
  have htrace : WordTrace (prefixWord ++ tailWord_3484450) baseStart_3484450 baseEnd_3484450 := by
    simpa [prefixWord, tailWord_3484450, baseEnd_3484450] using wordTrace_append hprefix tailTrace_3484450
  have hstable : (prefixWord ++ tailWord_3484450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484450).length < 2 ^ (prefixWord ++ tailWord_3484450).sum := by decide
  have hdescent : baseEnd_3484450 < baseStart_3484450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484504 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_3484504 : Nat := 118140960795 + 3484504 * 2 ^ 59
def prefixEnd_3484504 : Nat := 4983230072969 + 3 ^ 40 * 3484504 * 2
def baseEnd_3484504 : Nat := 1192816929676226730516709

theorem tailTrace_3484504 : CollatzResearch.WordTrace tailWord_3484504 prefixEnd_3484504 1192816929676226730516709 := by
  unfold tailWord_3484504
  simp only [CollatzResearch.WordTrace]
  refine ⟨63545150884122294374754283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84726867845496392499672377 63545150884122294374754283)
  ·
    refine ⟨95317726326183441562131425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63545150884122294374754283 95317726326183441562131425)
    ·
      refine ⟨71488294744637581171598569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95317726326183441562131425 71488294744637581171598569)
      ·
        refine ⟨53616221058478185878698927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71488294744637581171598569 53616221058478185878698927)
        ·
          refine ⟨80424331587717278818048391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53616221058478185878698927 80424331587717278818048391)
          ·
            refine ⟨120636497381575918227072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80424331587717278818048391 120636497381575918227072587)
            ·
              refine ⟨180954746072363877340608881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120636497381575918227072587 180954746072363877340608881)
              ·
                refine ⟨135716059554272908005456661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180954746072363877340608881 135716059554272908005456661)
                ·
                  refine ⟨6361690291606542562755781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135716059554272908005456661 6361690291606542562755781)
                  ·
                    refine ⟨1192816929676226730516709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6361690291606542562755781 1192816929676226730516709)
                    ·
                      rfl

theorem cell22_3484504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_3484504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484504 prefixEnd_3484504 := by exact prefixLift 3484504
  have htrace : WordTrace (prefixWord ++ tailWord_3484504) baseStart_3484504 baseEnd_3484504 := by
    simpa [prefixWord, tailWord_3484504, baseEnd_3484504] using wordTrace_append hprefix tailTrace_3484504
  have hstable : (prefixWord ++ tailWord_3484504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484504).length < 2 ^ (prefixWord ++ tailWord_3484504).sum := by decide
  have hdescent : baseEnd_3484504 < baseStart_3484504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484506 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_3484506 : Nat := 118140960795 + 3484506 * 2 ^ 59
def prefixEnd_3484506 : Nat := 4983230072969 + 3 ^ 40 * 3484506 * 2
def baseEnd_3484506 : Nat := 1192817614317099391966703

theorem tailTrace_3484506 : CollatzResearch.WordTrace tailWord_3484506 prefixEnd_3484506 1192817614317099391966703 := by
  unfold tailWord_3484506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31772593678559335772770343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84726916476158228727387581 31772593678559335772770343)
  ·
    refine ⟨47658890517839003659155515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31772593678559335772770343 47658890517839003659155515)
    ·
      refine ⟨71488335776758505488733273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47658890517839003659155515 71488335776758505488733273)
      ·
        refine ⟨53616251832568879116549955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71488335776758505488733273 53616251832568879116549955)
        ·
          refine ⟨80424377748853318674824933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53616251832568879116549955 80424377748853318674824933)
          ·
            refine ⟨15079570827909997251529675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80424377748853318674824933 15079570827909997251529675)
            ·
              refine ⟨22619356241864995877294513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15079570827909997251529675 22619356241864995877294513)
              ·
                refine ⟨16964517181398746907970885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22619356241864995877294513 16964517181398746907970885)
                ·
                  refine ⟨3180846971512265045244541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16964517181398746907970885 3180846971512265045244541)
                  ·
                    refine ⟨1192817614317099391966703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3180846971512265045244541 1192817614317099391966703)
                    ·
                      rfl

theorem cell22_3484506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_3484506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484506 prefixEnd_3484506 := by exact prefixLift 3484506
  have htrace : WordTrace (prefixWord ++ tailWord_3484506) baseStart_3484506 baseEnd_3484506 := by
    simpa [prefixWord, tailWord_3484506, baseEnd_3484506] using wordTrace_append hprefix tailTrace_3484506
  have hstable : (prefixWord ++ tailWord_3484506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484506).length < 2 ^ (prefixWord ++ tailWord_3484506).sum := by decide
  have hdescent : baseEnd_3484506 < baseStart_3484506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484519 : List Nat := [1, 1, 5, 1, 2, 2, 10]
def baseStart_3484519 : Nat := 118140960795 + 3484519 * 2 ^ 59
def prefixEnd_3484519 : Nat := 4983230072969 + 3 ^ 40 * 3484519 * 2
def baseEnd_3484519 : Nat := 44178594980843395977469

theorem tailTrace_3484519 : CollatzResearch.WordTrace tailWord_3484519 prefixEnd_3484519 44178594980843395977469 := by
  unfold tailWord_3484519
  simp only [CollatzResearch.WordTrace]
  refine ⟨127090848863190246311304611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84727232575460164207536407 127090848863190246311304611)
  ·
    refine ⟨190636273294785369466956917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127090848863190246311304611 190636273294785369466956917)
    ·
      refine ⟨17872150621386128387527211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190636273294785369466956917 17872150621386128387527211)
      ·
        refine ⟨26808225932079192581290817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872150621386128387527211 26808225932079192581290817)
        ·
          refine ⟨20106169449059394435968113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808225932079192581290817 20106169449059394435968113)
          ·
            refine ⟨15079627086794545826976085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20106169449059394435968113 15079627086794545826976085)
            ·
              refine ⟨44178594980843395977469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15079627086794545826976085 44178594980843395977469)
              ·
                rfl

theorem cell22_3484519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 10].length) (baseStart_3484519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484519 prefixEnd_3484519 := by exact prefixLift 3484519
  have htrace : WordTrace (prefixWord ++ tailWord_3484519) baseStart_3484519 baseEnd_3484519 := by
    simpa [prefixWord, tailWord_3484519, baseEnd_3484519] using wordTrace_append hprefix tailTrace_3484519
  have hstable : (prefixWord ++ tailWord_3484519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484519).length < 2 ^ (prefixWord ++ tailWord_3484519).sum := by decide
  have hdescent : baseEnd_3484519 < baseStart_3484519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484643 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 4]
def baseStart_3484643 : Nat := 118140960795 + 3484643 * 2 ^ 59
def prefixEnd_3484643 : Nat := 4983230072969 + 3 ^ 40 * 3484643 * 2
def baseEnd_3484643 : Nat := 397621504072292233763761

theorem tailTrace_3484643 : CollatzResearch.WordTrace tailWord_3484643 prefixEnd_3484643 397621504072292233763761 := by
  unfold tailWord_3484643
  simp only [CollatzResearch.WordTrace]
  refine ⟨127095371514741015488818583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84730247676494010325879055 127095371514741015488818583)
  ·
    refine ⟨190643057272111523233227875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127095371514741015488818583 190643057272111523233227875)
    ·
      refine ⟨285964585908167284849841813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190643057272111523233227875 285964585908167284849841813)
      ·
        refine ⟨13404589964445341477336335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 285964585908167284849841813 13404589964445341477336335)
        ·
          refine ⟨20106884946668012216004503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13404589964445341477336335 20106884946668012216004503)
          ·
            refine ⟨30160327420002018324006755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20106884946668012216004503 30160327420002018324006755)
            ·
              refine ⟨45240491130003027486010133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30160327420002018324006755 45240491130003027486010133)
              ·
                refine ⟨2120648021718891913406725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45240491130003027486010133 2120648021718891913406725)
                ·
                  refine ⟨397621504072292233763761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120648021718891913406725 397621504072292233763761)
                  ·
                    rfl

theorem cell22_3484643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 4].length) (baseStart_3484643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484643 prefixEnd_3484643 := by exact prefixLift 3484643
  have htrace : WordTrace (prefixWord ++ tailWord_3484643) baseStart_3484643 baseEnd_3484643 := by
    simpa [prefixWord, tailWord_3484643, baseEnd_3484643] using wordTrace_append hprefix tailTrace_3484643
  have hstable : (prefixWord ++ tailWord_3484643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484643).length < 2 ^ (prefixWord ++ tailWord_3484643).sum := by decide
  have hdescent : baseEnd_3484643 < baseStart_3484643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484754 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3484754 : Nat := 118140960795 + 3484754 * 2 ^ 59
def prefixEnd_3484754 : Nat := 4983230072969 + 3 ^ 40 * 3484754 * 2
def baseEnd_3484754 : Nat := 1192902509785309411765943

theorem tailTrace_3484754 : CollatzResearch.WordTrace tailWord_3484754 prefixEnd_3484754 1192902509785309411765943 := by
  unfold tailWord_3484754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31774855004334720361527329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84732946678225920964072877 31774855004334720361527329)
  ·
    refine ⟨23831141253251040271145497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31774855004334720361527329 23831141253251040271145497)
    ·
      refine ⟨17873355939938280203359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23831141253251040271145497 17873355939938280203359123)
      ·
        refine ⟨26810033909907420305038685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17873355939938280203359123 26810033909907420305038685)
        ·
          refine ⟨10053762716215282614389507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26810033909907420305038685 10053762716215282614389507)
          ·
            refine ⟨15080644074322923921584261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053762716215282614389507 15080644074322923921584261)
            ·
              refine ⟨2827620763935548235297049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15080644074322923921584261 2827620763935548235297049)
              ·
                refine ⟨2120715572951661176472787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827620763935548235297049 2120715572951661176472787)
                ·
                  refine ⟨3181073359427491764709181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120715572951661176472787 3181073359427491764709181)
                  ·
                    refine ⟨1192902509785309411765943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181073359427491764709181 1192902509785309411765943)
                    ·
                      rfl

theorem cell22_3484754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3484754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484754 prefixEnd_3484754 := by exact prefixLift 3484754
  have htrace : WordTrace (prefixWord ++ tailWord_3484754) baseStart_3484754 baseEnd_3484754 := by
    simpa [prefixWord, tailWord_3484754, baseEnd_3484754] using wordTrace_append hprefix tailTrace_3484754
  have hstable : (prefixWord ++ tailWord_3484754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484754).length < 2 ^ (prefixWord ++ tailWord_3484754).sum := by decide
  have hdescent : baseEnd_3484754 < baseStart_3484754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484778 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_3484778 : Nat := 118140960795 + 3484778 * 2 ^ 59
def prefixEnd_3484778 : Nat := 4983230072969 + 3 ^ 40 * 3484778 * 2
def baseEnd_3484778 : Nat := 397636908491927116388623

theorem tailTrace_3484778 : CollatzResearch.WordTrace tailWord_3484778 prefixEnd_3484778 397636908491927116388623 := by
  unfold tailWord_3484778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31775073842312983386245747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84733530246167955696655325 31775073842312983386245747)
  ·
    refine ⟨47662610763469475079368621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31775073842312983386245747 47662610763469475079368621)
    ·
      refine ⟨17873479036301053154763233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47662610763469475079368621 17873479036301053154763233)
      ·
        refine ⟨13405109277225789866072425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17873479036301053154763233 13405109277225789866072425)
        ·
          refine ⟨10053831957919342399554319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13405109277225789866072425 10053831957919342399554319)
          ·
            refine ⟨15080747936879013599331479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10053831957919342399554319 15080747936879013599331479)
            ·
              refine ⟨22621121905318520398997219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15080747936879013599331479 22621121905318520398997219)
              ·
                refine ⟨33931682857977780598495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22621121905318520398997219 33931682857977780598495829)
                ·
                  refine ⟨397636908491927116388623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33931682857977780598495829 397636908491927116388623)
                  ·
                    rfl

theorem cell22_3484778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_3484778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484778 prefixEnd_3484778 := by exact prefixLift 3484778
  have htrace : WordTrace (prefixWord ++ tailWord_3484778) baseStart_3484778 baseEnd_3484778 := by
    simpa [prefixWord, tailWord_3484778, baseEnd_3484778] using wordTrace_append hprefix tailTrace_3484778
  have hstable : (prefixWord ++ tailWord_3484778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484778).length < 2 ^ (prefixWord ++ tailWord_3484778).sum := by decide
  have hdescent : baseEnd_3484778 < baseStart_3484778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484810 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3484810 : Nat := 118140960795 + 3484810 * 2 ^ 59
def prefixEnd_3484810 : Nat := 4983230072969 + 3 ^ 40 * 3484810 * 2
def baseEnd_3484810 : Nat := 1192921679729743932365771

theorem tailTrace_3484810 : CollatzResearch.WordTrace tailWord_3484810 prefixEnd_3484810 1192921679729743932365771 := by
  unfold tailWord_3484810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31775365626284000752536971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84734308336757335340098589 31775365626284000752536971)
  ·
    refine ⟨47663048439426001128805457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31775365626284000752536971 47663048439426001128805457)
    ·
      refine ⟨35747286329569500846604093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47663048439426001128805457 35747286329569500846604093)
      ·
        refine ⟨13405232373588562817476535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35747286329569500846604093 13405232373588562817476535)
        ·
          refine ⟨20107848560382844226214803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13405232373588562817476535 20107848560382844226214803)
          ·
            refine ⟨30161772840574266339322205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20107848560382844226214803 30161772840574266339322205)
            ·
              refine ⟨11310664815215349877245827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30161772840574266339322205 11310664815215349877245827)
              ·
                refine ⟨16965997222823024815868741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11310664815215349877245827 16965997222823024815868741)
                ·
                  refine ⟨3181124479279317152975389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16965997222823024815868741 3181124479279317152975389)
                  ·
                    refine ⟨1192921679729743932365771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181124479279317152975389 1192921679729743932365771)
                    ·
                      rfl

theorem cell22_3484810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3484810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484810 prefixEnd_3484810 := by exact prefixLift 3484810
  have htrace : WordTrace (prefixWord ++ tailWord_3484810) baseStart_3484810 baseEnd_3484810 := by
    simpa [prefixWord, tailWord_3484810, baseEnd_3484810] using wordTrace_append hprefix tailTrace_3484810
  have hstable : (prefixWord ++ tailWord_3484810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484810).length < 2 ^ (prefixWord ++ tailWord_3484810).sum := by decide
  have hdescent : baseEnd_3484810 < baseStart_3484810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484872 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_3484872 : Nat := 118140960795 + 3484872 * 2 ^ 59
def prefixEnd_3484872 : Nat := 4983230072969 + 3 ^ 40 * 3484872 * 2
def baseEnd_3484872 : Nat := 1192942903596796437315581

theorem tailTrace_3484872 : CollatzResearch.WordTrace tailWord_3484872 prefixEnd_3484872 1192942903596796437315581 := by
  unfold tailWord_3484872
  simp only [CollatzResearch.WordTrace]
  refine ⟨63551861915455693799452435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84735815887274258399269913 63551861915455693799452435)
  ·
    refine ⟨95327792873183540699178653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63551861915455693799452435 95327792873183540699178653)
    ·
      refine ⟨35747922327443827762191995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95327792873183540699178653 35747922327443827762191995)
      ·
        refine ⟨53621883491165741643287993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35747922327443827762191995 53621883491165741643287993)
        ·
          refine ⟨40216412618374306232465995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53621883491165741643287993 40216412618374306232465995)
          ·
            refine ⟨60324618927561459348698993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40216412618374306232465995 60324618927561459348698993)
            ·
              refine ⟨45243464195671094511524245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60324618927561459348698993 45243464195671094511524245)
              ·
                refine ⟨2120787384172082555227699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45243464195671094511524245 2120787384172082555227699)
                ·
                  refine ⟨3181181076258123832841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2120787384172082555227699 3181181076258123832841549)
                  ·
                    refine ⟨1192942903596796437315581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181181076258123832841549 1192942903596796437315581)
                    ·
                      rfl

theorem cell22_3484872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_3484872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484872 prefixEnd_3484872 := by exact prefixLift 3484872
  have htrace : WordTrace (prefixWord ++ tailWord_3484872) baseStart_3484872 baseEnd_3484872 := by
    simpa [prefixWord, tailWord_3484872, baseEnd_3484872] using wordTrace_append hprefix tailTrace_3484872
  have hstable : (prefixWord ++ tailWord_3484872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484872).length < 2 ^ (prefixWord ++ tailWord_3484872).sum := by decide
  have hdescent : baseEnd_3484872 < baseStart_3484872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484928 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_3484928 : Nat := 118140960795 + 3484928 * 2 ^ 59
def prefixEnd_3484928 : Nat := 4983230072969 + 3 ^ 40 * 3484928 * 2
def baseEnd_3484928 : Nat := 1192962073541230957915409

theorem tailTrace_3484928 : CollatzResearch.WordTrace tailWord_3484928 prefixEnd_3484928 1192962073541230957915409 := by
  unfold tailWord_3484928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63552883159354254581471719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84737177545805672775295625 63552883159354254581471719)
  ·
    refine ⟨95329324739031381872207579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63552883159354254581471719 95329324739031381872207579)
    ·
      refine ⟨142993987108547072808311369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95329324739031381872207579 142993987108547072808311369)
      ·
        refine ⟨107245490331410304606233527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142993987108547072808311369 107245490331410304606233527)
        ·
          refine ⟨160868235497115456909350291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107245490331410304606233527 160868235497115456909350291)
          ·
            refine ⟨241302353245673185364025437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160868235497115456909350291 241302353245673185364025437)
            ·
              refine ⟨90488382467127444511509539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241302353245673185364025437 90488382467127444511509539)
              ·
                refine ⟨135732573700691166767264309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90488382467127444511509539 135732573700691166767264309)
                ·
                  refine ⟨12724928784439796884431029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135732573700691166767264309 12724928784439796884431029)
                  ·
                    refine ⟨1192962073541230957915409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12724928784439796884431029 1192962073541230957915409)
                    ·
                      rfl

theorem cell22_3484928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_3484928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484928 prefixEnd_3484928 := by exact prefixLift 3484928
  have htrace : WordTrace (prefixWord ++ tailWord_3484928) baseStart_3484928 baseEnd_3484928 := by
    simpa [prefixWord, tailWord_3484928, baseEnd_3484928] using wordTrace_append hprefix tailTrace_3484928
  have hstable : (prefixWord ++ tailWord_3484928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484928).length < 2 ^ (prefixWord ++ tailWord_3484928).sum := by decide
  have hdescent : baseEnd_3484928 < baseStart_3484928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484945 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_3484945 : Nat := 118140960795 + 3484945 * 2 ^ 59
def prefixEnd_3484945 : Nat := 4983230072969 + 3 ^ 40 * 3484945 * 2
def baseEnd_3484945 : Nat := 1192967892988648580240357

theorem tailTrace_3484945 : CollatzResearch.WordTrace tailWord_3484945 prefixEnd_3484945 1192967892988648580240357 := by
  unfold tailWord_3484945
  simp only [CollatzResearch.WordTrace]
  refine ⟨127106386359646921066312289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84737590906431280710874859 127106386359646921066312289)
  ·
    refine ⟨95329789769735190799734217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127106386359646921066312289 95329789769735190799734217)
    ·
      refine ⟨71497342327301393099800663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95329789769735190799734217 71497342327301393099800663)
      ·
        refine ⟨107246013490952089649700995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71497342327301393099800663 107246013490952089649700995)
        ·
          refine ⟨160869020236428134474551493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107246013490952089649700995 160869020236428134474551493)
          ·
            refine ⟨30162941294330275213978405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160869020236428134474551493 30162941294330275213978405)
            ·
              refine ⟨5655551492686926602620951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30162941294330275213978405 5655551492686926602620951)
              ·
                refine ⟨8483327239030389903931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5655551492686926602620951 8483327239030389903931427)
                ·
                  refine ⟨12724990858545584855897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8483327239030389903931427 12724990858545584855897141)
                  ·
                    refine ⟨1192967892988648580240357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12724990858545584855897141 1192967892988648580240357)
                    ·
                      rfl

theorem cell22_3484945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_3484945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484945 prefixEnd_3484945 := by exact prefixLift 3484945
  have htrace : WordTrace (prefixWord ++ tailWord_3484945) baseStart_3484945 baseEnd_3484945 := by
    simpa [prefixWord, tailWord_3484945, baseEnd_3484945] using wordTrace_append hprefix tailTrace_3484945
  have hstable : (prefixWord ++ tailWord_3484945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484945).length < 2 ^ (prefixWord ++ tailWord_3484945).sum := by decide
  have hdescent : baseEnd_3484945 < baseStart_3484945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3484979 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 2, 3]
def baseStart_3484979 : Nat := 118140960795 + 3484979 * 2 ^ 59
def prefixEnd_3484979 : Nat := 4983230072969 + 3 ^ 40 * 3484979 * 2
def baseEnd_3484979 : Nat := 1192979531883483824890253

theorem tailTrace_3484979 : CollatzResearch.WordTrace tailWord_3484979 prefixEnd_3484979 1192979531883483824890253 := by
  unfold tailWord_3484979
  simp only [CollatzResearch.WordTrace]
  refine ⟨127107626441523744873049991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84738417627682496582033327 127107626441523744873049991)
  ·
    refine ⟨190661439662285617309574987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127107626441523744873049991 190661439662285617309574987)
    ·
      refine ⟨285992159493428425964362481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190661439662285617309574987 285992159493428425964362481)
      ·
        refine ⟨214494119620071319473271861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285992159493428425964362481 214494119620071319473271861)
        ·
          refine ⟨20108823714381686200619237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214494119620071319473271861 20108823714381686200619237)
          ·
            refine ⟨3770404446446566162616107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20108823714381686200619237 3770404446446566162616107)
            ·
              refine ⟨5655606669669849243924161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770404446446566162616107 5655606669669849243924161)
              ·
                refine ⟨4241705002252386932943121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655606669669849243924161 4241705002252386932943121)
                ·
                  refine ⟨3181278751689290199707341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4241705002252386932943121 3181278751689290199707341)
                  ·
                    refine ⟨1192979531883483824890253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181278751689290199707341 1192979531883483824890253)
                    ·
                      rfl

theorem cell22_3484979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 3].length) (baseStart_3484979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3484979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3484979 prefixEnd_3484979 := by exact prefixLift 3484979
  have htrace : WordTrace (prefixWord ++ tailWord_3484979) baseStart_3484979 baseEnd_3484979 := by
    simpa [prefixWord, tailWord_3484979, baseEnd_3484979] using wordTrace_append hprefix tailTrace_3484979
  have hstable : (prefixWord ++ tailWord_3484979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3484979).length < 2 ^ (prefixWord ++ tailWord_3484979).sum := by decide
  have hdescent : baseEnd_3484979 < baseStart_3484979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3484979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485050 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_3485050 : Nat := 118140960795 + 3485050 * 2 ^ 59
def prefixEnd_3485050 : Nat := 4983230072969 + 3 ^ 40 * 3485050 * 2
def baseEnd_3485050 : Nat := 1193003836634463306365035

theorem tailTrace_3485050 : CollatzResearch.WordTrace tailWord_3485050 prefixEnd_3485050 1193003836634463306365035 := by
  unfold tailWord_3485050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777554006066630999721151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84740144016177682665923069 31777554006066630999721151)
  ·
    refine ⟨47666331009099946499581727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31777554006066630999721151 47666331009099946499581727)
    ·
      refine ⟨71499496513649919749372591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47666331009099946499581727 71499496513649919749372591)
      ·
        refine ⟨107249244770474879624058887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71499496513649919749372591 107249244770474879624058887)
        ·
          refine ⟨160873867155712319436088331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107249244770474879624058887 160873867155712319436088331)
          ·
            refine ⟨241310800733568479154132497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160873867155712319436088331 241310800733568479154132497)
            ·
              refine ⟨180983100550176359365599373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241310800733568479154132497 180983100550176359365599373)
              ·
                refine ⟨67868662706316134762099765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180983100550176359365599373 67868662706316134762099765)
                ·
                  refine ⟨6362687128717137633946853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67868662706316134762099765 6362687128717137633946853)
                  ·
                    refine ⟨1193003836634463306365035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6362687128717137633946853 1193003836634463306365035)
                    ·
                      rfl

theorem cell22_3485050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_3485050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485050 prefixEnd_3485050 := by exact prefixLift 3485050
  have htrace : WordTrace (prefixWord ++ tailWord_3485050) baseStart_3485050 baseEnd_3485050 := by
    simpa [prefixWord, tailWord_3485050, baseEnd_3485050] using wordTrace_append hprefix tailTrace_3485050
  have hstable : (prefixWord ++ tailWord_3485050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485050).length < 2 ^ (prefixWord ++ tailWord_3485050).sum := by decide
  have hdescent : baseEnd_3485050 < baseStart_3485050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485127 : List Nat := [1, 1, 4, 1, 1, 3, 5, 6]
def baseStart_3485127 : Nat := 118140960795 + 3485127 * 2 ^ 59
def prefixEnd_3485127 : Nat := 4983230072969 + 3 ^ 40 * 3485127 * 2
def baseEnd_3485127 : Nat := 132558910589784530243311

theorem tailTrace_3485127 : CollatzResearch.WordTrace tailWord_3485127 prefixEnd_3485127 132558910589784530243311 := by
  unfold tailWord_3485127
  simp only [CollatzResearch.WordTrace]
  refine ⟨127113024444987566149437635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84742016296658377432958423 127113024444987566149437635)
  ·
    refine ⟨190669536667481349224156453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127113024444987566149437635 190669536667481349224156453)
    ·
      refine ⟨35750538125152752979529335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190669536667481349224156453 35750538125152752979529335)
      ·
        refine ⟨53625807187729129469294003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35750538125152752979529335 53625807187729129469294003)
        ·
          refine ⟨80438710781593694203941005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53625807187729129469294003 80438710781593694203941005)
          ·
            refine ⟨30164516543097635326477877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80438710781593694203941005 30164516543097635326477877)
            ·
              refine ⟨2827923425915403311857301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30164516543097635326477877 2827923425915403311857301)
              ·
                refine ⟨132558910589784530243311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827923425915403311857301 132558910589784530243311)
                ·
                  rfl

theorem cell22_3485127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 6].length) (baseStart_3485127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485127 prefixEnd_3485127 := by exact prefixLift 3485127
  have htrace : WordTrace (prefixWord ++ tailWord_3485127) baseStart_3485127 baseEnd_3485127 := by
    simpa [prefixWord, tailWord_3485127, baseEnd_3485127] using wordTrace_append hprefix tailTrace_3485127
  have hstable : (prefixWord ++ tailWord_3485127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485127).length < 2 ^ (prefixWord ++ tailWord_3485127).sum := by decide
  have hdescent : baseEnd_3485127 < baseStart_3485127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485159 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3485159 : Nat := 118140960795 + 3485159 * 2 ^ 59
def prefixEnd_3485159 : Nat := 4983230072969 + 3 ^ 40 * 3485159 * 2
def baseEnd_3485159 : Nat := 1193041149562023355389701

theorem tailTrace_3485159 : CollatzResearch.WordTrace tailWord_3485159 prefixEnd_3485159 1193041149562023355389701 := by
  unfold tailWord_3485159
  simp only [CollatzResearch.WordTrace]
  refine ⟨127114191580871635614602531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84742794387247757076401687 127114191580871635614602531)
  ·
    refine ⟨190671287371307453421903797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127114191580871635614602531 190671287371307453421903797)
    ·
      refine ⟨17875433191060073758303481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190671287371307453421903797 17875433191060073758303481)
      ·
        refine ⟨13406574893295055318727611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17875433191060073758303481 13406574893295055318727611)
        ·
          refine ⟨20109862339942582978091417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406574893295055318727611 20109862339942582978091417)
          ·
            refine ⟨15082396754956937233568563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20109862339942582978091417 15082396754956937233568563)
            ·
              refine ⟨22623595132435405850352845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082396754956937233568563 22623595132435405850352845)
              ·
                refine ⟨8483848174663277193882317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22623595132435405850352845 8483848174663277193882317)
                ·
                  refine ⟨3181443065498728947705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8483848174663277193882317 3181443065498728947705869)
                  ·
                    refine ⟨1193041149562023355389701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181443065498728947705869 1193041149562023355389701)
                    ·
                      rfl

theorem cell22_3485159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3485159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485159 prefixEnd_3485159 := by exact prefixLift 3485159
  have htrace : WordTrace (prefixWord ++ tailWord_3485159) baseStart_3485159 baseEnd_3485159 := by
    simpa [prefixWord, tailWord_3485159, baseEnd_3485159] using wordTrace_append hprefix tailTrace_3485159
  have hstable : (prefixWord ++ tailWord_3485159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485159).length < 2 ^ (prefixWord ++ tailWord_3485159).sum := by decide
  have hdescent : baseEnd_3485159 < baseStart_3485159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485232 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_3485232 : Nat := 118140960795 + 3485232 * 2 ^ 59
def prefixEnd_3485232 : Nat := 4983230072969 + 3 ^ 40 * 3485232 * 2
def baseEnd_3485232 : Nat := 1193066138953875498314477

theorem tailTrace_3485232 : CollatzResearch.WordTrace tailWord_3485232 prefixEnd_3485232 1193066138953875498314477 := by
  unfold tailWord_3485232
  simp only [CollatzResearch.WordTrace]
  refine ⟨63558427054803584541004975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84744569406404779388006633 63558427054803584541004975)
  ·
    refine ⟨95337640582205376811507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63558427054803584541004975 95337640582205376811507463)
    ·
      refine ⟨143006460873308065217261195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95337640582205376811507463 143006460873308065217261195)
      ·
        refine ⟨214509691309962097825891793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143006460873308065217261195 214509691309962097825891793)
        ·
          refine ⟨160882268482471573369418845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214509691309962097825891793 160882268482471573369418845)
          ·
            refine ⟨60330850680926840013532067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160882268482471573369418845 60330850680926840013532067)
            ·
              refine ⟨90496276021390260020298101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60330850680926840013532067 90496276021390260020298101)
              ·
                refine ⟨8484025877005336876902947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90496276021390260020298101 8484025877005336876902947)
                ·
                  refine ⟨12726038815508005315354421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484025877005336876902947 12726038815508005315354421)
                  ·
                    refine ⟨1193066138953875498314477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12726038815508005315354421 1193066138953875498314477)
                    ·
                      rfl

theorem cell22_3485232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_3485232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485232 prefixEnd_3485232 := by exact prefixLift 3485232
  have htrace : WordTrace (prefixWord ++ tailWord_3485232) baseStart_3485232 baseEnd_3485232 := by
    simpa [prefixWord, tailWord_3485232, baseEnd_3485232] using wordTrace_append hprefix tailTrace_3485232
  have hstable : (prefixWord ++ tailWord_3485232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485232).length < 2 ^ (prefixWord ++ tailWord_3485232).sum := by decide
  have hdescent : baseEnd_3485232 < baseStart_3485232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485249 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3485249 : Nat := 118140960795 + 3485249 * 2 ^ 59
def prefixEnd_3485249 : Nat := 4983230072969 + 3 ^ 40 * 3485249 * 2
def baseEnd_3485249 : Nat := 1193071958401293120639425

theorem tailTrace_3485249 : CollatzResearch.WordTrace tailWord_3485249 prefixEnd_3485249 1193071958401293120639425 := by
  unfold tailWord_3485249
  simp only [CollatzResearch.WordTrace]
  refine ⟨127117474150545580985378801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84744982767030387323585867 127117474150545580985378801)
  ·
    refine ⟨95338105612909185739034101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127117474150545580985378801 95338105612909185739034101)
    ·
      refine ⟨8937947401210236163034447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95338105612909185739034101 8937947401210236163034447)
      ·
        refine ⟨13406921101815354244551671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8937947401210236163034447 13406921101815354244551671)
        ·
          refine ⟨20110381652723031366827507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13406921101815354244551671 20110381652723031366827507)
          ·
            refine ⟨30165572479084547050241261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20110381652723031366827507 30165572479084547050241261)
            ·
              refine ⟨11312089679656705143840473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30165572479084547050241261 11312089679656705143840473)
              ·
                refine ⟨8484067259742528857880355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312089679656705143840473 8484067259742528857880355)
                ·
                  refine ⟨12726100889613793286820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484067259742528857880355 12726100889613793286820533)
                  ·
                    refine ⟨1193071958401293120639425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12726100889613793286820533 1193071958401293120639425)
                    ·
                      rfl

theorem cell22_3485249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3485249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485249 prefixEnd_3485249 := by exact prefixLift 3485249
  have htrace : WordTrace (prefixWord ++ tailWord_3485249) baseStart_3485249 baseEnd_3485249 := by
    simpa [prefixWord, tailWord_3485249, baseEnd_3485249] using wordTrace_append hprefix tailTrace_3485249
  have hstable : (prefixWord ++ tailWord_3485249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485249).length < 2 ^ (prefixWord ++ tailWord_3485249).sum := by decide
  have hdescent : baseEnd_3485249 < baseStart_3485249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485266 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3485266 : Nat := 118140960795 + 3485266 * 2 ^ 59
def prefixEnd_3485266 : Nat := 4983230072969 + 3 ^ 40 * 3485266 * 2
def baseEnd_3485266 : Nat := 1193077777848710742964373

theorem tailTrace_3485266 : CollatzResearch.WordTrace tailWord_3485266 prefixEnd_3485266 1193077777848710742964373 := by
  unfold tailWord_3485266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31779523547870998222186913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84745396127655995259165101 31779523547870998222186913)
  ·
    refine ⟨23834642660903248666640185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31779523547870998222186913 23834642660903248666640185)
    ·
      refine ⟨17875981995677436499980139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23834642660903248666640185 17875981995677436499980139)
      ·
        refine ⟨26813972993516154749970209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17875981995677436499980139 26813972993516154749970209)
        ·
          refine ⟨20110479745137116062477657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26813972993516154749970209 20110479745137116062477657)
          ·
            refine ⟨15082859808852837046858243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20110479745137116062477657 15082859808852837046858243)
            ·
              refine ⟨22624289713279255570287365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15082859808852837046858243 22624289713279255570287365)
              ·
                refine ⟨4242054321239860419428881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22624289713279255570287365 4242054321239860419428881)
                ·
                  refine ⟨3181540740929895314571661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242054321239860419428881 3181540740929895314571661)
                  ·
                    refine ⟨1193077777848710742964373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181540740929895314571661 1193077777848710742964373)
                    ·
                      rfl

theorem cell22_3485266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3485266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485266 prefixEnd_3485266 := by exact prefixLift 3485266
  have htrace : WordTrace (prefixWord ++ tailWord_3485266) baseStart_3485266 baseEnd_3485266 := by
    simpa [prefixWord, tailWord_3485266, baseEnd_3485266] using wordTrace_append hprefix tailTrace_3485266
  have hstable : (prefixWord ++ tailWord_3485266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485266).length < 2 ^ (prefixWord ++ tailWord_3485266).sum := by decide
  have hdescent : baseEnd_3485266 < baseStart_3485266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485292 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3485292 : Nat := 118140960795 + 3485292 * 2 ^ 59
def prefixEnd_3485292 : Nat := 4983230072969 + 3 ^ 40 * 3485292 * 2
def baseEnd_3485292 : Nat := 1193086678180055341814293

theorem tailTrace_3485292 : CollatzResearch.WordTrace tailWord_3485292 prefixEnd_3485292 1193086678180055341814293 := by
  unfold tailWord_3485292
  simp only [CollatzResearch.WordTrace]
  refine ⟨63559521244694899664597065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84746028326259866219462753 63559521244694899664597065)
  ·
    refine ⟨47669640933521174748447799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63559521244694899664597065 47669640933521174748447799)
    ·
      refine ⟨71504461400281762122671699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47669640933521174748447799 71504461400281762122671699)
      ·
        refine ⟨107256692100422643184007549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71504461400281762122671699 107256692100422643184007549)
        ·
          refine ⟨40221259537658491194002831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107256692100422643184007549 40221259537658491194002831)
          ·
            refine ⟨60331889306487736791004247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40221259537658491194002831 60331889306487736791004247)
            ·
              refine ⟨90497833959731605186506371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60331889306487736791004247 90497833959731605186506371)
              ·
                refine ⟨135746750939597407779759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90497833959731605186506371 135746750939597407779759557)
                ·
                  refine ⟨25452515801174513958704917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135746750939597407779759557 25452515801174513958704917)
                  ·
                    refine ⟨1193086678180055341814293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25452515801174513958704917 1193086678180055341814293)
                    ·
                      rfl

theorem cell22_3485292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3485292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485292 prefixEnd_3485292 := by exact prefixLift 3485292
  have htrace : WordTrace (prefixWord ++ tailWord_3485292) baseStart_3485292 baseEnd_3485292 := by
    simpa [prefixWord, tailWord_3485292, baseEnd_3485292] using wordTrace_append hprefix tailTrace_3485292
  have hstable : (prefixWord ++ tailWord_3485292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485292).length < 2 ^ (prefixWord ++ tailWord_3485292).sum := by decide
  have hdescent : baseEnd_3485292 < baseStart_3485292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485307 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 7]
def baseStart_3485307 : Nat := 118140960795 + 3485307 * 2 ^ 59
def prefixEnd_3485307 : Nat := 4983230072969 + 3 ^ 40 * 3485307 * 2
def baseEnd_3485307 : Nat := 397697270995533434229749

theorem tailTrace_3485307 : CollatzResearch.WordTrace tailWord_3485307 prefixEnd_3485307 397697270995533434229749 := by
  unfold tailWord_3485307
  simp only [CollatzResearch.WordTrace]
  refine ⟨127119589584335456890990175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84746393056223637927326783 127119589584335456890990175)
  ·
    refine ⟨190679384376503185336485263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127119589584335456890990175 190679384376503185336485263)
    ·
      refine ⟨286019076564754778004727895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190679384376503185336485263 286019076564754778004727895)
      ·
        refine ⟨429028614847132167007091843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286019076564754778004727895 429028614847132167007091843)
        ·
          refine ⟨643542922270698250510637765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429028614847132167007091843 643542922270698250510637765)
          ·
            refine ⟨120664297925755921970744581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 643542922270698250510637765 120664297925755921970744581)
            ·
              refine ⟨22624555861079235369514609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120664297925755921970744581 22624555861079235369514609)
              ·
                refine ⟨16968416895809426527135957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22624555861079235369514609 16968416895809426527135957)
                ·
                  refine ⟨397697270995533434229749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16968416895809426527135957 397697270995533434229749)
                  ·
                    rfl

theorem cell22_3485307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_3485307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485307 prefixEnd_3485307 := by exact prefixLift 3485307
  have htrace : WordTrace (prefixWord ++ tailWord_3485307) baseStart_3485307 baseEnd_3485307 := by
    simpa [prefixWord, tailWord_3485307, baseEnd_3485307] using wordTrace_append hprefix tailTrace_3485307
  have hstable : (prefixWord ++ tailWord_3485307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485307).length < 2 ^ (prefixWord ++ tailWord_3485307).sum := by decide
  have hdescent : baseEnd_3485307 < baseStart_3485307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485337 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_3485337 : Nat := 118140960795 + 3485337 * 2 ^ 59
def prefixEnd_3485337 : Nat := 4983230072969 + 3 ^ 40 * 3485337 * 2
def baseEnd_3485337 : Nat := 1193102082599690224439155

theorem tailTrace_3485337 : CollatzResearch.WordTrace tailWord_3485337 prefixEnd_3485337 1193102082599690224439155 := by
  unfold tailWord_3485337
  simp only [CollatzResearch.WordTrace]
  refine ⟨127120683774226772014582265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84747122516151181343054843 127120683774226772014582265)
  ·
    refine ⟨95340512830670079010936699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127120683774226772014582265 95340512830670079010936699)
    ·
      refine ⟨143010769246005118516405049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95340512830670079010936699 143010769246005118516405049)
      ·
        refine ⟨107258076934503838887303787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143010769246005118516405049 107258076934503838887303787)
        ·
          refine ⟨160887115401755758330955681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107258076934503838887303787 160887115401755758330955681)
          ·
            refine ⟨120665336551316818748216761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160887115401755758330955681 120665336551316818748216761)
            ·
              refine ⟨90499002413487614061162571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120665336551316818748216761 90499002413487614061162571)
              ·
                refine ⟨135748503620231421091743857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90499002413487614061162571 135748503620231421091743857)
                ·
                  refine ⟨101811377715173565818807893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135748503620231421091743857 101811377715173565818807893)
                  ·
                    refine ⟨1193102082599690224439155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101811377715173565818807893 1193102082599690224439155)
                    ·
                      rfl

theorem cell22_3485337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_3485337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485337 prefixEnd_3485337 := by exact prefixLift 3485337
  have htrace : WordTrace (prefixWord ++ tailWord_3485337) baseStart_3485337 baseEnd_3485337 := by
    simpa [prefixWord, tailWord_3485337, baseEnd_3485337] using wordTrace_append hprefix tailTrace_3485337
  have hstable : (prefixWord ++ tailWord_3485337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485337).length < 2 ^ (prefixWord ++ tailWord_3485337).sum := by decide
  have hdescent : baseEnd_3485337 < baseStart_3485337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485399 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3485399 : Nat := 118140960795 + 3485399 * 2 ^ 59
def prefixEnd_3485399 : Nat := 4983230072969 + 3 ^ 40 * 3485399 * 2
def baseEnd_3485399 : Nat := 1193123306466742729388965

theorem tailTrace_3485399 : CollatzResearch.WordTrace tailWord_3485399 prefixEnd_3485399 1193123306466742729388965 := by
  unfold tailWord_3485399
  simp only [CollatzResearch.WordTrace]
  refine ⟨127122945100002156603339251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84748630066668104402226167 127122945100002156603339251)
  ·
    refine ⟨190684417650003234905008877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127122945100002156603339251 190684417650003234905008877)
    ·
      refine ⟨71506656618751213089378329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190684417650003234905008877 71506656618751213089378329)
      ·
        refine ⟨53629992464063409817033747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71506656618751213089378329 53629992464063409817033747)
        ·
          refine ⟨80444988696095114725550621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53629992464063409817033747 80444988696095114725550621)
          ·
            refine ⟨30166870761035668022081483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80444988696095114725550621 30166870761035668022081483)
            ·
              refine ⟨45250306141553502033122225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30166870761035668022081483 45250306141553502033122225)
              ·
                refine ⟨33937729606165126524841669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45250306141553502033122225 33937729606165126524841669)
                ·
                  refine ⟨6363324301155961223407813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33937729606165126524841669 6363324301155961223407813)
                  ·
                    refine ⟨1193123306466742729388965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363324301155961223407813 1193123306466742729388965)
                    ·
                      rfl

theorem cell22_3485399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3485399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485399 prefixEnd_3485399 := by exact prefixLift 3485399
  have htrace : WordTrace (prefixWord ++ tailWord_3485399) baseStart_3485399 baseEnd_3485399 := by
    simpa [prefixWord, tailWord_3485399, baseEnd_3485399] using wordTrace_append hprefix tailTrace_3485399
  have hstable : (prefixWord ++ tailWord_3485399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485399).length < 2 ^ (prefixWord ++ tailWord_3485399).sum := by decide
  have hdescent : baseEnd_3485399 < baseStart_3485399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485416 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3485416 : Nat := 118140960795 + 3485416 * 2 ^ 59
def prefixEnd_3485416 : Nat := 4983230072969 + 3 ^ 40 * 3485416 * 2
def baseEnd_3485416 : Nat := 1193129125914160351713913

theorem tailTrace_3485416 : CollatzResearch.WordTrace tailWord_3485416 prefixEnd_3485416 1193129125914160351713913 := by
  unfold tailWord_3485416
  simp only [CollatzResearch.WordTrace]
  refine ⟨63561782570470284253354051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84749043427293712337805401 63561782570470284253354051)
  ·
    refine ⟨95342673855705426380031077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63561782570470284253354051 95342673855705426380031077)
    ·
      refine ⟨17876751347944767446255827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95342673855705426380031077 17876751347944767446255827)
      ·
        refine ⟨26815127021917151169383741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17876751347944767446255827 26815127021917151169383741)
        ·
          refine ⟨10055672633218931688518903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26815127021917151169383741 10055672633218931688518903)
          ·
            refine ⟨15083508949828397532778355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055672633218931688518903 15083508949828397532778355)
            ·
              refine ⟨22625263424742596299167533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15083508949828397532778355 22625263424742596299167533)
              ·
                refine ⟨8484473784278473612187825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22625263424742596299167533 8484473784278473612187825)
                ·
                  refine ⟨6363355338208855209140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8484473784278473612187825 6363355338208855209140869)
                  ·
                    refine ⟨1193129125914160351713913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6363355338208855209140869 1193129125914160351713913)
                    ·
                      rfl

theorem cell22_3485416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3485416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485416 prefixEnd_3485416 := by exact prefixLift 3485416
  have htrace : WordTrace (prefixWord ++ tailWord_3485416) baseStart_3485416 baseEnd_3485416 := by
    simpa [prefixWord, tailWord_3485416, baseEnd_3485416] using wordTrace_append hprefix tailTrace_3485416
  have hstable : (prefixWord ++ tailWord_3485416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485416).length < 2 ^ (prefixWord ++ tailWord_3485416).sum := by decide
  have hdescent : baseEnd_3485416 < baseStart_3485416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485463 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 3, 3]
def baseStart_3485463 : Nat := 118140960795 + 3485463 * 2 ^ 59
def prefixEnd_3485463 : Nat := 4983230072969 + 3 ^ 40 * 3485463 * 2
def baseEnd_3485463 : Nat := 1193145214974667895788769

theorem tailTrace_3485463 : CollatzResearch.WordTrace tailWord_3485463 prefixEnd_3485463 1193145214974667895788769 := by
  unfold tailWord_3485463
  simp only [CollatzResearch.WordTrace]
  refine ⟨127125279371770295533669043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84750186247846863689112695 127125279371770295533669043)
  ·
    refine ⟨190687919057655443300503565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127125279371770295533669043 190687919057655443300503565)
    ·
      refine ⟨71507969646620791237688837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190687919057655443300503565 71507969646620791237688837)
      ·
        refine ⟨13407744308741398357066657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71507969646620791237688837 13407744308741398357066657)
        ·
          refine ⟨10055808231556048767799993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13407744308741398357066657 10055808231556048767799993)
          ·
            refine ⟨7541856173667036575849995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10055808231556048767799993 7541856173667036575849995)
            ·
              refine ⟨11312784260500554863774993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7541856173667036575849995 11312784260500554863774993)
              ·
                refine ⟨8484588195375416147831245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312784260500554863774993 8484588195375416147831245)
                ·
                  refine ⟨3181720573265781055436717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8484588195375416147831245 3181720573265781055436717)
                  ·
                    refine ⟨1193145214974667895788769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181720573265781055436717 1193145214974667895788769)
                    ·
                      rfl

theorem cell22_3485463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_3485463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485463 prefixEnd_3485463 := by exact prefixLift 3485463
  have htrace : WordTrace (prefixWord ++ tailWord_3485463) baseStart_3485463 baseEnd_3485463 := by
    simpa [prefixWord, tailWord_3485463, baseEnd_3485463] using wordTrace_append hprefix tailTrace_3485463
  have hstable : (prefixWord ++ tailWord_3485463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485463).length < 2 ^ (prefixWord ++ tailWord_3485463).sum := by decide
  have hdescent : baseEnd_3485463 < baseStart_3485463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485480 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3485480 : Nat := 118140960795 + 3485480 * 2 ^ 59
def prefixEnd_3485480 : Nat := 4983230072969 + 3 ^ 40 * 3485480 * 2
def baseEnd_3485480 : Nat := 1193151034422085518113717

theorem tailTrace_3485480 : CollatzResearch.WordTrace tailWord_3485480 prefixEnd_3485480 1193151034422085518113717 := by
  unfold tailWord_3485480
  simp only [CollatzResearch.WordTrace]
  refine ⟨63562949706354353718518947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84750599608472471624691929 63562949706354353718518947)
  ·
    refine ⟨95344424559531530577778421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63562949706354353718518947 95344424559531530577778421)
    ·
      refine ⟨8938539802456080991666727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95344424559531530577778421 8938539802456080991666727)
      ·
        refine ⟨13407809703684121487500091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8938539802456080991666727 13407809703684121487500091)
        ·
          refine ⟨20111714555526182231250137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13407809703684121487500091 20111714555526182231250137)
          ·
            refine ⟨15083785916644636673437603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20111714555526182231250137 15083785916644636673437603)
            ·
              refine ⟨22625678874966955010156405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15083785916644636673437603 22625678874966955010156405)
              ·
                refine ⟨2121157394528152032202163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22625678874966955010156405 2121157394528152032202163)
                ·
                  refine ⟨3181736091792228048303245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121157394528152032202163 3181736091792228048303245)
                  ·
                    refine ⟨1193151034422085518113717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181736091792228048303245 1193151034422085518113717)
                    ·
                      rfl

theorem cell22_3485480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3485480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485480 prefixEnd_3485480 := by exact prefixLift 3485480
  have htrace : WordTrace (prefixWord ++ tailWord_3485480) baseStart_3485480 baseEnd_3485480 := by
    simpa [prefixWord, tailWord_3485480, baseEnd_3485480] using wordTrace_append hprefix tailTrace_3485480
  have hstable : (prefixWord ++ tailWord_3485480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485480).length < 2 ^ (prefixWord ++ tailWord_3485480).sum := by decide
  have hdescent : baseEnd_3485480 < baseStart_3485480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485521 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 6]
def baseStart_3485521 : Nat := 118140960795 + 3485521 * 2 ^ 59
def prefixEnd_3485521 : Nat := 4983230072969 + 3 ^ 40 * 3485521 * 2
def baseEnd_3485521 : Nat := 397721689853325025946197

theorem tailTrace_3485521 : CollatzResearch.WordTrace tailWord_3485521 prefixEnd_3485521 397721689853325025946197 := by
  unfold tailWord_3485521
  simp only [CollatzResearch.WordTrace]
  refine ⟨127127394805560171439280417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84751596537040114292853611 127127394805560171439280417)
  ·
    refine ⟨95345546104170128579460313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127127394805560171439280417 95345546104170128579460313)
    ·
      refine ⟨71509159578127596434595235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95345546104170128579460313 71509159578127596434595235)
      ·
        refine ⟨107263739367191394651892853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71509159578127596434595235 107263739367191394651892853)
        ·
          refine ⟨10055975565674193248614955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107263739367191394651892853 10055975565674193248614955)
          ·
            refine ⟨15083963348511289872922433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10055975565674193248614955 15083963348511289872922433)
            ·
              refine ⟨11312972511383467404691825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15083963348511289872922433 11312972511383467404691825)
              ·
                refine ⟨8484729383537600553518869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11312972511383467404691825 8484729383537600553518869)
                ·
                  refine ⟨397721689853325025946197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8484729383537600553518869 397721689853325025946197)
                  ·
                    rfl

theorem cell22_3485521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_3485521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485521 prefixEnd_3485521 := by exact prefixLift 3485521
  have htrace : WordTrace (prefixWord ++ tailWord_3485521) baseStart_3485521 baseEnd_3485521 := by
    simpa [prefixWord, tailWord_3485521, baseEnd_3485521] using wordTrace_append hprefix tailTrace_3485521
  have hstable : (prefixWord ++ tailWord_3485521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485521).length < 2 ^ (prefixWord ++ tailWord_3485521).sum := by decide
  have hdescent : baseEnd_3485521 < baseStart_3485521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485553 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3485553 : Nat := 118140960795 + 3485553 * 2 ^ 59
def prefixEnd_3485553 : Nat := 4983230072969 + 3 ^ 40 * 3485553 * 2
def baseEnd_3485553 : Nat := 1193176023813937661038493

theorem tailTrace_3485553 : CollatzResearch.WordTrace tailWord_3485553 prefixEnd_3485553 1193176023813937661038493 := by
  unfold tailWord_3485553
  simp only [CollatzResearch.WordTrace]
  refine ⟨127128561941444240904445313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84752374627629493936296875 127128561941444240904445313)
  ·
    refine ⟨95346421456083180678333985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127128561941444240904445313 95346421456083180678333985)
    ·
      refine ⟨71509816092062385508750489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95346421456083180678333985 71509816092062385508750489)
      ·
        refine ⟨53632362069046789131562867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71509816092062385508750489 53632362069046789131562867)
        ·
          refine ⟨80448543103570183697344301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53632362069046789131562867 80448543103570183697344301)
          ·
            refine ⟨30168203663838818886504113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80448543103570183697344301 30168203663838818886504113)
            ·
              refine ⟨22626152747879114164878085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30168203663838818886504113 22626152747879114164878085)
              ·
                refine ⟨4242403640227333905914641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22626152747879114164878085 4242403640227333905914641)
                ·
                  refine ⟨3181802730170500429435981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4242403640227333905914641 3181802730170500429435981)
                  ·
                    refine ⟨1193176023813937661038493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181802730170500429435981 1193176023813937661038493)
                    ·
                      rfl

theorem cell22_3485553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3485553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485553 prefixEnd_3485553 := by exact prefixLift 3485553
  have htrace : WordTrace (prefixWord ++ tailWord_3485553) baseStart_3485553 baseEnd_3485553 := by
    simpa [prefixWord, tailWord_3485553, baseEnd_3485553] using wordTrace_append hprefix tailTrace_3485553
  have hstable : (prefixWord ++ tailWord_3485553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485553).length < 2 ^ (prefixWord ++ tailWord_3485553).sum := by decide
  have hdescent : baseEnd_3485553 < baseStart_3485553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485615 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 1, 3]
def baseStart_3485615 : Nat := 118140960795 + 3485615 * 2 ^ 59
def prefixEnd_3485615 : Nat := 4983230072969 + 3 ^ 40 * 3485615 * 2
def baseEnd_3485615 : Nat := 1193197247680990165988303

theorem tailTrace_3485615 : CollatzResearch.WordTrace tailWord_3485615 prefixEnd_3485615 1193197247680990165988303 := by
  unfold tailWord_3485615
  simp only [CollatzResearch.WordTrace]
  refine ⟨127130823267219625493202299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84753882178146416995468199 127130823267219625493202299)
  ·
    refine ⟨190696234900829438239803449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127130823267219625493202299 190696234900829438239803449)
    ·
      refine ⟨143022176175622078679852587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190696234900829438239803449 143022176175622078679852587)
      ·
        refine ⟨214533264263433118019778881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143022176175622078679852587 214533264263433118019778881)
        ·
          refine ⟨160899948197574838514834161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214533264263433118019778881 160899948197574838514834161)
          ·
            refine ⟨120674961148181128886125621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160899948197574838514834161 120674961148181128886125621)
            ·
              refine ⟨11313277607641980833074277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120674961148181128886125621 11313277607641980833074277)
              ·
                refine ⟨2121239551432871406201427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11313277607641980833074277 2121239551432871406201427)
                ·
                  refine ⟨3181859327149307109302141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121239551432871406201427 3181859327149307109302141)
                  ·
                    refine ⟨1193197247680990165988303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181859327149307109302141 1193197247680990165988303)
                    ·
                      rfl

theorem cell22_3485615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_3485615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485615 prefixEnd_3485615 := by exact prefixLift 3485615
  have htrace : WordTrace (prefixWord ++ tailWord_3485615) baseStart_3485615 baseEnd_3485615 := by
    simpa [prefixWord, tailWord_3485615, baseEnd_3485615] using wordTrace_append hprefix tailTrace_3485615
  have hstable : (prefixWord ++ tailWord_3485615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485615).length < 2 ^ (prefixWord ++ tailWord_3485615).sum := by decide
  have hdescent : baseEnd_3485615 < baseStart_3485615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485656 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_3485656 : Nat := 118140960795 + 3485656 * 2 ^ 59
def prefixEnd_3485656 : Nat := 4983230072969 + 3 ^ 40 * 3485656 * 2
def baseEnd_3485656 : Nat := 397737094272959908571059

theorem tailTrace_3485656 : CollatzResearch.WordTrace tailWord_3485656 prefixEnd_3485656 397737094272959908571059 := by
  unfold tailWord_3485656
  simp only [CollatzResearch.WordTrace]
  refine ⟨63566159330035544747722411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84754879106714059663629881 63566159330035544747722411)
  ·
    refine ⟨95349238995053317121583617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63566159330035544747722411 95349238995053317121583617)
    ·
      refine ⟨71511929246289987841187713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95349238995053317121583617 71511929246289987841187713)
      ·
        refine ⟨53633946934717490880890785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71511929246289987841187713 53633946934717490880890785)
        ·
          refine ⟨40225460201038118160668089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53633946934717490880890785 40225460201038118160668089)
          ·
            refine ⟨30169095150778588620501067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40225460201038118160668089 30169095150778588620501067)
            ·
              refine ⟨45253642726167882930751601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30169095150778588620501067 45253642726167882930751601)
              ·
                refine ⟨33940232044625912198063701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45253642726167882930751601 33940232044625912198063701)
                ·
                  refine ⟨397737094272959908571059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33940232044625912198063701 397737094272959908571059)
                  ·
                    rfl

theorem cell22_3485656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_3485656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485656 prefixEnd_3485656 := by exact prefixLift 3485656
  have htrace : WordTrace (prefixWord ++ tailWord_3485656) baseStart_3485656 baseEnd_3485656 := by
    simpa [prefixWord, tailWord_3485656, baseEnd_3485656] using wordTrace_append hprefix tailTrace_3485656
  have hstable : (prefixWord ++ tailWord_3485656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485656).length < 2 ^ (prefixWord ++ tailWord_3485656).sum := by decide
  have hdescent : baseEnd_3485656 < baseStart_3485656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485688 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_3485688 : Nat := 118140960795 + 3485688 * 2 ^ 59
def prefixEnd_3485688 : Nat := 4983230072969 + 3 ^ 40 * 3485688 * 2
def baseEnd_3485688 : Nat := 1193222237072842308913079

theorem tailTrace_3485688 : CollatzResearch.WordTrace tailWord_3485688 prefixEnd_3485688 1193222237072842308913079 := by
  unfold tailWord_3485688
  simp only [CollatzResearch.WordTrace]
  refine ⟨63566742897977579480304859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84755657197303439307073145 63566742897977579480304859)
  ·
    refine ⟨95350114346966369220457289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63566742897977579480304859 95350114346966369220457289)
    ·
      refine ⟨71512585760224776915342967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95350114346966369220457289 71512585760224776915342967)
      ·
        refine ⟨107268878640337165373014451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71512585760224776915342967 107268878640337165373014451)
        ·
          refine ⟨160903317960505748059521677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107268878640337165373014451 160903317960505748059521677)
          ·
            refine ⟨60338744235189655522320629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160903317960505748059521677 60338744235189655522320629)
            ·
              refine ⟨5656757272049030205217559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60338744235189655522320629 5656757272049030205217559)
              ·
                refine ⟨8485135908073545307826339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656757272049030205217559 8485135908073545307826339)
                ·
                  refine ⟨12727703862110317961739509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485135908073545307826339 12727703862110317961739509)
                  ·
                    refine ⟨1193222237072842308913079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12727703862110317961739509 1193222237072842308913079)
                    ·
                      rfl

theorem cell22_3485688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_3485688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485688 prefixEnd_3485688 := by exact prefixLift 3485688
  have htrace : WordTrace (prefixWord ++ tailWord_3485688) baseStart_3485688 baseEnd_3485688 := by
    simpa [prefixWord, tailWord_3485688, baseEnd_3485688] using wordTrace_append hprefix tailTrace_3485688
  have hstable : (prefixWord ++ tailWord_3485688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485688).length < 2 ^ (prefixWord ++ tailWord_3485688).sum := by decide
  have hdescent : baseEnd_3485688 < baseStart_3485688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485703 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3485703 : Nat := 118140960795 + 3485703 * 2 ^ 59
def prefixEnd_3485703 : Nat := 4983230072969 + 3 ^ 40 * 3485703 * 2
def baseEnd_3485703 : Nat := 1193227371879387269788033

theorem tailTrace_3485703 : CollatzResearch.WordTrace tailWord_3485703 prefixEnd_3485703 1193227371879387269788033 := by
  unfold tailWord_3485703
  simp only [CollatzResearch.WordTrace]
  refine ⟨127134032890900816522405763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84756021927267211014937175 127134032890900816522405763)
  ·
    refine ⟨190701049336351224783608645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127134032890900816522405763 190701049336351224783608645)
    ·
      refine ⟨35756446750565854646926621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190701049336351224783608645 35756446750565854646926621)
      ·
        refine ⟨13408667531462195492597483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35756446750565854646926621 13408667531462195492597483)
        ·
          refine ⟨20113001297193293238896225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13408667531462195492597483 20113001297193293238896225)
          ·
            refine ⟨15084750972894969929172169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113001297193293238896225 15084750972894969929172169)
            ·
              refine ⟨11313563229671227446879127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15084750972894969929172169 11313563229671227446879127)
              ·
                refine ⟨16970344844506841170318691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313563229671227446879127 16970344844506841170318691)
                ·
                  refine ⟨25455517266760261755478037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16970344844506841170318691 25455517266760261755478037)
                  ·
                    refine ⟨1193227371879387269788033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25455517266760261755478037 1193227371879387269788033)
                    ·
                      rfl

theorem cell22_3485703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3485703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485703 prefixEnd_3485703 := by exact prefixLift 3485703
  have htrace : WordTrace (prefixWord ++ tailWord_3485703) baseStart_3485703 baseEnd_3485703 := by
    simpa [prefixWord, tailWord_3485703, baseEnd_3485703] using wordTrace_append hprefix tailTrace_3485703
  have hstable : (prefixWord ++ tailWord_3485703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485703).length < 2 ^ (prefixWord ++ tailWord_3485703).sum := by decide
  have hdescent : baseEnd_3485703 < baseStart_3485703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485767 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3485767 : Nat := 118140960795 + 3485767 * 2 ^ 59
def prefixEnd_3485767 : Nat := 4983230072969 + 3 ^ 40 * 3485767 * 2
def baseEnd_3485767 : Nat := 1193249280387312436187837

theorem tailTrace_3485767 : CollatzResearch.WordTrace tailWord_3485767 prefixEnd_3485767 1193249280387312436187837 := by
  unfold tailWord_3485767
  simp only [CollatzResearch.WordTrace]
  refine ⟨127136367162668955452735555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84757578108445970301823703 127136367162668955452735555)
  ·
    refine ⟨190704550744003433179103333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127136367162668955452735555 190704550744003433179103333)
    ·
      refine ⟨35757103264500643721081875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190704550744003433179103333 35757103264500643721081875)
      ·
        refine ⟨53635654896750965581622813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35757103264500643721081875 53635654896750965581622813)
        ·
          refine ⟨20113370586281612093108555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53635654896750965581622813 20113370586281612093108555)
          ·
            refine ⟨30170055879422418139662833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20113370586281612093108555 30170055879422418139662833)
            ·
              refine ⟨22627541909566813604747125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30170055879422418139662833 22627541909566813604747125)
              ·
                refine ⟨2121332054021888775445043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22627541909566813604747125 2121332054021888775445043)
                ·
                  refine ⟨3181998081032833163167565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121332054021888775445043 3181998081032833163167565)
                  ·
                    refine ⟨1193249280387312436187837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3181998081032833163167565 1193249280387312436187837)
                    ·
                      rfl

theorem cell22_3485767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3485767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485767 prefixEnd_3485767 := by exact prefixLift 3485767
  have htrace : WordTrace (prefixWord ++ tailWord_3485767) baseStart_3485767 baseEnd_3485767 := by
    simpa [prefixWord, tailWord_3485767, baseEnd_3485767] using wordTrace_append hprefix tailTrace_3485767
  have hstable : (prefixWord ++ tailWord_3485767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485767).length < 2 ^ (prefixWord ++ tailWord_3485767).sum := by decide
  have hdescent : baseEnd_3485767 < baseStart_3485767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485782 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3485782 : Nat := 118140960795 + 3485782 * 2 ^ 59
def prefixEnd_3485782 : Nat := 4983230072969 + 3 ^ 40 * 3485782 * 2
def baseEnd_3485782 : Nat := 1193254415193857397062791

theorem tailTrace_3485782 : CollatzResearch.WordTrace tailWord_3485782 prefixEnd_3485782 1193254415193857397062791 := by
  unfold tailWord_3485782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946057141100913313408225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84757942838409742009687733 7946057141100913313408225)
  ·
    refine ⟨5959542855825684985056169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7946057141100913313408225 5959542855825684985056169)
    ·
      refine ⟨4469657141869263738792127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959542855825684985056169 4469657141869263738792127)
      ·
        refine ⟨6704485712803895608188191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469657141869263738792127 6704485712803895608188191)
        ·
          refine ⟨10056728569205843412282287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704485712803895608188191 10056728569205843412282287)
          ·
            refine ⟨15085092853808765118423431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056728569205843412282287 15085092853808765118423431)
            ·
              refine ⟨22627639280713147677635147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085092853808765118423431 22627639280713147677635147)
              ·
                refine ⟨33941458921069721516452721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22627639280713147677635147 33941458921069721516452721)
                ·
                  refine ⟨25456094190802291137339541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33941458921069721516452721 25456094190802291137339541)
                  ·
                    refine ⟨1193254415193857397062791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25456094190802291137339541 1193254415193857397062791)
                    ·
                      rfl

theorem cell22_3485782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3485782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485782 prefixEnd_3485782 := by exact prefixLift 3485782
  have htrace : WordTrace (prefixWord ++ tailWord_3485782) baseStart_3485782 baseEnd_3485782 := by
    simpa [prefixWord, tailWord_3485782, baseEnd_3485782] using wordTrace_append hprefix tailTrace_3485782
  have hstable : (prefixWord ++ tailWord_3485782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485782).length < 2 ^ (prefixWord ++ tailWord_3485782).sum := by decide
  have hdescent : baseEnd_3485782 < baseStart_3485782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485784 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_3485784 : Nat := 118140960795 + 3485784 * 2 ^ 59
def prefixEnd_3485784 : Nat := 4983230072969 + 3 ^ 40 * 3485784 * 2
def baseEnd_3485784 : Nat := 1193255099834730058512785

theorem tailTrace_3485784 : CollatzResearch.WordTrace tailWord_3485784 prefixEnd_3485784 1193255099834730058512785 := by
  unfold tailWord_3485784
  simp only [CollatzResearch.WordTrace]
  refine ⟨63568493601803683678052203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84757991469071578237402937 63568493601803683678052203)
  ·
    refine ⟨95352740402705525517078305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63568493601803683678052203 95352740402705525517078305)
    ·
      refine ⟨71514555302029144137808729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95352740402705525517078305 71514555302029144137808729)
      ·
        refine ⟨53635916476521858103356547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71514555302029144137808729 53635916476521858103356547)
        ·
          refine ⟨80453874714782787155034821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53635916476521858103356547 80453874714782787155034821)
          ·
            refine ⟨15085101509021772591569029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80453874714782787155034821 15085101509021772591569029)
            ·
              refine ⟨2828456532941582360919193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15085101509021772591569029 2828456532941582360919193)
              ·
                refine ⟨2121342399706186770689395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2828456532941582360919193 2121342399706186770689395)
                ·
                  refine ⟨3182013599559280156034093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121342399706186770689395 3182013599559280156034093)
                  ·
                    refine ⟨1193255099834730058512785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182013599559280156034093 1193255099834730058512785)
                    ·
                      rfl

theorem cell22_3485784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_3485784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485784 prefixEnd_3485784 := by exact prefixLift 3485784
  have htrace : WordTrace (prefixWord ++ tailWord_3485784) baseStart_3485784 baseEnd_3485784 := by
    simpa [prefixWord, tailWord_3485784, baseEnd_3485784] using wordTrace_append hprefix tailTrace_3485784
  have hstable : (prefixWord ++ tailWord_3485784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485784).length < 2 ^ (prefixWord ++ tailWord_3485784).sum := by decide
  have hdescent : baseEnd_3485784 < baseStart_3485784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485808 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_3485808 : Nat := 118140960795 + 3485808 * 2 ^ 59
def prefixEnd_3485808 : Nat := 4983230072969 + 3 ^ 40 * 3485808 * 2
def baseEnd_3485808 : Nat := 397754438508400665304237

theorem tailTrace_3485808 : CollatzResearch.WordTrace tailWord_3485808 prefixEnd_3485808 397754438508400665304237 := by
  unfold tailWord_3485808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63568931277760209727489039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84758575037013612969985385 63568931277760209727489039)
  ·
    refine ⟨95353396916640314591233559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63568931277760209727489039 95353396916640314591233559)
    ·
      refine ⟨143030095374960471886850339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95353396916640314591233559 143030095374960471886850339)
      ·
        refine ⟨214545143062440707830275509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143030095374960471886850339 214545143062440707830275509)
        ·
          refine ⟨20113607162103816359088329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214545143062440707830275509 20113607162103816359088329)
          ·
            refine ⟨15085205371577862269316247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113607162103816359088329 15085205371577862269316247)
            ·
              refine ⟨22627808057366793403974371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085205371577862269316247 22627808057366793403974371)
              ·
                refine ⟨33941712086050190105961557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22627808057366793403974371 33941712086050190105961557)
                ·
                  refine ⟨397754438508400665304237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33941712086050190105961557 397754438508400665304237)
                  ·
                    rfl

theorem cell22_3485808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_3485808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485808 prefixEnd_3485808 := by exact prefixLift 3485808
  have htrace : WordTrace (prefixWord ++ tailWord_3485808) baseStart_3485808 baseEnd_3485808 := by
    simpa [prefixWord, tailWord_3485808, baseEnd_3485808] using wordTrace_append hprefix tailTrace_3485808
  have hstable : (prefixWord ++ tailWord_3485808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485808).length < 2 ^ (prefixWord ++ tailWord_3485808).sum := by decide
  have hdescent : baseEnd_3485808 < baseStart_3485808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485810 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3485810 : Nat := 118140960795 + 3485810 * 2 ^ 59
def prefixEnd_3485810 : Nat := 4983230072969 + 3 ^ 40 * 3485810 * 2
def baseEnd_3485810 : Nat := 1193264000166074657362705

theorem tailTrace_3485810 : CollatzResearch.WordTrace tailWord_3485810 prefixEnd_3485810 1193264000166074657362705 := by
  unfold tailWord_3485810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784483875378293449137721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84758623667675449197700589 31784483875378293449137721)
  ·
    refine ⟨23838362906533720086853291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31784483875378293449137721 23838362906533720086853291)
    ·
      refine ⟨35757544359800580130279937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23838362906533720086853291 35757544359800580130279937)
      ·
        refine ⟨26818158269850435097709953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35757544359800580130279937 26818158269850435097709953)
        ·
          refine ⟨20113618702387826323282465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26818158269850435097709953 20113618702387826323282465)
          ·
            refine ⟨15085214026790869742461849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20113618702387826323282465 15085214026790869742461849)
            ·
              refine ⟨11313910520093152306846387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15085214026790869742461849 11313910520093152306846387)
              ·
                refine ⟨16970865780139728460269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11313910520093152306846387 16970865780139728460269581)
                ·
                  refine ⟨6364074667552398172601093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16970865780139728460269581 6364074667552398172601093)
                  ·
                    refine ⟨1193264000166074657362705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364074667552398172601093 1193264000166074657362705)
                    ·
                      rfl

theorem cell22_3485810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3485810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485810 prefixEnd_3485810 := by exact prefixLift 3485810
  have htrace : WordTrace (prefixWord ++ tailWord_3485810) baseStart_3485810 baseEnd_3485810 := by
    simpa [prefixWord, tailWord_3485810, baseEnd_3485810] using wordTrace_append hprefix tailTrace_3485810
  have hstable : (prefixWord ++ tailWord_3485810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485810).length < 2 ^ (prefixWord ++ tailWord_3485810).sum := by decide
  have hdescent : baseEnd_3485810 < baseStart_3485810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485827 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 1, 4]
def baseStart_3485827 : Nat := 118140960795 + 3485827 * 2 ^ 59
def prefixEnd_3485827 : Nat := 4983230072969 + 3 ^ 40 * 3485827 * 2
def baseEnd_3485827 : Nat := 1193269819613492279687653

theorem tailTrace_3485827 : CollatzResearch.WordTrace tailWord_3485827 prefixEnd_3485827 1193269819613492279687653 := by
  unfold tailWord_3485827
  simp only [CollatzResearch.WordTrace]
  refine ⟨127138555542451585699919735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84759037028301057133279823 127138555542451585699919735)
  ·
    refine ⟨190707833313677378549879603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127138555542451585699919735 190707833313677378549879603)
    ·
      refine ⟨286061749970516067824819405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190707833313677378549879603 286061749970516067824819405)
      ·
        refine ⟨107273156238943525434307277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286061749970516067824819405 107273156238943525434307277)
        ·
          refine ⟨40227433589603822037865229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107273156238943525434307277 40227433589603822037865229)
          ·
            refine ⟨15085287596101433264199461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40227433589603822037865229 15085287596101433264199461)
            ·
              refine ⟨2828491424269018737037399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15085287596101433264199461 2828491424269018737037399)
              ·
                refine ⟨4242737136403528105556099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828491424269018737037399 4242737136403528105556099)
                ·
                  refine ⟨6364105704605292158334149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4242737136403528105556099 6364105704605292158334149)
                  ·
                    refine ⟨1193269819613492279687653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364105704605292158334149 1193269819613492279687653)
                    ·
                      rfl

theorem cell22_3485827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 4].length) (baseStart_3485827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485827 prefixEnd_3485827 := by exact prefixLift 3485827
  have htrace : WordTrace (prefixWord ++ tailWord_3485827) baseStart_3485827 baseEnd_3485827 := by
    simpa [prefixWord, tailWord_3485827, baseEnd_3485827] using wordTrace_append hprefix tailTrace_3485827
  have hstable : (prefixWord ++ tailWord_3485827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485827).length < 2 ^ (prefixWord ++ tailWord_3485827).sum := by decide
  have hdescent : baseEnd_3485827 < baseStart_3485827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485840 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_3485840 : Nat := 118140960795 + 3485840 * 2 ^ 59
def prefixEnd_3485840 : Nat := 4983230072969 + 3 ^ 40 * 3485840 * 2
def baseEnd_3485840 : Nat := 1193274269779164579112613

theorem tailTrace_3485840 : CollatzResearch.WordTrace tailWord_3485840 prefixEnd_3485840 1193274269779164579112613 := by
  unfold tailWord_3485840
  simp only [CollatzResearch.WordTrace]
  refine ⟨63569514845702244460071487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84759353127602992613428649 63569514845702244460071487)
  ·
    refine ⟨95354272268553366690107231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63569514845702244460071487 95354272268553366690107231)
    ·
      refine ⟨143031408402830050035160847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95354272268553366690107231 143031408402830050035160847)
      ·
        refine ⟨214547112604245075052741271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143031408402830050035160847 214547112604245075052741271)
        ·
          refine ⟨321820668906367612579111907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214547112604245075052741271 321820668906367612579111907)
          ·
            refine ⟨482731003359551418868667861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321820668906367612579111907 482731003359551418868667861)
            ·
              refine ⟨11314007891239486379734403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 482731003359551418868667861 11314007891239486379734403)
              ·
                refine ⟨16971011836859229569601605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314007891239486379734403 16971011836859229569601605)
                ·
                  refine ⟨3182064719411105544300301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16971011836859229569601605 3182064719411105544300301)
                  ·
                    refine ⟨1193274269779164579112613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182064719411105544300301 1193274269779164579112613)
                    ·
                      rfl

theorem cell22_3485840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_3485840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485840 prefixEnd_3485840 := by exact prefixLift 3485840
  have htrace : WordTrace (prefixWord ++ tailWord_3485840) baseStart_3485840 baseEnd_3485840 := by
    simpa [prefixWord, tailWord_3485840, baseEnd_3485840] using wordTrace_append hprefix tailTrace_3485840
  have hstable : (prefixWord ++ tailWord_3485840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485840).length < 2 ^ (prefixWord ++ tailWord_3485840).sum := by decide
  have hdescent : baseEnd_3485840 < baseStart_3485840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485842 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3485842 : Nat := 118140960795 + 3485842 * 2 ^ 59
def prefixEnd_3485842 : Nat := 4983230072969 + 3 ^ 40 * 3485842 * 2
def baseEnd_3485842 : Nat := 397758318140012413520869

theorem tailTrace_3485842 : CollatzResearch.WordTrace tailWord_3485842 prefixEnd_3485842 397758318140012413520869 := by
  unfold tailWord_3485842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784775659349310815428945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84759401758264828841143853 31784775659349310815428945)
  ·
    refine ⟨23838581744511983111571709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31784775659349310815428945 23838581744511983111571709)
    ·
      refine ⟨8939468154191993666839391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23838581744511983111571709 8939468154191993666839391)
      ·
        refine ⟨13409202231287990500259087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939468154191993666839391 13409202231287990500259087)
        ·
          refine ⟨20113803346931985750388631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409202231287990500259087 20113803346931985750388631)
          ·
            refine ⟨30170705020397978625582947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20113803346931985750388631 30170705020397978625582947)
            ·
              refine ⟨45256057530596967938374421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30170705020397978625582947 45256057530596967938374421)
              ·
                refine ⟨2121377696746732872111301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45256057530596967938374421 2121377696746732872111301)
                ·
                  refine ⟨397758318140012413520869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121377696746732872111301 397758318140012413520869)
                  ·
                    rfl

theorem cell22_3485842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3485842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485842 prefixEnd_3485842 := by exact prefixLift 3485842
  have htrace : WordTrace (prefixWord ++ tailWord_3485842) baseStart_3485842 baseEnd_3485842 := by
    simpa [prefixWord, tailWord_3485842, baseEnd_3485842] using wordTrace_append hprefix tailTrace_3485842
  have hstable : (prefixWord ++ tailWord_3485842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485842).length < 2 ^ (prefixWord ++ tailWord_3485842).sum := by decide
  have hdescent : baseEnd_3485842 < baseStart_3485842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485855 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_3485855 : Nat := 118140960795 + 3485855 * 2 ^ 59
def prefixEnd_3485855 : Nat := 4983230072969 + 3 ^ 40 * 3485855 * 2
def baseEnd_3485855 : Nat := 1193279404585709539987567

theorem tailTrace_3485855 : CollatzResearch.WordTrace tailWord_3485855 prefixEnd_3485855 1193279404585709539987567 := by
  unfold tailWord_3485855
  simp only [CollatzResearch.WordTrace]
  refine ⟨127139576786350146481939019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84759717857566764321292679 127139576786350146481939019)
  ·
    refine ⟨190709365179525219722908529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127139576786350146481939019 190709365179525219722908529)
    ·
      refine ⟨143032023884643914792181397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190709365179525219722908529 143032023884643914792181397)
      ·
        refine ⟨6704626119592683505883503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143032023884643914792181397 6704626119592683505883503)
        ·
          refine ⟨10056939179389025258825255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704626119592683505883503 10056939179389025258825255)
          ·
            refine ⟨15085408769083537888237883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10056939179389025258825255 15085408769083537888237883)
            ·
              refine ⟨22628113153625306832356825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15085408769083537888237883 22628113153625306832356825)
              ·
                refine ⟨16971084865218980124267619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22628113153625306832356825 16971084865218980124267619)
                ·
                  refine ⟨25456627297828470186401429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16971084865218980124267619 25456627297828470186401429)
                  ·
                    refine ⟨1193279404585709539987567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25456627297828470186401429 1193279404585709539987567)
                    ·
                      rfl

theorem cell22_3485855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_3485855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485855 prefixEnd_3485855 := by exact prefixLift 3485855
  have htrace : WordTrace (prefixWord ++ tailWord_3485855) baseStart_3485855 baseEnd_3485855 := by
    simpa [prefixWord, tailWord_3485855, baseEnd_3485855] using wordTrace_append hprefix tailTrace_3485855
  have hstable : (prefixWord ++ tailWord_3485855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485855).length < 2 ^ (prefixWord ++ tailWord_3485855).sum := by decide
  have hdescent : baseEnd_3485855 < baseStart_3485855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485857 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3485857 : Nat := 118140960795 + 3485857 * 2 ^ 59
def prefixEnd_3485857 : Nat := 4983230072969 + 3 ^ 40 * 3485857 * 2
def baseEnd_3485857 : Nat := 1193280089226582201437561

theorem tailTrace_3485857 : CollatzResearch.WordTrace tailWord_3485857 prefixEnd_3485857 1193280089226582201437561 := by
  unfold tailWord_3485857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127139649732342900823511825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84759766488228600549007883 127139649732342900823511825)
  ·
    refine ⟨95354737299257175617633869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127139649732342900823511825 95354737299257175617633869)
    ·
      refine ⟨35758026487221440856612701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95354737299257175617633869 35758026487221440856612701)
      ·
        refine ⟨13409259932708040321229763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35758026487221440856612701 13409259932708040321229763)
        ·
          refine ⟨20113889899062060481844645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409259932708040321229763 20113889899062060481844645)
          ·
            refine ⟨3771354356074136340345871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20113889899062060481844645 3771354356074136340345871)
            ·
              refine ⟨5657031534111204510518807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771354356074136340345871 5657031534111204510518807)
              ·
                refine ⟨8485547301166806765778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657031534111204510518807 8485547301166806765778211)
                ·
                  refine ⟨12728320951750210148667317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8485547301166806765778211 12728320951750210148667317)
                  ·
                    refine ⟨1193280089226582201437561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12728320951750210148667317 1193280089226582201437561)
                    ·
                      rfl

theorem cell22_3485857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3485857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485857 prefixEnd_3485857 := by exact prefixLift 3485857
  have htrace : WordTrace (prefixWord ++ tailWord_3485857) baseStart_3485857 baseEnd_3485857 := by
    simpa [prefixWord, tailWord_3485857, baseEnd_3485857] using wordTrace_append hprefix tailTrace_3485857
  have hstable : (prefixWord ++ tailWord_3485857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485857).length < 2 ^ (prefixWord ++ tailWord_3485857).sum := by decide
  have hdescent : baseEnd_3485857 < baseStart_3485857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3485889 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3485889 : Nat := 118140960795 + 3485889 * 2 ^ 59
def prefixEnd_3485889 : Nat := 4983230072969 + 3 ^ 40 * 3485889 * 2
def baseEnd_3485889 : Nat := 1193291043480544784637463

theorem tailTrace_3485889 : CollatzResearch.WordTrace tailWord_3485889 prefixEnd_3485889 1193291043480544784637463 := by
  unfold tailWord_3485889
  simp only [CollatzResearch.WordTrace]
  refine ⟨127140816868226970288676721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84760544578817980192451147 127140816868226970288676721)
  ·
    refine ⟨95355612651170227716507541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127140816868226970288676721 95355612651170227716507541)
    ·
      refine ⟨4469794343023604424211291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95355612651170227716507541 4469794343023604424211291)
      ·
        refine ⟨6704691514535406636316937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469794343023604424211291 6704691514535406636316937)
        ·
          refine ⟨5028518635901554977237703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6704691514535406636316937 5028518635901554977237703)
          ·
            refine ⟨7542777953852332465856555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028518635901554977237703 7542777953852332465856555)
            ·
              refine ⟨11314166930778498698784833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7542777953852332465856555 11314166930778498698784833)
              ·
                refine ⟨8485625198083874024088625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11314166930778498698784833 8485625198083874024088625)
                ·
                  refine ⟨6364218898562905518066469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485625198083874024088625 6364218898562905518066469)
                  ·
                    refine ⟨1193291043480544784637463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364218898562905518066469 1193291043480544784637463)
                    ·
                      rfl

theorem cell22_3485889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3485889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3485889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3485889 prefixEnd_3485889 := by exact prefixLift 3485889
  have htrace : WordTrace (prefixWord ++ tailWord_3485889) baseStart_3485889 baseEnd_3485889 := by
    simpa [prefixWord, tailWord_3485889, baseEnd_3485889] using wordTrace_append hprefix tailTrace_3485889
  have hstable : (prefixWord ++ tailWord_3485889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3485889).length < 2 ^ (prefixWord ++ tailWord_3485889).sum := by decide
  have hdescent : baseEnd_3485889 < baseStart_3485889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3485889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486005 : List Nat := [1, 3, 3, 1, 2, 1, 11]
def baseStart_3486005 : Nat := 118140960795 + 3486005 * 2 ^ 59
def prefixEnd_3486005 : Nat := 4983230072969 + 3 ^ 40 * 3486005 * 2
def baseEnd_3486005 : Nat := 44197435283376264768041

theorem tailTrace_3486005 : CollatzResearch.WordTrace tailWord_3486005 prefixEnd_3486005 44197435283376264768041 := by
  unfold tailWord_3486005
  simp only [CollatzResearch.WordTrace]
  refine ⟨127145047735806722099899469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84763365157204481399932979 127145047735806722099899469)
  ·
    refine ⟨47679392900927520787462301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127145047735806722099899469 47679392900927520787462301)
    ·
      refine ⟨17879772337847820295298363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47679392900927520787462301 17879772337847820295298363)
      ·
        refine ⟨26819658506771730442947545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17879772337847820295298363 26819658506771730442947545)
        ·
          refine ⟨20114743880078797832210659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26819658506771730442947545 20114743880078797832210659)
          ·
            refine ⟨30172115820118196748315989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20114743880078797832210659 30172115820118196748315989)
            ·
              refine ⟨44197435283376264768041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30172115820118196748315989 44197435283376264768041)
              ·
                rfl

theorem cell22_3486005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 11].length) (baseStart_3486005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486005 prefixEnd_3486005 := by exact prefixLift 3486005
  have htrace : WordTrace (prefixWord ++ tailWord_3486005) baseStart_3486005 baseEnd_3486005 := by
    simpa [prefixWord, tailWord_3486005, baseEnd_3486005] using wordTrace_append hprefix tailTrace_3486005
  have hstable : (prefixWord ++ tailWord_3486005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486005).length < 2 ^ (prefixWord ++ tailWord_3486005).sum := by decide
  have hdescent : baseEnd_3486005 < baseStart_3486005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486009 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_3486009 : Nat := 118140960795 + 3486009 * 2 ^ 59
def prefixEnd_3486009 : Nat := 4983230072969 + 3 ^ 40 * 3486009 * 2
def baseEnd_3486009 : Nat := 1193332121932904471637095

theorem tailTrace_3486009 : CollatzResearch.WordTrace tailWord_3486009 prefixEnd_3486009 1193332121932904471637095 := by
  unfold tailWord_3486009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127145193627792230783045081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84763462418528153855363387 127145193627792230783045081)
  ·
    refine ⟨95358895220844173087283811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127145193627792230783045081 95358895220844173087283811)
    ·
      refine ⟨143038342831266259630925717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95358895220844173087283811 143038342831266259630925717)
      ·
        refine ⟨6704922320215605920199643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143038342831266259630925717 6704922320215605920199643)
        ·
          refine ⟨10057383480323408880299465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704922320215605920199643 10057383480323408880299465)
          ·
            refine ⟨7543037610242556660224599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10057383480323408880299465 7543037610242556660224599)
            ·
              refine ⟨11314556415363834990336899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543037610242556660224599 11314556415363834990336899)
              ·
                refine ⟨16971834623045752485505349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314556415363834990336899 16971834623045752485505349)
                ·
                  refine ⟨3182218991821078591032253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16971834623045752485505349 3182218991821078591032253)
                  ·
                    refine ⟨1193332121932904471637095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182218991821078591032253 1193332121932904471637095)
                    ·
                      rfl

theorem cell22_3486009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_3486009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486009 prefixEnd_3486009 := by exact prefixLift 3486009
  have htrace : WordTrace (prefixWord ++ tailWord_3486009) baseStart_3486009 baseEnd_3486009 := by
    simpa [prefixWord, tailWord_3486009, baseEnd_3486009] using wordTrace_append hprefix tailTrace_3486009
  have hstable : (prefixWord ++ tailWord_3486009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486009).length < 2 ^ (prefixWord ++ tailWord_3486009).sum := by decide
  have hdescent : baseEnd_3486009 < baseStart_3486009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486080 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_3486080 : Nat := 118140960795 + 3486080 * 2 ^ 59
def prefixEnd_3486080 : Nat := 4983230072969 + 3 ^ 40 * 3486080 * 2
def baseEnd_3486080 : Nat := 1193356426683883953111877

theorem tailTrace_3486080 : CollatzResearch.WordTrace tailWord_3486080 prefixEnd_3486080 1193356426683883953111877 := by
  unfold tailWord_3486080
  simp only [CollatzResearch.WordTrace]
  refine ⟨63573891605267504954439847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84765188807023339939253129 63573891605267504954439847)
  ·
    refine ⟨95360837407901257431659771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63573891605267504954439847 95360837407901257431659771)
    ·
      refine ⟨143041256111851886147489657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95360837407901257431659771 143041256111851886147489657)
      ·
        refine ⟨107280942083888914610617243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143041256111851886147489657 107280942083888914610617243)
        ·
          refine ⟨160921413125833371915925865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107280942083888914610617243 160921413125833371915925865)
          ·
            refine ⟨120691059844375028936944399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160921413125833371915925865 120691059844375028936944399)
            ·
              refine ⟨181036589766562543405416599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120691059844375028936944399 181036589766562543405416599)
              ·
                refine ⟨271554884649843815108124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181036589766562543405416599 271554884649843815108124899)
                ·
                  refine ⟨407332326974765722662187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271554884649843815108124899 407332326974765722662187349)
                  ·
                    refine ⟨1193356426683883953111877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 407332326974765722662187349 1193356426683883953111877)
                    ·
                      rfl

theorem cell22_3486080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_3486080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486080 prefixEnd_3486080 := by exact prefixLift 3486080
  have htrace : WordTrace (prefixWord ++ tailWord_3486080) baseStart_3486080 baseEnd_3486080 := by
    simpa [prefixWord, tailWord_3486080, baseEnd_3486080] using wordTrace_append hprefix tailTrace_3486080
  have hstable : (prefixWord ++ tailWord_3486080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486080).length < 2 ^ (prefixWord ++ tailWord_3486080).sum := by decide
  have hdescent : baseEnd_3486080 < baseStart_3486080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486122 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3486122 : Nat := 118140960795 + 3486122 * 2 ^ 59
def prefixEnd_3486122 : Nat := 4983230072969 + 3 ^ 40 * 3486122 * 2
def baseEnd_3486122 : Nat := 1193370804142209843561749

theorem tailTrace_3486122 : CollatzResearch.WordTrace tailWord_3486122 prefixEnd_3486122 1193370804142209843561749 := by
  unfold tailWord_3486122
  simp only [CollatzResearch.WordTrace]
  refine ⟨31787328769095712770477155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84766210050921900721272413 31787328769095712770477155)
  ·
    refine ⟨47680993153643569155715733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31787328769095712770477155 47680993153643569155715733)
    ·
      refine ⟨2235046554077042304174175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47680993153643569155715733 2235046554077042304174175)
      ·
        refine ⟨3352569831115563456261263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235046554077042304174175 3352569831115563456261263)
        ·
          refine ⟨5028854746673345184391895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352569831115563456261263 5028854746673345184391895)
          ·
            refine ⟨7543282120010017776587843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028854746673345184391895 7543282120010017776587843)
            ·
              refine ⟨11314923180015026664881765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7543282120010017776587843 11314923180015026664881765)
              ·
                refine ⟨2121548096252817499665331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11314923180015026664881765 2121548096252817499665331)
                ·
                  refine ⟨3182322144379226249497997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121548096252817499665331 3182322144379226249497997)
                  ·
                    refine ⟨1193370804142209843561749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182322144379226249497997 1193370804142209843561749)
                    ·
                      rfl

theorem cell22_3486122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3486122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486122 prefixEnd_3486122 := by exact prefixLift 3486122
  have htrace : WordTrace (prefixWord ++ tailWord_3486122) baseStart_3486122 baseEnd_3486122 := by
    simpa [prefixWord, tailWord_3486122, baseEnd_3486122] using wordTrace_append hprefix tailTrace_3486122
  have hstable : (prefixWord ++ tailWord_3486122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486122).length < 2 ^ (prefixWord ++ tailWord_3486122).sum := by decide
  have hdescent : baseEnd_3486122 < baseStart_3486122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486217 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_3486217 : Nat := 118140960795 + 3486217 * 2 ^ 59
def prefixEnd_3486217 : Nat := 4983230072969 + 3 ^ 40 * 3486217 * 2
def baseEnd_3486217 : Nat := 1193403324583661262436457

theorem tailTrace_3486217 : CollatzResearch.WordTrace tailWord_3486217 prefixEnd_3486217 1193403324583661262436457 := by
  unfold tailWord_3486217
  simp only [CollatzResearch.WordTrace]
  refine ⟨127152780011038682306616905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84768520007359121537744603 127152780011038682306616905)
  ·
    refine ⟨95364585008279011729962679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127152780011038682306616905 95364585008279011729962679)
    ·
      refine ⟨143046877512418517594944019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95364585008279011729962679 143046877512418517594944019)
      ·
        refine ⟨214570316268627776392416029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143046877512418517594944019 214570316268627776392416029)
        ·
          refine ⟨80463868600735416147156011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214570316268627776392416029 80463868600735416147156011)
          ·
            refine ⟨120695802901103124220734017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80463868600735416147156011 120695802901103124220734017)
            ·
              refine ⟨90521852175827343165550513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120695802901103124220734017 90521852175827343165550513)
              ·
                refine ⟨67891389131870507374162885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90521852175827343165550513 67891389131870507374162885)
                ·
                  refine ⟨12729635462225720132655541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67891389131870507374162885 12729635462225720132655541)
                  ·
                    refine ⟨1193403324583661262436457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12729635462225720132655541 1193403324583661262436457)
                    ·
                      rfl

theorem cell22_3486217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_3486217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486217 prefixEnd_3486217 := by exact prefixLift 3486217
  have htrace : WordTrace (prefixWord ++ tailWord_3486217) baseStart_3486217 baseEnd_3486217 := by
    simpa [prefixWord, tailWord_3486217, baseEnd_3486217] using wordTrace_append hprefix tailTrace_3486217
  have hstable : (prefixWord ++ tailWord_3486217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486217).length < 2 ^ (prefixWord ++ tailWord_3486217).sum := by decide
  have hdescent : baseEnd_3486217 < baseStart_3486217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486240 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_3486240 : Nat := 118140960795 + 3486240 * 2 ^ 59
def prefixEnd_3486240 : Nat := 4983230072969 + 3 ^ 40 * 3486240 * 2
def baseEnd_3486240 : Nat := 1193411197953696869111387

theorem tailTrace_3486240 : CollatzResearch.WordTrace tailWord_3486240 prefixEnd_3486240 1193411197953696869111387 := by
  unfold tailWord_3486240
  simp only [CollatzResearch.WordTrace]
  refine ⟨63576809444977678617352087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84769079259970238156469449 63576809444977678617352087)
  ·
    refine ⟨95365214167466517926028131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63576809444977678617352087 95365214167466517926028131)
    ·
      refine ⟨143047821251199776889042197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95365214167466517926028131 143047821251199776889042197)
      ·
        refine ⟨6705366621149989541673853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143047821251199776889042197 6705366621149989541673853)
        ·
          refine ⟨2514512482931246078127695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6705366621149989541673853 2514512482931246078127695)
          ·
            refine ⟨3771768724396869117191543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514512482931246078127695 3771768724396869117191543)
            ·
              refine ⟨5657653086595303675787315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771768724396869117191543 5657653086595303675787315)
              ·
                refine ⟨8486479629892955513680973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657653086595303675787315 8486479629892955513680973)
                ·
                  refine ⟨3182429861209858317630365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8486479629892955513680973 3182429861209858317630365)
                  ·
                    refine ⟨1193411197953696869111387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182429861209858317630365 1193411197953696869111387)
                    ·
                      rfl

theorem cell22_3486240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_3486240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486240 prefixEnd_3486240 := by exact prefixLift 3486240
  have htrace : WordTrace (prefixWord ++ tailWord_3486240) baseStart_3486240 baseEnd_3486240 := by
    simpa [prefixWord, tailWord_3486240, baseEnd_3486240] using wordTrace_append hprefix tailTrace_3486240
  have hstable : (prefixWord ++ tailWord_3486240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486240).length < 2 ^ (prefixWord ++ tailWord_3486240).sum := by decide
  have hdescent : baseEnd_3486240 < baseStart_3486240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486266 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_3486266 : Nat := 118140960795 + 3486266 * 2 ^ 59
def prefixEnd_3486266 : Nat := 4983230072969 + 3 ^ 40 * 3486266 * 2
def baseEnd_3486266 : Nat := 1193420098285041467961307

theorem tailTrace_3486266 : CollatzResearch.WordTrace tailWord_3486266 prefixEnd_3486266 1193420098285041467961307 := by
  unfold tailWord_3486266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788641796965290918787663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84769711458574109116767101 31788641796965290918787663)
  ·
    refine ⟨47682962695447936378181495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31788641796965290918787663 47682962695447936378181495)
    ·
      refine ⟨71524444043171904567272243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47682962695447936378181495 71524444043171904567272243)
      ·
        refine ⟨107286666064757856850908365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71524444043171904567272243 107286666064757856850908365)
        ·
          refine ⟨40232499774284196319090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107286666064757856850908365 40232499774284196319090637)
          ·
            refine ⟨15087187415356573619658989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40232499774284196319090637 15087187415356573619658989)
            ·
              refine ⟨5657695280758715107372121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15087187415356573619658989 5657695280758715107372121)
              ·
                refine ⟨4243271460569036330529091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657695280758715107372121 4243271460569036330529091)
                ·
                  refine ⟨6364907190853554495793637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243271460569036330529091 6364907190853554495793637)
                  ·
                    refine ⟨1193420098285041467961307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6364907190853554495793637 1193420098285041467961307)
                    ·
                      rfl

theorem cell22_3486266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_3486266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486266 prefixEnd_3486266 := by exact prefixLift 3486266
  have htrace : WordTrace (prefixWord ++ tailWord_3486266) baseStart_3486266 baseEnd_3486266 := by
    simpa [prefixWord, tailWord_3486266, baseEnd_3486266] using wordTrace_append hprefix tailTrace_3486266
  have hstable : (prefixWord ++ tailWord_3486266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486266).length < 2 ^ (prefixWord ++ tailWord_3486266).sum := by decide
  have hdescent : baseEnd_3486266 < baseStart_3486266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486279 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3486279 : Nat := 118140960795 + 3486279 * 2 ^ 59
def prefixEnd_3486279 : Nat := 4983230072969 + 3 ^ 40 * 3486279 * 2
def baseEnd_3486279 : Nat := 1193424548450713767386267

theorem tailTrace_3486279 : CollatzResearch.WordTrace tailWord_3486279 prefixEnd_3486279 1193424548450713767386267 := by
  unfold tailWord_3486279
  simp only [CollatzResearch.WordTrace]
  refine ⟨127155041336814066895373891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84770027557876044596915927 127155041336814066895373891)
  ·
    refine ⟨190732562005221100343060837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127155041336814066895373891 190732562005221100343060837)
    ·
      refine ⟨35762355375978956314323907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190732562005221100343060837 35762355375978956314323907)
      ·
        refine ⟨53643533063968434471485861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35762355375978956314323907 53643533063968434471485861)
        ·
          refine ⟨10058162449494081463403599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53643533063968434471485861 10058162449494081463403599)
          ·
            refine ⟨15087243674241122195105399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10058162449494081463403599 15087243674241122195105399)
            ·
              refine ⟨22630865511361683292658099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15087243674241122195105399 22630865511361683292658099)
              ·
                refine ⟨33946298267042524938987149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22630865511361683292658099 33946298267042524938987149)
                ·
                  refine ⟨12729861850140946852120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33946298267042524938987149 12729861850140946852120181)
                  ·
                    refine ⟨1193424548450713767386267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12729861850140946852120181 1193424548450713767386267)
                    ·
                      rfl

theorem cell22_3486279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3486279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486279 prefixEnd_3486279 := by exact prefixLift 3486279
  have htrace : WordTrace (prefixWord ++ tailWord_3486279) baseStart_3486279 baseEnd_3486279 := by
    simpa [prefixWord, tailWord_3486279, baseEnd_3486279] using wordTrace_append hprefix tailTrace_3486279
  have hstable : (prefixWord ++ tailWord_3486279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486279).length < 2 ^ (prefixWord ++ tailWord_3486279).sum := by decide
  have hdescent : baseEnd_3486279 < baseStart_3486279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486296 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_3486296 : Nat := 118140960795 + 3486296 * 2 ^ 59
def prefixEnd_3486296 : Nat := 4983230072969 + 3 ^ 40 * 3486296 * 2
def baseEnd_3486296 : Nat := 1193430367898131389711215

theorem tailTrace_3486296 : CollatzResearch.WordTrace tailWord_3486296 prefixEnd_3486296 1193430367898131389711215 := by
  unfold tailWord_3486296
  simp only [CollatzResearch.WordTrace]
  refine ⟨63577830688876239399371371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84770440918501652532495161 63577830688876239399371371)
  ·
    refine ⟨95366746033314359099057057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63577830688876239399371371 95366746033314359099057057)
    ·
      refine ⟨71525059524985769324292793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95366746033314359099057057 71525059524985769324292793)
      ·
        refine ⟨53643794643739326993219595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71525059524985769324292793 53643794643739326993219595)
        ·
          refine ⟨80465691965608990489829393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53643794643739326993219595 80465691965608990489829393)
          ·
            refine ⟨60349268974206742867372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80465691965608990489829393 60349268974206742867372045)
            ·
              refine ⟨22630975865327528575264517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60349268974206742867372045 22630975865327528575264517)
              ·
                refine ⟨4243307974748911607862097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22630975865327528575264517 4243307974748911607862097)
                ·
                  refine ⟨3182480981061683705896573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243307974748911607862097 3182480981061683705896573)
                  ·
                    refine ⟨1193430367898131389711215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182480981061683705896573 1193430367898131389711215)
                    ·
                      rfl

theorem cell22_3486296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_3486296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486296 prefixEnd_3486296 := by exact prefixLift 3486296
  have htrace : WordTrace (prefixWord ++ tailWord_3486296) baseStart_3486296 baseEnd_3486296 := by
    simpa [prefixWord, tailWord_3486296, baseEnd_3486296] using wordTrace_append hprefix tailTrace_3486296
  have hstable : (prefixWord ++ tailWord_3486296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486296).length < 2 ^ (prefixWord ++ tailWord_3486296).sum := by decide
  have hdescent : baseEnd_3486296 < baseStart_3486296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486435 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 1, 4]
def baseStart_3486435 : Nat := 118140960795 + 3486435 * 2 ^ 59
def prefixEnd_3486435 : Nat := 4983230072969 + 3 ^ 40 * 3486435 * 2
def baseEnd_3486435 : Nat := 1193477950438781360485789

theorem tailTrace_3486435 : CollatzResearch.WordTrace tailWord_3486435 prefixEnd_3486435 1193477950438781360485789 := by
  unfold tailWord_3486435
  simp only [CollatzResearch.WordTrace]
  refine ⟨127160731124248905538052759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84773820749499270358701839 127160731124248905538052759)
  ·
    refine ⟨190741096686373358307079139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127160731124248905538052759 190741096686373358307079139)
    ·
      refine ⟨286111645029560037460618709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190741096686373358307079139 286111645029560037460618709)
      ·
        refine ⟨6705741680380313377983251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 286111645029560037460618709 6705741680380313377983251)
        ·
          refine ⟨10058612520570470066974877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6705741680380313377983251 10058612520570470066974877)
          ·
            refine ⟨3771979695213926275115579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10058612520570470066974877 3771979695213926275115579)
            ·
              refine ⟨5657969542820889412673369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771979695213926275115579 5657969542820889412673369)
              ·
                refine ⟨4243477157115667059505027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657969542820889412673369 4243477157115667059505027)
                ·
                  refine ⟨6365215735673500589257541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243477157115667059505027 6365215735673500589257541)
                  ·
                    refine ⟨1193477950438781360485789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365215735673500589257541 1193477950438781360485789)
                    ·
                      rfl

theorem cell22_3486435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].length) (baseStart_3486435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486435 prefixEnd_3486435 := by exact prefixLift 3486435
  have htrace : WordTrace (prefixWord ++ tailWord_3486435) baseStart_3486435 baseEnd_3486435 := by
    simpa [prefixWord, tailWord_3486435, baseEnd_3486435] using wordTrace_append hprefix tailTrace_3486435
  have hstable : (prefixWord ++ tailWord_3486435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486435).length < 2 ^ (prefixWord ++ tailWord_3486435).sum := by decide
  have hdescent : baseEnd_3486435 < baseStart_3486435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_3486459 : Nat := 118140960795 + 3486459 * 2 ^ 59
def prefixEnd_3486459 : Nat := 4983230072969 + 3 ^ 40 * 3486459 * 2
def baseEnd_3486459 : Nat := 1193486166129253297885715

theorem tailTrace_3486459 : CollatzResearch.WordTrace tailWord_3486459 prefixEnd_3486459 1193486166129253297885715 := by
  unfold tailWord_3486459
  simp only [CollatzResearch.WordTrace]
  refine ⟨127161606476161957636926431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84774404317441305091284287 127161606476161957636926431)
  ·
    refine ⟨190742409714242936455389647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127161606476161957636926431 190742409714242936455389647)
    ·
      refine ⟨286113614571364404683084471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190742409714242936455389647 286113614571364404683084471)
      ·
        refine ⟨429170421857046607024626707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286113614571364404683084471 429170421857046607024626707)
        ·
          refine ⟨643755632785569910536940061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429170421857046607024626707 643755632785569910536940061)
          ·
            refine ⟨241408362294588716451352523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 643755632785569910536940061 241408362294588716451352523)
            ·
              refine ⟨362112543441883074677028785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241408362294588716451352523 362112543441883074677028785)
              ·
                refine ⟨271584407581412306007771589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362112543441883074677028785 271584407581412306007771589)
                ·
                  refine ⟨50922076421514807376457173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271584407581412306007771589 50922076421514807376457173)
                  ·
                    refine ⟨1193486166129253297885715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50922076421514807376457173 1193486166129253297885715)
                    ·
                      rfl

theorem cell22_3486459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_3486459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486459 prefixEnd_3486459 := by exact prefixLift 3486459
  have htrace : WordTrace (prefixWord ++ tailWord_3486459) baseStart_3486459 baseEnd_3486459 := by
    simpa [prefixWord, tailWord_3486459, baseEnd_3486459] using wordTrace_append hprefix tailTrace_3486459
  have hstable : (prefixWord ++ tailWord_3486459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486459).length < 2 ^ (prefixWord ++ tailWord_3486459).sum := by decide
  have hdescent : baseEnd_3486459 < baseStart_3486459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486540 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_3486540 : Nat := 118140960795 + 3486540 * 2 ^ 59
def prefixEnd_3486540 : Nat := 4983230072969 + 3 ^ 40 * 3486540 * 2
def baseEnd_3486540 : Nat := 397837964694865362203489

theorem tailTrace_3486540 : CollatzResearch.WordTrace tailWord_3486540 prefixEnd_3486540 397837964694865362203489 := by
  unfold tailWord_3486540
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582280394434254235312537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84776373859245672313750049 63582280394434254235312537)
  ·
    refine ⟨47686710295825690676484403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582280394434254235312537 47686710295825690676484403)
    ·
      refine ⟨71530065443738536014726605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47686710295825690676484403 71530065443738536014726605)
      ·
        refine ⟨26823774541401951005522477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71530065443738536014726605 26823774541401951005522477)
        ·
          refine ⟨10058915453025731627070929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26823774541401951005522477 10058915453025731627070929)
          ·
            refine ⟨7544186589769298720303197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10058915453025731627070929 7544186589769298720303197)
            ·
              refine ⟨2829069971163487020113699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7544186589769298720303197 2829069971163487020113699)
              ·
                refine ⟨4243604956745230530170549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829069971163487020113699 4243604956745230530170549)
                ·
                  refine ⟨397837964694865362203489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243604956745230530170549 397837964694865362203489)
                  ·
                    rfl

theorem cell22_3486540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_3486540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486540 prefixEnd_3486540 := by exact prefixLift 3486540
  have htrace : WordTrace (prefixWord ++ tailWord_3486540) baseStart_3486540 baseEnd_3486540 := by
    simpa [prefixWord, tailWord_3486540, baseEnd_3486540] using wordTrace_append hprefix tailTrace_3486540
  have hstable : (prefixWord ++ tailWord_3486540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486540).length < 2 ^ (prefixWord ++ tailWord_3486540).sum := by decide
  have hdescent : baseEnd_3486540 < baseStart_3486540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486553 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_3486553 : Nat := 118140960795 + 3486553 * 2 ^ 59
def prefixEnd_3486553 : Nat := 4983230072969 + 3 ^ 40 * 3486553 * 2
def baseEnd_3486553 : Nat := 1193518344250268386035427

theorem tailTrace_3486553 : CollatzResearch.WordTrace tailWord_3486553 prefixEnd_3486553 1193518344250268386035427 := by
  unfold tailWord_3486553
  simp only [CollatzResearch.WordTrace]
  refine ⟨127165034937821411690848313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84776689958547607793898875 127165034937821411690848313)
  ·
    refine ⟨95373776203366058768136235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127165034937821411690848313 95373776203366058768136235)
    ·
      refine ⟨143060664305049088152204353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95373776203366058768136235 143060664305049088152204353)
      ·
        refine ⟨107295498228786816114153265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143060664305049088152204353 107295498228786816114153265)
        ·
          refine ⟨80471623671590112085614949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107295498228786816114153265 80471623671590112085614949)
          ·
            refine ⟨15088429438423146016052803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80471623671590112085614949 15088429438423146016052803)
            ·
              refine ⟨22632644157634719024079205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15088429438423146016052803 22632644157634719024079205)
              ·
                refine ⟨4243620779556509817014851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22632644157634719024079205 4243620779556509817014851)
                ·
                  refine ⟨6365431169334764725522277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243620779556509817014851 6365431169334764725522277)
                  ·
                    refine ⟨1193518344250268386035427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365431169334764725522277 1193518344250268386035427)
                    ·
                      rfl

theorem cell22_3486553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_3486553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486553 prefixEnd_3486553 := by exact prefixLift 3486553
  have htrace : WordTrace (prefixWord ++ tailWord_3486553) baseStart_3486553 baseEnd_3486553 := by
    simpa [prefixWord, tailWord_3486553, baseEnd_3486553] using wordTrace_append hprefix tailTrace_3486553
  have hstable : (prefixWord ++ tailWord_3486553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486553).length < 2 ^ (prefixWord ++ tailWord_3486553).sum := by decide
  have hdescent : baseEnd_3486553 < baseStart_3486553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486645 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3486645 : Nat := 118140960795 + 3486645 * 2 ^ 59
def prefixEnd_3486645 : Nat := 4983230072969 + 3 ^ 40 * 3486645 * 2
def baseEnd_3486645 : Nat := 1193549837730410812735145

theorem tailTrace_3486645 : CollatzResearch.WordTrace tailWord_3486645 prefixEnd_3486645 1193549837730410812735145 := by
  unfold tailWord_3486645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127168390453488111403197389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84778926968992074268798259 127168390453488111403197389)
  ·
    refine ⟨47688146420058041776199021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127168390453488111403197389 47688146420058041776199021)
    ·
      refine ⟨17883054907521765666074633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47688146420058041776199021 17883054907521765666074633)
      ·
        refine ⟨13412291180641324249555975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17883054907521765666074633 13412291180641324249555975)
        ·
          refine ⟨20118436770961986374333963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412291180641324249555975 20118436770961986374333963)
          ·
            refine ⟨30177655156442979561500945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118436770961986374333963 30177655156442979561500945)
            ·
              refine ⟨22633241367332234671125709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30177655156442979561500945 22633241367332234671125709)
              ·
                refine ⟨8487465512749588001672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22633241367332234671125709 8487465512749588001672141)
                ·
                  refine ⟨3182799567281095500627053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8487465512749588001672141 3182799567281095500627053)
                  ·
                    refine ⟨1193549837730410812735145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3182799567281095500627053 1193549837730410812735145)
                    ·
                      rfl

theorem cell22_3486645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3486645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486645 prefixEnd_3486645 := by exact prefixLift 3486645
  have htrace : WordTrace (prefixWord ++ tailWord_3486645) baseStart_3486645 baseEnd_3486645 := by
    simpa [prefixWord, tailWord_3486645, baseEnd_3486645] using wordTrace_append hprefix tailTrace_3486645
  have hstable : (prefixWord ++ tailWord_3486645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486645).length < 2 ^ (prefixWord ++ tailWord_3486645).sum := by decide
  have hdescent : baseEnd_3486645 < baseStart_3486645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486703 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 6]
def baseStart_3486703 : Nat := 118140960795 + 3486703 * 2 ^ 59
def prefixEnd_3486703 : Nat := 4983230072969 + 3 ^ 40 * 3486703 * 2
def baseEnd_3486703 : Nat := 397856564105239331594989

theorem tailTrace_3486703 : CollatzResearch.WordTrace tailWord_3486703 prefixEnd_3486703 397856564105239331594989 := by
  unfold tailWord_3486703
  simp only [CollatzResearch.WordTrace]
  refine ⟨127170505887277987308808763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84780337258185324872539175 127170505887277987308808763)
  ·
    refine ⟨190755758830916980963213145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127170505887277987308808763 190755758830916980963213145)
    ·
      refine ⟨143066819123187735722409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190755758830916980963213145 143066819123187735722409859)
      ·
        refine ⟨214600228684781603583614789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143066819123187735722409859 214600228684781603583614789)
        ·
          refine ⟨40237542878396550671927773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214600228684781603583614789 40237542878396550671927773)
          ·
            refine ⟨15089078579398706501972915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40237542878396550671927773 15089078579398706501972915)
            ·
              refine ⟨22633617869098059752959373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15089078579398706501972915 22633617869098059752959373)
              ·
                refine ⟨8487606700911772407359765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22633617869098059752959373 8487606700911772407359765)
                ·
                  refine ⟨397856564105239331594989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8487606700911772407359765 397856564105239331594989)
                  ·
                    rfl

theorem cell22_3486703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_3486703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486703 prefixEnd_3486703 := by exact prefixLift 3486703
  have htrace : WordTrace (prefixWord ++ tailWord_3486703) baseStart_3486703 baseEnd_3486703 := by
    simpa [prefixWord, tailWord_3486703, baseEnd_3486703] using wordTrace_append hprefix tailTrace_3486703
  have hstable : (prefixWord ++ tailWord_3486703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486703).length < 2 ^ (prefixWord ++ tailWord_3486703).sum := by decide
  have hdescent : baseEnd_3486703 < baseStart_3486703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486754 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3486754 : Nat := 118140960795 + 3486754 * 2 ^ 59
def prefixEnd_3486754 : Nat := 4983230072969 + 3 ^ 40 * 3486754 * 2
def baseEnd_3486754 : Nat := 397862383552656953919937

theorem tailTrace_3486754 : CollatzResearch.WordTrace tailWord_3486754 prefixEnd_3486754 397862383552656953919937 := by
  unfold tailWord_3486754
  simp only [CollatzResearch.WordTrace]
  refine ⟨31793091502523305754728829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84781577340062148679276877 31793091502523305754728829)
  ·
    refine ⟨11922409313446239658023311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31793091502523305754728829 11922409313446239658023311)
    ·
      refine ⟨17883613970169359487034967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922409313446239658023311 17883613970169359487034967)
      ·
        refine ⟨26825420955254039230552451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17883613970169359487034967 26825420955254039230552451)
        ·
          refine ⟨40238131432881058845828677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26825420955254039230552451 40238131432881058845828677)
          ·
            refine ⟨7544649643665198533592877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40238131432881058845828677 7544649643665198533592877)
            ·
              refine ⟨2829243616374449450097329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7544649643665198533592877 2829243616374449450097329)
              ·
                refine ⟨2121932712280837087572997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829243616374449450097329 2121932712280837087572997)
                ·
                  refine ⟨397862383552656953919937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121932712280837087572997 397862383552656953919937)
                  ·
                    rfl

theorem cell22_3486754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3486754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486754 prefixEnd_3486754 := by exact prefixLift 3486754
  have htrace : WordTrace (prefixWord ++ tailWord_3486754) baseStart_3486754 baseEnd_3486754 := by
    simpa [prefixWord, tailWord_3486754, baseEnd_3486754] using wordTrace_append hprefix tailTrace_3486754
  have hstable : (prefixWord ++ tailWord_3486754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486754).length < 2 ^ (prefixWord ++ tailWord_3486754).sum := by decide
  have hdescent : baseEnd_3486754 < baseStart_3486754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486793 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 7]
def baseStart_3486793 : Nat := 118140960795 + 3486793 * 2 ^ 59
def prefixEnd_3486793 : Nat := 4983230072969 + 3 ^ 40 * 3486793 * 2
def baseEnd_3486793 : Nat := 397866833718329253344897

theorem tailTrace_3486793 : CollatzResearch.WordTrace tailWord_3486793 prefixEnd_3486793 397866833718329253344897 := by
  unfold tailWord_3486793
  simp only [CollatzResearch.WordTrace]
  refine ⟨127173788456951932679585033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84782525637967955119723355 127173788456951932679585033)
  ·
    refine ⟨95380341342713949509688775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127173788456951932679585033 95380341342713949509688775)
    ·
      refine ⟨143070512014070924264533163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95380341342713949509688775 143070512014070924264533163)
      ·
        refine ⟨214605768021106386396799745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143070512014070924264533163 214605768021106386396799745)
        ·
          refine ⟨160954326015829789797599809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214605768021106386396799745 160954326015829789797599809)
          ·
            refine ⟨120715744511872342348199857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160954326015829789797599809 120715744511872342348199857)
            ·
              refine ⟨90536808383904256761149893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120715744511872342348199857 90536808383904256761149893)
              ·
                refine ⟨16975651571982048142715605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90536808383904256761149893 16975651571982048142715605)
                ·
                  refine ⟨397866833718329253344897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16975651571982048142715605 397866833718329253344897)
                  ·
                    rfl

theorem cell22_3486793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_3486793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486793 prefixEnd_3486793 := by exact prefixLift 3486793
  have htrace : WordTrace (prefixWord ++ tailWord_3486793) baseStart_3486793 baseEnd_3486793 := by
    simpa [prefixWord, tailWord_3486793, baseEnd_3486793] using wordTrace_append hprefix tailTrace_3486793
  have hstable : (prefixWord ++ tailWord_3486793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486793).length < 2 ^ (prefixWord ++ tailWord_3486793).sum := by decide
  have hdescent : baseEnd_3486793 < baseStart_3486793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486825 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_3486825 : Nat := 118140960795 + 3486825 * 2 ^ 59
def prefixEnd_3486825 : Nat := 4983230072969 + 3 ^ 40 * 3486825 * 2
def baseEnd_3486825 : Nat := 1193611455408950343234593

theorem tailTrace_3486825 : CollatzResearch.WordTrace tailWord_3486825 prefixEnd_3486825 1193611455408950343234593 := by
  unfold tailWord_3486825
  simp only [CollatzResearch.WordTrace]
  refine ⟨127174955592836002144749929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84783303728557334763166619 127174955592836002144749929)
  ·
    refine ⟨95381216694627001608562447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127174955592836002144749929 95381216694627001608562447)
    ·
      refine ⟨143071825041940502412843671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95381216694627001608562447 143071825041940502412843671)
      ·
        refine ⟨214607737562910753619265507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143071825041940502412843671 214607737562910753619265507)
        ·
          refine ⟨321911606344366130428898261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214607737562910753619265507 321911606344366130428898261)
          ·
            refine ⟨7544803273696081181927303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 321911606344366130428898261 7544803273696081181927303)
            ·
              refine ⟨11317204910544121772890955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544803273696081181927303 11317204910544121772890955)
              ·
                refine ⟨16975807365816182659336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11317204910544121772890955 16975807365816182659336433)
                ·
                  refine ⟨12731855524362136994502325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16975807365816182659336433 12731855524362136994502325)
                  ·
                    refine ⟨1193611455408950343234593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12731855524362136994502325 1193611455408950343234593)
                    ·
                      rfl

theorem cell22_3486825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_3486825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486825 prefixEnd_3486825 := by exact prefixLift 3486825
  have htrace : WordTrace (prefixWord ++ tailWord_3486825) baseStart_3486825 baseEnd_3486825 := by
    simpa [prefixWord, tailWord_3486825, baseEnd_3486825] using wordTrace_append hprefix tailTrace_3486825
  have hstable : (prefixWord ++ tailWord_3486825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486825).length < 2 ^ (prefixWord ++ tailWord_3486825).sum := by decide
  have hdescent : baseEnd_3486825 < baseStart_3486825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486840 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_3486840 : Nat := 118140960795 + 3486840 * 2 ^ 59
def prefixEnd_3486840 : Nat := 4983230072969 + 3 ^ 40 * 3486840 * 2
def baseEnd_3486840 : Nat := 1193616590215495304109547

theorem tailTrace_3486840 : CollatzResearch.WordTrace tailWord_3486840 prefixEnd_3486840 1193616590215495304109547 := by
  unfold tailWord_3486840
  simp only [CollatzResearch.WordTrace]
  refine ⟨63587751343890829853272987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84783668458521106471030649 63587751343890829853272987)
  ·
    refine ⟨95381627015836244779909481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63587751343890829853272987 95381627015836244779909481)
    ·
      refine ⟨71536220261877183584932111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95381627015836244779909481 71536220261877183584932111)
      ·
        refine ⟨107304330392815775377398167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71536220261877183584932111 107304330392815775377398167)
        ·
          refine ⟨160956495589223663066097251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107304330392815775377398167 160956495589223663066097251)
          ·
            refine ⟨241434743383835494599145877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160956495589223663066097251 241434743383835494599145877)
            ·
              refine ⟨11317253596117288809334963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241434743383835494599145877 11317253596117288809334963)
              ·
                refine ⟨16975880394175933214002445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11317253596117288809334963 16975880394175933214002445)
                ·
                  refine ⟨6365955147815974955250917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16975880394175933214002445 6365955147815974955250917)
                  ·
                    refine ⟨1193616590215495304109547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365955147815974955250917 1193616590215495304109547)
                    ·
                      rfl

theorem cell22_3486840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_3486840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486840 prefixEnd_3486840 := by exact prefixLift 3486840
  have htrace : WordTrace (prefixWord ++ tailWord_3486840) baseStart_3486840 baseEnd_3486840 := by
    simpa [prefixWord, tailWord_3486840, baseEnd_3486840] using wordTrace_append hprefix tailTrace_3486840
  have hstable : (prefixWord ++ tailWord_3486840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486840).length < 2 ^ (prefixWord ++ tailWord_3486840).sum := by decide
  have hdescent : baseEnd_3486840 < baseStart_3486840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486857 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_3486857 : Nat := 118140960795 + 3486857 * 2 ^ 59
def prefixEnd_3486857 : Nat := 4983230072969 + 3 ^ 40 * 3486857 * 2
def baseEnd_3486857 : Nat := 1193622409662912926434495

theorem tailTrace_3486857 : CollatzResearch.WordTrace tailWord_3486857 prefixEnd_3486857 1193622409662912926434495 := by
  unfold tailWord_3486857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127176122728720071609914825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84784081819146714406609883 127176122728720071609914825)
  ·
    refine ⟨95382092046540053707436119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127176122728720071609914825 95382092046540053707436119)
    ·
      refine ⟨143073138069810080561154179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95382092046540053707436119 143073138069810080561154179)
      ·
        refine ⟨214609707104715120841731269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143073138069810080561154179 214609707104715120841731269)
        ·
          refine ⟨40239320082134085157824613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214609707104715120841731269 40239320082134085157824613)
          ·
            refine ⟨7544872515400140967092115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40239320082134085157824613 7544872515400140967092115)
            ·
              refine ⟨11317308773100211450638173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544872515400140967092115 11317308773100211450638173)
              ·
                refine ⟨4243990789912579293989315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11317308773100211450638173 4243990789912579293989315)
                ·
                  refine ⟨6365986184868868940983973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243990789912579293989315 6365986184868868940983973)
                  ·
                    refine ⟨1193622409662912926434495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365986184868868940983973 1193622409662912926434495)
                    ·
                      rfl

theorem cell22_3486857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_3486857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486857 prefixEnd_3486857 := by exact prefixLift 3486857
  have htrace : WordTrace (prefixWord ++ tailWord_3486857) baseStart_3486857 baseEnd_3486857 := by
    simpa [prefixWord, tailWord_3486857, baseEnd_3486857] using wordTrace_append hprefix tailTrace_3486857
  have hstable : (prefixWord ++ tailWord_3486857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486857).length < 2 ^ (prefixWord ++ tailWord_3486857).sum := by decide
  have hdescent : baseEnd_3486857 < baseStart_3486857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486872 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_3486872 : Nat := 118140960795 + 3486872 * 2 ^ 59
def prefixEnd_3486872 : Nat := 4983230072969 + 3 ^ 40 * 3486872 * 2
def baseEnd_3486872 : Nat := 397875848156485962436483

theorem tailTrace_3486872 : CollatzResearch.WordTrace tailWord_3486872 prefixEnd_3486872 397875848156485962436483 := by
  unfold tailWord_3486872
  simp only [CollatzResearch.WordTrace]
  refine ⟨63588334911832864585855435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84784446549110486114473913 63588334911832864585855435)
  ·
    refine ⟨95382502367749296878783153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63588334911832864585855435 95382502367749296878783153)
    ·
      refine ⟨71536876775811972659087365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95382502367749296878783153 71536876775811972659087365)
      ·
        refine ⟨13413164395464744873578881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71536876775811972659087365 13413164395464744873578881)
        ·
          refine ⟨10059873296598558655184161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13413164395464744873578881 10059873296598558655184161)
          ·
            refine ⟨7544904972448918991388121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059873296598558655184161 7544904972448918991388121)
            ·
              refine ⟨5658678729336689243541091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544904972448918991388121 5658678729336689243541091)
              ·
                refine ⟨8488018094005033865311637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658678729336689243541091 8488018094005033865311637)
                ·
                  refine ⟨397875848156485962436483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8488018094005033865311637 397875848156485962436483)
                  ·
                    rfl

theorem cell22_3486872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_3486872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486872 prefixEnd_3486872 := by exact prefixLift 3486872
  have htrace : WordTrace (prefixWord ++ tailWord_3486872) baseStart_3486872 baseEnd_3486872 := by
    simpa [prefixWord, tailWord_3486872, baseEnd_3486872] using wordTrace_append hprefix tailTrace_3486872
  have hstable : (prefixWord ++ tailWord_3486872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486872).length < 2 ^ (prefixWord ++ tailWord_3486872).sum := by decide
  have hdescent : baseEnd_3486872 < baseStart_3486872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486885 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3486885 : Nat := 118140960795 + 3486885 * 2 ^ 59
def prefixEnd_3486885 : Nat := 4983230072969 + 3 ^ 40 * 3486885 * 2
def baseEnd_3486885 : Nat := 1193631994635130186734409

theorem tailTrace_3486885 : CollatzResearch.WordTrace tailWord_3486885 prefixEnd_3486885 1193631994635130186734409 := by
  unfold tailWord_3486885
  simp only [CollatzResearch.WordTrace]
  refine ⟨127177143972618632391934109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84784762648412421594622739 127177143972618632391934109)
  ·
    refine ⟨47691428989731987146975291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127177143972618632391934109 47691428989731987146975291)
    ·
      refine ⟨71537143484597980720462937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47691428989731987146975291 71537143484597980720462937)
      ·
        refine ⟨53652857613448485540347203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71537143484597980720462937 53652857613448485540347203)
        ·
          refine ⟨80479286420172728310520805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53652857613448485540347203 80479286420172728310520805)
          ·
            refine ⟨15089866203782386558222651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80479286420172728310520805 15089866203782386558222651)
            ·
              refine ⟨22634799305673579837333977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15089866203782386558222651 22634799305673579837333977)
              ·
                refine ⟨16976099479255184878000483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22634799305673579837333977 16976099479255184878000483)
                ·
                  refine ⟨25464149218882777317000725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16976099479255184878000483 25464149218882777317000725)
                  ·
                    refine ⟨1193631994635130186734409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25464149218882777317000725 1193631994635130186734409)
                    ·
                      rfl

theorem cell22_3486885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3486885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486885 prefixEnd_3486885 := by exact prefixLift 3486885
  have htrace : WordTrace (prefixWord ++ tailWord_3486885) baseStart_3486885 baseEnd_3486885 := by
    simpa [prefixWord, tailWord_3486885, baseEnd_3486885] using wordTrace_append hprefix tailTrace_3486885
  have hstable : (prefixWord ++ tailWord_3486885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486885).length < 2 ^ (prefixWord ++ tailWord_3486885).sum := by decide
  have hdescent : baseEnd_3486885 < baseStart_3486885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486960 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_3486960 : Nat := 118140960795 + 3486960 * 2 ^ 59
def prefixEnd_3486960 : Nat := 4983230072969 + 3 ^ 40 * 3486960 * 2
def baseEnd_3486960 : Nat := 1193657668667854991109179

theorem tailTrace_3486960 : CollatzResearch.WordTrace tailWord_3486960 prefixEnd_3486960 1193657668667854991109179 := by
  unfold tailWord_3486960
  simp only [CollatzResearch.WordTrace]
  refine ⟨63589939723673460100457167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84786586298231280133942889 63589939723673460100457167)
  ·
    refine ⟨95384909585510190150685751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63589939723673460100457167 95384909585510190150685751)
    ·
      refine ⟨143077364378265285226028627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95384909585510190150685751 143077364378265285226028627)
      ·
        refine ⟨214616046567397927839042941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143077364378265285226028627 214616046567397927839042941)
        ·
          refine ⟨80481017462774222939641103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214616046567397927839042941 80481017462774222939641103)
          ·
            refine ⟨120721526194161334409461655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80481017462774222939641103 120721526194161334409461655)
            ·
              refine ⟨181082289291242001614192483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120721526194161334409461655 181082289291242001614192483)
              ·
                refine ⟨271623433936863002421288725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181082289291242001614192483 271623433936863002421288725)
                ·
                  refine ⟨12732348465790453238497909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271623433936863002421288725 12732348465790453238497909)
                  ·
                    refine ⟨1193657668667854991109179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12732348465790453238497909 1193657668667854991109179)
                    ·
                      rfl

theorem cell22_3486960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_3486960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486960 prefixEnd_3486960 := by exact prefixLift 3486960
  have htrace : WordTrace (prefixWord ++ tailWord_3486960) baseStart_3486960 baseEnd_3486960 := by
    simpa [prefixWord, tailWord_3486960, baseEnd_3486960] using wordTrace_append hprefix tailTrace_3486960
  have hstable : (prefixWord ++ tailWord_3486960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486960).length < 2 ^ (prefixWord ++ tailWord_3486960).sum := by decide
  have hdescent : baseEnd_3486960 < baseStart_3486960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3486966 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3486966 : Nat := 118140960795 + 3486966 * 2 ^ 59
def prefixEnd_3486966 : Nat := 4983230072969 + 3 ^ 40 * 3486966 * 2
def baseEnd_3486966 : Nat := 1193659722590472975459161

theorem tailTrace_3486966 : CollatzResearch.WordTrace tailWord_3486966 prefixEnd_3486966 1193659722590472975459161 := by
  unfold tailWord_3486966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948756142832823951602047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84786732190216788817088501 7948756142832823951602047)
  ·
    refine ⟨11923134214249235927403071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948756142832823951602047 11923134214249235927403071)
    ·
      refine ⟨17884701321373853891104607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923134214249235927403071 17884701321373853891104607)
      ·
        refine ⟨26827051982060780836656911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17884701321373853891104607 26827051982060780836656911)
        ·
          refine ⟨40240577973091171254985367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26827051982060780836656911 40240577973091171254985367)
          ·
            refine ⟨60360866959636756882478051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40240577973091171254985367 60360866959636756882478051)
            ·
              refine ⟨90541300439455135323717077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60360866959636756882478051 90541300439455135323717077)
              ·
                refine ⟨2122061729049729734149619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90541300439455135323717077 2122061729049729734149619)
                ·
                  refine ⟨3183092593574594601224429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122061729049729734149619 3183092593574594601224429)
                  ·
                    refine ⟨1193659722590472975459161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183092593574594601224429 1193659722590472975459161)
                    ·
                      rfl

theorem cell22_3486966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3486966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3486966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3486966 prefixEnd_3486966 := by exact prefixLift 3486966
  have htrace : WordTrace (prefixWord ++ tailWord_3486966) baseStart_3486966 baseEnd_3486966 := by
    simpa [prefixWord, tailWord_3486966, baseEnd_3486966] using wordTrace_append hprefix tailTrace_3486966
  have hstable : (prefixWord ++ tailWord_3486966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3486966).length < 2 ^ (prefixWord ++ tailWord_3486966).sum := by decide
  have hdescent : baseEnd_3486966 < baseStart_3486966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3486966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487024 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_3487024 : Nat := 118140960795 + 3487024 * 2 ^ 59
def prefixEnd_3487024 : Nat := 4983230072969 + 3 ^ 40 * 3487024 * 2
def baseEnd_3487024 : Nat := 397893192391926719169661

theorem tailTrace_3487024 : CollatzResearch.WordTrace tailWord_3487024 prefixEnd_3487024 397893192391926719169661 := by
  unfold tailWord_3487024
  simp only [CollatzResearch.WordTrace]
  refine ⟨63591106859557529565622063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84788142479410039420829417 63591106859557529565622063)
  ·
    refine ⟨95386660289336294348433095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63591106859557529565622063 95386660289336294348433095)
    ·
      refine ⟨143079990434004441522649643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95386660289336294348433095 143079990434004441522649643)
      ·
        refine ⟨214619985651006662283974465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143079990434004441522649643 214619985651006662283974465)
        ·
          refine ⟨160964989238254996712980849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214619985651006662283974465 160964989238254996712980849)
          ·
            refine ⟨120723741928691247534735637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160964989238254996712980849 120723741928691247534735637)
            ·
              refine ⟨5658925402907402228190733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120723741928691247534735637 5658925402907402228190733)
              ·
                refine ⟨2122097026090275835571525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5658925402907402228190733 2122097026090275835571525)
                ·
                  refine ⟨397893192391926719169661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122097026090275835571525 397893192391926719169661)
                  ·
                    rfl

theorem cell22_3487024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_3487024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487024 prefixEnd_3487024 := by exact prefixLift 3487024
  have htrace : WordTrace (prefixWord ++ tailWord_3487024) baseStart_3487024 baseEnd_3487024 := by
    simpa [prefixWord, tailWord_3487024, baseEnd_3487024] using wordTrace_append hprefix tailTrace_3487024
  have hstable : (prefixWord ++ tailWord_3487024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487024).length < 2 ^ (prefixWord ++ tailWord_3487024).sum := by decide
  have hdescent : baseEnd_3487024 < baseStart_3487024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487026 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_3487026 : Nat := 118140960795 + 3487026 * 2 ^ 59
def prefixEnd_3487026 : Nat := 4983230072969 + 3 ^ 40 * 3487026 * 2
def baseEnd_3487026 : Nat := 1193680261816652818958977

theorem tailTrace_3487026 : CollatzResearch.WordTrace tailWord_3487026 prefixEnd_3487026 1193680261816652818958977 := by
  unfold tailWord_3487026
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795571666276953368204233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84788191110071875648544621 31795571666276953368204233)
  ·
    refine ⟨23846678749707715026153175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31795571666276953368204233 23846678749707715026153175)
    ·
      refine ⟨35770018124561572539229763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23846678749707715026153175 35770018124561572539229763)
      ·
        refine ⟨53655027186842358808844645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35770018124561572539229763 53655027186842358808844645)
        ·
          refine ⟨10060317597532942276658371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53655027186842358808844645 10060317597532942276658371)
          ·
            refine ⟨15090476396299413414987557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060317597532942276658371 15090476396299413414987557)
            ·
              refine ⟨2829464324306140015310167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15090476396299413414987557 2829464324306140015310167)
              ·
                refine ⟨4244196486459210022965251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829464324306140015310167 4244196486459210022965251)
                ·
                  refine ⟨6366294729688815034447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244196486459210022965251 6366294729688815034447877)
                  ·
                    refine ⟨1193680261816652818958977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366294729688815034447877 1193680261816652818958977)
                    ·
                      rfl

theorem cell22_3487026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_3487026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487026 prefixEnd_3487026 := by exact prefixLift 3487026
  have htrace : WordTrace (prefixWord ++ tailWord_3487026) baseStart_3487026 baseEnd_3487026 := by
    simpa [prefixWord, tailWord_3487026, baseEnd_3487026] using wordTrace_append hprefix tailTrace_3487026
  have hstable : (prefixWord ++ tailWord_3487026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487026).length < 2 ^ (prefixWord ++ tailWord_3487026).sum := by decide
  have hdescent : baseEnd_3487026 < baseStart_3487026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487030 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3487030 : Nat := 118140960795 + 3487030 * 2 ^ 59
def prefixEnd_3487030 : Nat := 4983230072969 + 3 ^ 40 * 3487030 * 2
def baseEnd_3487030 : Nat := 397893877032799380619655

theorem tailTrace_3487030 : CollatzResearch.WordTrace tailWord_3487030 prefixEnd_3487030 397893877032799380619655 := by
  unfold tailWord_3487030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948902034818332634747659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84788288371395548103975029 7948902034818332634747659)
  ·
    refine ⟨11923353052227498952121489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948902034818332634747659 11923353052227498952121489)
    ·
      refine ⟨8942514789170624214091117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11923353052227498952121489 8942514789170624214091117)
      ·
        refine ⟨3353443045938984080284169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8942514789170624214091117 3353443045938984080284169)
        ·
          refine ⟨2515082284454238060213127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3353443045938984080284169 2515082284454238060213127)
          ·
            refine ⟨3772623426681357090319691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515082284454238060213127 3772623426681357090319691)
            ·
              refine ⟨5658935140022035635479537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772623426681357090319691 5658935140022035635479537)
              ·
                refine ⟨4244201355016526726609653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658935140022035635479537 4244201355016526726609653)
                ·
                  refine ⟨397893877032799380619655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244201355016526726609653 397893877032799380619655)
                  ·
                    rfl

theorem cell22_3487030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3487030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487030 prefixEnd_3487030 := by exact prefixLift 3487030
  have htrace : WordTrace (prefixWord ++ tailWord_3487030) baseStart_3487030 baseEnd_3487030 := by
    simpa [prefixWord, tailWord_3487030, baseEnd_3487030] using wordTrace_append hprefix tailTrace_3487030
  have hstable : (prefixWord ++ tailWord_3487030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487030).length < 2 ^ (prefixWord ++ tailWord_3487030).sum := by decide
  have hdescent : baseEnd_3487030 < baseStart_3487030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487039 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 4, 3]
def baseStart_3487039 : Nat := 118140960795 + 3487039 * 2 ^ 59
def prefixEnd_3487039 : Nat := 4983230072969 + 3 ^ 40 * 3487039 * 2
def baseEnd_3487039 : Nat := 1193684711982325118383937

theorem tailTrace_3487039 : CollatzResearch.WordTrace tailWord_3487039 prefixEnd_3487039 1193684711982325118383937 := by
  unfold tailWord_3487039
  simp only [CollatzResearch.WordTrace]
  refine ⟨127182760814060716693040171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84788507209373811128693447 127182760814060716693040171)
  ·
    refine ⟨190774141221091075039560257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127182760814060716693040171 190774141221091075039560257)
    ·
      refine ⟨143080605915818306279670193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190774141221091075039560257 143080605915818306279670193)
      ·
        refine ⟨107310454436863729709752645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143080605915818306279670193 107310454436863729709752645)
        ·
          refine ⟨20120710206911949320578621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107310454436863729709752645 20120710206911949320578621)
          ·
            refine ⟨7545266327591980995216983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20120710206911949320578621 7545266327591980995216983)
            ·
              refine ⟨11317899491387971492825475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545266327591980995216983 11317899491387971492825475)
              ·
                refine ⟨16976849237081957239238213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11317899491387971492825475 16976849237081957239238213)
                ·
                  refine ⟨3183159231952866982357165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16976849237081957239238213 3183159231952866982357165)
                  ·
                    refine ⟨1193684711982325118383937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183159231952866982357165 1193684711982325118383937)
                    ·
                      rfl

theorem cell22_3487039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_3487039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487039 prefixEnd_3487039 := by exact prefixLift 3487039
  have htrace : WordTrace (prefixWord ++ tailWord_3487039) baseStart_3487039 baseEnd_3487039 := by
    simpa [prefixWord, tailWord_3487039, baseEnd_3487039] using wordTrace_append hprefix tailTrace_3487039
  have hstable : (prefixWord ++ tailWord_3487039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487039).length < 2 ^ (prefixWord ++ tailWord_3487039).sum := by decide
  have hdescent : baseEnd_3487039 < baseStart_3487039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487041 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 4]
def baseStart_3487041 : Nat := 118140960795 + 3487041 * 2 ^ 59
def prefixEnd_3487041 : Nat := 4983230072969 + 3 ^ 40 * 3487041 * 2
def baseEnd_3487041 : Nat := 397895132207732593277977

theorem tailTrace_3487041 : CollatzResearch.WordTrace tailWord_3487041 prefixEnd_3487041 397895132207732593277977 := by
  unfold tailWord_3487041
  simp only [CollatzResearch.WordTrace]
  refine ⟨127182833760053471034612977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84788555840035647356408651 127182833760053471034612977)
  ·
    refine ⟨95387125320040103275959733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127182833760053471034612977 95387125320040103275959733)
    ·
      refine ⟨8942542998753759682121225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95387125320040103275959733 8942542998753759682121225)
      ·
        refine ⟨6706907249065319761590919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8942542998753759682121225 6706907249065319761590919)
        ·
          refine ⟨10060360873597979642386379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706907249065319761590919 10060360873597979642386379)
          ·
            refine ⟨15090541310396969463579569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060360873597979642386379 15090541310396969463579569)
            ·
              refine ⟨11317905982797727097684677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15090541310396969463579569 11317905982797727097684677)
              ·
                refine ⟨2122107371774573830815877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11317905982797727097684677 2122107371774573830815877)
                ·
                  refine ⟨397895132207732593277977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122107371774573830815877 397895132207732593277977)
                  ·
                    rfl

theorem cell22_3487041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_3487041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487041 prefixEnd_3487041 := by exact prefixLift 3487041
  have htrace : WordTrace (prefixWord ++ tailWord_3487041) baseStart_3487041 baseEnd_3487041 := by
    simpa [prefixWord, tailWord_3487041, baseEnd_3487041] using wordTrace_append hprefix tailTrace_3487041
  have hstable : (prefixWord ++ tailWord_3487041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487041).length < 2 ^ (prefixWord ++ tailWord_3487041).sum := by decide
  have hdescent : baseEnd_3487041 < baseStart_3487041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487056 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_3487056 : Nat := 118140960795 + 3487056 * 2 ^ 59
def prefixEnd_3487056 : Nat := 4983230072969 + 3 ^ 40 * 3487056 * 2
def baseEnd_3487056 : Nat := 1193690531429742740708885

theorem tailTrace_3487056 : CollatzResearch.WordTrace tailWord_3487056 prefixEnd_3487056 1193690531429742740708885 := by
  unfold tailWord_3487056
  simp only [CollatzResearch.WordTrace]
  refine ⟨63591690427499564298204511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84788920569999419064272681 63591690427499564298204511)
  ·
    refine ⟨95387535641249346447306767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63591690427499564298204511 95387535641249346447306767)
    ·
      refine ⟨143081303461874019670960151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95387535641249346447306767 143081303461874019670960151)
      ·
        refine ⟨214621955192811029506440227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143081303461874019670960151 214621955192811029506440227)
        ·
          refine ⟨321932932789216544259660341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214621955192811029506440227 321932932789216544259660341)
          ·
            refine ⟨30181212448989051024343157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321932932789216544259660341 30181212448989051024343157)
            ·
              refine ⟨2829488667092723533532171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30181212448989051024343157 2829488667092723533532171)
              ·
                refine ⟨4244233000639085300298257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829488667092723533532171 4244233000639085300298257)
                ·
                  refine ⟨3183174750479313975223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244233000639085300298257 3183174750479313975223693)
                  ·
                    refine ⟨1193690531429742740708885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183174750479313975223693 1193690531429742740708885)
                    ·
                      rfl

theorem cell22_3487056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_3487056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487056 prefixEnd_3487056 := by exact prefixLift 3487056
  have htrace : WordTrace (prefixWord ++ tailWord_3487056) baseStart_3487056 baseEnd_3487056 := by
    simpa [prefixWord, tailWord_3487056, baseEnd_3487056] using wordTrace_append hprefix tailTrace_3487056
  have hstable : (prefixWord ++ tailWord_3487056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487056).length < 2 ^ (prefixWord ++ tailWord_3487056).sum := by decide
  have hdescent : baseEnd_3487056 < baseStart_3487056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487086 : List Nat := [4, 1, 2, 4, 1, 2, 8]
def baseStart_3487086 : Nat := 118140960795 + 3487086 * 2 ^ 59
def prefixEnd_3487086 : Nat := 4983230072969 + 3 ^ 40 * 3487086 * 2
def baseEnd_3487086 : Nat := 44211140779364172683659

theorem tailTrace_3487086 : CollatzResearch.WordTrace tailWord_3487086 prefixEnd_3487086 44211140779364172683659 := by
  unfold tailWord_3487086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898059380611305465000139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84789650029926962480000741 15898059380611305465000139)
  ·
    refine ⟨23847089070916958197500209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15898059380611305465000139 23847089070916958197500209)
    ·
      refine ⟨17885316803187718648125157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23847089070916958197500209 17885316803187718648125157)
      ·
        refine ⟨3353496900597697246523467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17885316803187718648125157 3353496900597697246523467)
        ·
          refine ⟨5030245350896545869785201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353496900597697246523467 5030245350896545869785201)
          ·
            refine ⟨3772684013172409402338901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5030245350896545869785201 3772684013172409402338901)
            ·
              refine ⟨44211140779364172683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3772684013172409402338901 44211140779364172683659)
              ·
                rfl

theorem cell22_3487086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 8].length) (baseStart_3487086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487086 prefixEnd_3487086 := by exact prefixLift 3487086
  have htrace : WordTrace (prefixWord ++ tailWord_3487086) baseStart_3487086 baseEnd_3487086 := by
    simpa [prefixWord, tailWord_3487086, baseEnd_3487086] using wordTrace_append hprefix tailTrace_3487086
  have hstable : (prefixWord ++ tailWord_3487086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487086).length < 2 ^ (prefixWord ++ tailWord_3487086).sum := by decide
  have hdescent : baseEnd_3487086 < baseStart_3487086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487097 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 7]
def baseStart_3487097 : Nat := 118140960795 + 3487097 * 2 ^ 59
def prefixEnd_3487097 : Nat := 4983230072969 + 3 ^ 40 * 3487097 * 2
def baseEnd_3487097 : Nat := 397901522189210766811253

theorem tailTrace_3487097 : CollatzResearch.WordTrace tailWord_3487097 prefixEnd_3487097 397901522189210766811253 := by
  unfold tailWord_3487097
  simp only [CollatzResearch.WordTrace]
  refine ⟨127184876247850592598651545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84789917498567061732434363 127184876247850592598651545)
  ·
    refine ⟨95388657185887944448988659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127184876247850592598651545 95388657185887944448988659)
    ·
      refine ⟨143082985778831916673482989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95388657185887944448988659 143082985778831916673482989)
      ·
        refine ⟨53656119667061968752556121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143082985778831916673482989 53656119667061968752556121)
        ·
          refine ⟨40242089750296476564417091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53656119667061968752556121 40242089750296476564417091)
          ·
            refine ⟨60363134625444714846625637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40242089750296476564417091 60363134625444714846625637)
            ·
              refine ⟨11318087742270884033742307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60363134625444714846625637 11318087742270884033742307)
              ·
                refine ⟨16977131613406326050613461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318087742270884033742307 16977131613406326050613461)
                ·
                  refine ⟨397901522189210766811253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16977131613406326050613461 397901522189210766811253)
                  ·
                    rfl

theorem cell22_3487097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_3487097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487097 prefixEnd_3487097 := by exact prefixLift 3487097
  have htrace : WordTrace (prefixWord ++ tailWord_3487097) baseStart_3487097 baseEnd_3487097 := by
    simpa [prefixWord, tailWord_3487097, baseEnd_3487097] using wordTrace_append hprefix tailTrace_3487097
  have hstable : (prefixWord ++ tailWord_3487097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487097).length < 2 ^ (prefixWord ++ tailWord_3487097).sum := by decide
  have hdescent : baseEnd_3487097 < baseStart_3487097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487189 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3487189 : Nat := 118140960795 + 3487189 * 2 ^ 59
def prefixEnd_3487189 : Nat := 4983230072969 + 3 ^ 40 * 3487189 * 2
def baseEnd_3487189 : Nat := 1193736060047774727133477

theorem tailTrace_3487189 : CollatzResearch.WordTrace tailWord_3487189 prefixEnd_3487189 1193736060047774727133477 := by
  unfold tailWord_3487189
  simp only [CollatzResearch.WordTrace]
  refine ⟨127188231763517292311000621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84792154509011528207333747 127188231763517292311000621)
  ·
    refine ⟨47695586911318984616625233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127188231763517292311000621 47695586911318984616625233)
    ·
      refine ⟨35771690183489238462468925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47695586911318984616625233 35771690183489238462468925)
      ·
        refine ⟨13414383818808464423425847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35771690183489238462468925 13414383818808464423425847)
        ·
          refine ⟨20121575728212696635138771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414383818808464423425847 20121575728212696635138771)
          ·
            refine ⟨30182363592319044952708157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20121575728212696635138771 30182363592319044952708157)
            ·
              refine ⟨11318386347119641857265559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30182363592319044952708157 11318386347119641857265559)
              ·
                refine ⟨16977579520679462785898339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318386347119641857265559 16977579520679462785898339)
                ·
                  refine ⟨25466369281019194178847509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16977579520679462785898339 25466369281019194178847509)
                  ·
                    refine ⟨1193736060047774727133477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25466369281019194178847509 1193736060047774727133477)
                    ·
                      rfl

theorem cell22_3487189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3487189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487189 prefixEnd_3487189 := by exact prefixLift 3487189
  have htrace : WordTrace (prefixWord ++ tailWord_3487189) baseStart_3487189 baseEnd_3487189 := by
    simpa [prefixWord, tailWord_3487189, baseEnd_3487189] using wordTrace_append hprefix tailTrace_3487189
  have hstable : (prefixWord ++ tailWord_3487189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487189).length < 2 ^ (prefixWord ++ tailWord_3487189).sum := by decide
  have hdescent : baseEnd_3487189 < baseStart_3487189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487283 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 5]
def baseStart_3487283 : Nat := 118140960795 + 3487283 * 2 ^ 59
def prefixEnd_3487283 : Nat := 4983230072969 + 3 ^ 40 * 3487283 * 2
def baseEnd_3487283 : Nat := 397922746056263271761063

theorem tailTrace_3487283 : CollatzResearch.WordTrace tailWord_3487283 prefixEnd_3487283 397922746056263271761063 := by
  unfold tailWord_3487283
  simp only [CollatzResearch.WordTrace]
  refine ⟨127191660225176746364922503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84794440150117830909948335 127191660225176746364922503)
  ·
    refine ⟨190787490337765119547383755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127191660225176746364922503 190787490337765119547383755)
    ·
      refine ⟨286181235506647679321075633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190787490337765119547383755 286181235506647679321075633)
      ·
        refine ⟨214635926629985759490806725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286181235506647679321075633 214635926629985759490806725)
        ·
          refine ⟨40244236243122329904526261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214635926629985759490806725 40244236243122329904526261)
          ·
            refine ⟨3772897147792718428549337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40244236243122329904526261 3772897147792718428549337)
            ·
              refine ⟨2829672860844538821412003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3772897147792718428549337 2829672860844538821412003)
              ·
                refine ⟨4244509291266808232118005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829672860844538821412003 4244509291266808232118005)
                ·
                  refine ⟨397922746056263271761063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244509291266808232118005 397922746056263271761063)
                  ·
                    rfl

theorem cell22_3487283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 5].length) (baseStart_3487283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487283 prefixEnd_3487283 := by exact prefixLift 3487283
  have htrace : WordTrace (prefixWord ++ tailWord_3487283) baseStart_3487283 baseEnd_3487283 := by
    simpa [prefixWord, tailWord_3487283, baseEnd_3487283] using wordTrace_append hprefix tailTrace_3487283
  have hstable : (prefixWord ++ tailWord_3487283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487283).length < 2 ^ (prefixWord ++ tailWord_3487283).sum := by decide
  have hdescent : baseEnd_3487283 < baseStart_3487283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487311 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 4]
def baseStart_3487311 : Nat := 118140960795 + 3487311 * 2 ^ 59
def prefixEnd_3487311 : Nat := 4983230072969 + 3 ^ 40 * 3487311 * 2
def baseEnd_3487311 : Nat := 397925941047002358527701

theorem tailTrace_3487311 : CollatzResearch.WordTrace tailWord_3487311 prefixEnd_3487311 397925941047002358527701 := by
  unfold tailWord_3487311
  simp only [CollatzResearch.WordTrace]
  refine ⟨127192681469075307146941787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84795120979383538097961191 127192681469075307146941787)
  ·
    refine ⟨190789022203612960720412681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127192681469075307146941787 190789022203612960720412681)
    ·
      refine ⟨143091766652709720540309511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190789022203612960720412681 143091766652709720540309511)
      ·
        refine ⟨214637649979064580810464267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143091766652709720540309511 214637649979064580810464267)
        ·
          refine ⟨321956474968596871215696401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214637649979064580810464267 321956474968596871215696401)
          ·
            refine ⟨241467356226447653411772301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321956474968596871215696401 241467356226447653411772301)
            ·
              refine ⟨90550258584917870029414613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241467356226447653411772301 90550258584917870029414613)
              ·
                refine ⟨2122271685584012578814405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90550258584917870029414613 2122271685584012578814405)
                ·
                  refine ⟨397925941047002358527701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2122271685584012578814405 397925941047002358527701)
                  ·
                    rfl

theorem cell22_3487311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 4].length) (baseStart_3487311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487311 prefixEnd_3487311 := by exact prefixLift 3487311
  have htrace : WordTrace (prefixWord ++ tailWord_3487311) baseStart_3487311 baseEnd_3487311 := by
    simpa [prefixWord, tailWord_3487311, baseEnd_3487311] using wordTrace_append hprefix tailTrace_3487311
  have hstable : (prefixWord ++ tailWord_3487311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487311).length < 2 ^ (prefixWord ++ tailWord_3487311).sum := by decide
  have hdescent : baseEnd_3487311 < baseStart_3487311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487313 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_3487313 : Nat := 118140960795 + 3487313 * 2 ^ 59
def prefixEnd_3487313 : Nat := 4983230072969 + 3 ^ 40 * 3487313 * 2
def baseEnd_3487313 : Nat := 1193778507781879737033097

theorem tailTrace_3487313 : CollatzResearch.WordTrace tailWord_3487313 prefixEnd_3487313 1193778507781879737033097 := by
  unfold tailWord_3487313
  simp only [CollatzResearch.WordTrace]
  refine ⟨127192754415068061488514593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84795169610045374325676395 127192754415068061488514593)
  ·
    refine ⟨95394565811301046116385945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127192754415068061488514593 95394565811301046116385945)
    ·
      refine ⟨71545924358475784587289459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95394565811301046116385945 71545924358475784587289459)
      ·
        refine ⟨107318886537713676880934189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71545924358475784587289459 107318886537713676880934189)
        ·
          refine ⟨40244582451642628830350321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107318886537713676880934189 40244582451642628830350321)
          ·
            refine ⟨30183436838731971622762741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40244582451642628830350321 30183436838731971622762741)
            ·
              refine ⟨2829697203631122339634007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30183436838731971622762741 2829697203631122339634007)
              ·
                refine ⟨4244545805446683509451011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829697203631122339634007 4244545805446683509451011)
                ·
                  refine ⟨6366818708170025264176517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244545805446683509451011 6366818708170025264176517)
                  ·
                    refine ⟨1193778507781879737033097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366818708170025264176517 1193778507781879737033097)
                    ·
                      rfl

theorem cell22_3487313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_3487313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487313 prefixEnd_3487313 := by exact prefixLift 3487313
  have htrace : WordTrace (prefixWord ++ tailWord_3487313) baseStart_3487313 baseEnd_3487313 := by
    simpa [prefixWord, tailWord_3487313, baseEnd_3487313] using wordTrace_append hprefix tailTrace_3487313
  have hstable : (prefixWord ++ tailWord_3487313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487313).length < 2 ^ (prefixWord ++ tailWord_3487313).sum := by decide
  have hdescent : baseEnd_3487313 < baseStart_3487313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487354 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_3487354 : Nat := 118140960795 + 3487354 * 2 ^ 59
def prefixEnd_3487354 : Nat := 4983230072969 + 3 ^ 40 * 3487354 * 2
def baseEnd_3487354 : Nat := 1193792542919769296757971

theorem tailTrace_3487354 : CollatzResearch.WordTrace tailWord_3487354 prefixEnd_3487354 1193792542919769296757971 := by
  unfold tailWord_3487354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31798562451979881372689279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84796166538613016993838077 31798562451979881372689279)
  ·
    refine ⟨47697843677969822059033919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31798562451979881372689279 47697843677969822059033919)
    ·
      refine ⟨71546765516954733088550879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47697843677969822059033919 71546765516954733088550879)
      ·
        refine ⟨107320148275432099632826319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71546765516954733088550879 107320148275432099632826319)
        ·
          refine ⟨160980222413148149449239479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107320148275432099632826319 160980222413148149449239479)
          ·
            refine ⟨241470333619722224173859219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160980222413148149449239479 241470333619722224173859219)
            ·
              refine ⟨362205500429583336260788829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241470333619722224173859219 362205500429583336260788829)
              ·
                refine ⟨135827062661093751097795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362205500429583336260788829 135827062661093751097795811)
                ·
                  refine ⟨203740593991640626646693717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135827062661093751097795811 203740593991640626646693717)
                  ·
                    refine ⟨1193792542919769296757971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 203740593991640626646693717 1193792542919769296757971)
                    ·
                      rfl

theorem cell22_3487354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_3487354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487354 prefixEnd_3487354 := by exact prefixLift 3487354
  have htrace : WordTrace (prefixWord ++ tailWord_3487354) baseStart_3487354 baseEnd_3487354 := by
    simpa [prefixWord, tailWord_3487354, baseEnd_3487354] using wordTrace_append hprefix tailTrace_3487354
  have hstable : (prefixWord ++ tailWord_3487354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487354).length < 2 ^ (prefixWord ++ tailWord_3487354).sum := by decide
  have hdescent : baseEnd_3487354 < baseStart_3487354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487371 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 5, 3]
def baseStart_3487371 : Nat := 118140960795 + 3487371 * 2 ^ 59
def prefixEnd_3487371 : Nat := 4983230072969 + 3 ^ 40 * 3487371 * 2
def baseEnd_3487371 : Nat := 1193798362367186919082919

theorem tailTrace_3487371 : CollatzResearch.WordTrace tailWord_3487371 prefixEnd_3487371 1193798362367186919082919 := by
  unfold tailWord_3487371
  simp only [CollatzResearch.WordTrace]
  refine ⟨127194869848857937394125967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84796579899238624929417311 127194869848857937394125967)
  ·
    refine ⟨190792304773286906091188951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127194869848857937394125967 190792304773286906091188951)
    ·
      refine ⟨286188457159930359136783427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190792304773286906091188951 286188457159930359136783427)
      ·
        refine ⟨429282685739895538705175141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286188457159930359136783427 429282685739895538705175141)
        ·
          refine ⟨80490503576230413507220339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429282685739895538705175141 80490503576230413507220339)
          ·
            refine ⟨120735755364345620260830509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80490503576230413507220339 120735755364345620260830509)
            ·
              refine ⟨45275908261629607597811441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120735755364345620260830509 45275908261629607597811441)
              ·
                refine ⟨33956931196222205698358581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45275908261629607597811441 33956931196222205698358581)
                ·
                  refine ⟨3183462299645831784221117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33956931196222205698358581 3183462299645831784221117)
                  ·
                    refine ⟨1193798362367186919082919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183462299645831784221117 1193798362367186919082919)
                    ·
                      rfl

theorem cell22_3487371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].length) (baseStart_3487371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487371 prefixEnd_3487371 := by exact prefixLift 3487371
  have htrace : WordTrace (prefixWord ++ tailWord_3487371) baseStart_3487371 baseEnd_3487371 := by
    simpa [prefixWord, tailWord_3487371, baseEnd_3487371] using wordTrace_append hprefix tailTrace_3487371
  have hstable : (prefixWord ++ tailWord_3487371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487371).length < 2 ^ (prefixWord ++ tailWord_3487371).sum := by decide
  have hdescent : baseEnd_3487371 < baseStart_3487371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487394 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3487394 : Nat := 118140960795 + 3487394 * 2 ^ 59
def prefixEnd_3487394 : Nat := 4983230072969 + 3 ^ 40 * 3487394 * 2
def baseEnd_3487394 : Nat := 1193806235737222525757849

theorem tailTrace_3487394 : CollatzResearch.WordTrace tailWord_3487394 prefixEnd_3487394 1193806235737222525757849 := by
  unfold tailWord_3487394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31798927181943653080553309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84797139151849741548142157 31798927181943653080553309)
  ·
    refine ⟨11924597693228869905207491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31798927181943653080553309 11924597693228869905207491)
    ·
      refine ⟨17886896539843304857811237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924597693228869905207491 17886896539843304857811237)
      ·
        refine ⟨3353793101220619660839607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17886896539843304857811237 3353793101220619660839607)
        ·
          refine ⟨5030689651830929491259411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353793101220619660839607 5030689651830929491259411)
          ·
            refine ⟨7546034477746394236889117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030689651830929491259411 7546034477746394236889117)
            ·
              refine ⟨2829762929154897838833419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7546034477746394236889117 2829762929154897838833419)
              ·
                refine ⟨4244644393732346758250129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829762929154897838833419 4244644393732346758250129)
                ·
                  refine ⟨3183483295299260068687597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4244644393732346758250129 3183483295299260068687597)
                  ·
                    refine ⟨1193806235737222525757849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183483295299260068687597 1193806235737222525757849)
                    ·
                      rfl

theorem cell22_3487394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3487394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487394 prefixEnd_3487394 := by exact prefixLift 3487394
  have htrace : WordTrace (prefixWord ++ tailWord_3487394) baseStart_3487394 baseEnd_3487394 := by
    simpa [prefixWord, tailWord_3487394, baseEnd_3487394] using wordTrace_append hprefix tailTrace_3487394
  have hstable : (prefixWord ++ tailWord_3487394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487394).length < 2 ^ (prefixWord ++ tailWord_3487394).sum := by decide
  have hdescent : baseEnd_3487394 < baseStart_3487394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487422 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_3487422 : Nat := 118140960795 + 3487422 * 2 ^ 59
def prefixEnd_3487422 : Nat := 4983230072969 + 3 ^ 40 * 3487422 * 2
def baseEnd_3487422 : Nat := 1193815820709439786057763

theorem tailTrace_3487422 : CollatzResearch.WordTrace tailWord_3487422 prefixEnd_3487422 1193815820709439786057763 := by
  unfold tailWord_3487422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15899591246459146638029065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84797819981115448736155013 15899591246459146638029065)
  ·
    refine ⟨11924693434844359978521799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15899591246459146638029065 11924693434844359978521799)
    ·
      refine ⟨17887040152266539967782699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924693434844359978521799 17887040152266539967782699)
      ·
        refine ⟨26830560228399809951674049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887040152266539967782699 26830560228399809951674049)
        ·
          refine ⟨20122920171299857463755537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26830560228399809951674049 20122920171299857463755537)
          ·
            refine ⟨15092190128474893097816653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20122920171299857463755537 15092190128474893097816653)
            ·
              refine ⟨5659571298178084911681245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15092190128474893097816653 5659571298178084911681245)
              ·
                refine ⟨2122339236816781841880467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5659571298178084911681245 2122339236816781841880467)
                ·
                  refine ⟨3183508855225172762820701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122339236816781841880467 3183508855225172762820701)
                  ·
                    refine ⟨1193815820709439786057763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183508855225172762820701 1193815820709439786057763)
                    ·
                      rfl

theorem cell22_3487422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_3487422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487422 prefixEnd_3487422 := by exact prefixLift 3487422
  have htrace : WordTrace (prefixWord ++ tailWord_3487422) baseStart_3487422 baseEnd_3487422 := by
    simpa [prefixWord, tailWord_3487422, baseEnd_3487422] using wordTrace_append hprefix tailTrace_3487422
  have hstable : (prefixWord ++ tailWord_3487422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487422).length < 2 ^ (prefixWord ++ tailWord_3487422).sum := by decide
  have hdescent : baseEnd_3487422 < baseStart_3487422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487478 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3487478 : Nat := 118140960795 + 3487478 * 2 ^ 59
def prefixEnd_3487478 : Nat := 4983230072969 + 3 ^ 40 * 3487478 * 2
def baseEnd_3487478 : Nat := 1193834990653874306657591

theorem tailTrace_3487478 : CollatzResearch.WordTrace tailWord_3487478 prefixEnd_3487478 1193834990653874306657591 := by
  unfold tailWord_3487478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949923278716893416766943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84799181639646863112180725 7949923278716893416766943)
  ·
    refine ⟨11924884918075340125150415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949923278716893416766943 11924884918075340125150415)
    ·
      refine ⟨17887327377113010187725623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924884918075340125150415 17887327377113010187725623)
      ·
        refine ⟨26830991065669515281588435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887327377113010187725623 26830991065669515281588435)
        ·
          refine ⟨40246486598504272922382653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26830991065669515281588435 40246486598504272922382653)
          ·
            refine ⟨15092432474439102345893495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40246486598504272922382653 15092432474439102345893495)
            ·
              refine ⟨22638648711658653518840243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092432474439102345893495 22638648711658653518840243)
              ·
                refine ⟨33957973067487980278260365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22638648711658653518840243 33957973067487980278260365)
                ·
                  refine ⟨12734239900307992604347637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33957973067487980278260365 12734239900307992604347637)
                  ·
                    refine ⟨1193834990653874306657591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12734239900307992604347637 1193834990653874306657591)
                    ·
                      rfl

theorem cell22_3487478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3487478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487478 prefixEnd_3487478 := by exact prefixLift 3487478
  have htrace : WordTrace (prefixWord ++ tailWord_3487478) baseStart_3487478 baseEnd_3487478 := by
    simpa [prefixWord, tailWord_3487478, baseEnd_3487478] using wordTrace_append hprefix tailTrace_3487478
  have hstable : (prefixWord ++ tailWord_3487478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487478).length < 2 ^ (prefixWord ++ tailWord_3487478).sum := by decide
  have hdescent : baseEnd_3487478 < baseStart_3487478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487523 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 5, 3]
def baseStart_3487523 : Nat := 118140960795 + 3487523 * 2 ^ 59
def prefixEnd_3487523 : Nat := 4983230072969 + 3 ^ 40 * 3487523 * 2
def baseEnd_3487523 : Nat := 1193850395073509189282453

theorem tailTrace_3487523 : CollatzResearch.WordTrace tailWord_3487523 prefixEnd_3487523 1193850395073509189282453 := by
  unfold tailWord_3487523
  simp only [CollatzResearch.WordTrace]
  refine ⟨127200413744307267353659223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84800275829538178235772815 127200413744307267353659223)
  ·
    refine ⟨190800620616460901030488835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127200413744307267353659223 190800620616460901030488835)
    ·
      refine ⟨286200930924691351545733253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190800620616460901030488835 286200930924691351545733253)
      ·
        refine ⟨53662674548379628414824985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286200930924691351545733253 53662674548379628414824985)
        ·
          refine ⟨40247005911284721311118739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53662674548379628414824985 40247005911284721311118739)
          ·
            refine ⟨60370508866927081966678109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40247005911284721311118739 60370508866927081966678109)
            ·
              refine ⟨22638940825097655737504291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60370508866927081966678109 22638940825097655737504291)
              ·
                refine ⟨33958411237646483606256437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22638940825097655737504291 33958411237646483606256437)
                ·
                  refine ⟨3183601053529357838086541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33958411237646483606256437 3183601053529357838086541)
                  ·
                    refine ⟨1193850395073509189282453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183601053529357838086541 1193850395073509189282453)
                    ·
                      rfl

theorem cell22_3487523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 3].length) (baseStart_3487523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487523 prefixEnd_3487523 := by exact prefixLift 3487523
  have htrace : WordTrace (prefixWord ++ tailWord_3487523) baseStart_3487523 baseEnd_3487523 := by
    simpa [prefixWord, tailWord_3487523, baseEnd_3487523] using wordTrace_append hprefix tailTrace_3487523
  have hstable : (prefixWord ++ tailWord_3487523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487523).length < 2 ^ (prefixWord ++ tailWord_3487523).sum := by decide
  have hdescent : baseEnd_3487523 < baseStart_3487523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3487628 : Nat := 118140960795 + 3487628 * 2 ^ 59
def prefixEnd_3487628 : Nat := 4983230072969 + 3 ^ 40 * 3487628 * 2
def baseEnd_3487628 : Nat := 1193886338719323915407131

theorem tailTrace_3487628 : CollatzResearch.WordTrace tailWord_3487628 prefixEnd_3487628 1193886338719323915407131 := by
  unfold tailWord_3487628
  simp only [CollatzResearch.WordTrace]
  refine ⟨63602121704463435143115769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84802828939284580190821025 63602121704463435143115769)
  ·
    refine ⟨47701591278347576357336827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63602121704463435143115769 47701591278347576357336827)
    ·
      refine ⟨71552386917521364536005241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47701591278347576357336827 71552386917521364536005241)
      ·
        refine ⟨53664290188141023402003931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71552386917521364536005241 53664290188141023402003931)
        ·
          refine ⟨80496435282211535103005897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53664290188141023402003931 80496435282211535103005897)
          ·
            refine ⟨60372326461658651327254423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80496435282211535103005897 60372326461658651327254423)
            ·
              refine ⟨90558489692487976990881635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60372326461658651327254423 90558489692487976990881635)
              ·
                refine ⟨135837734538731965486322453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90558489692487976990881635 135837734538731965486322453)
                ·
                  refine ⟨6367393806503060882171365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135837734538731965486322453 6367393806503060882171365)
                  ·
                    refine ⟨1193886338719323915407131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367393806503060882171365 1193886338719323915407131)
                    ·
                      rfl

theorem cell22_3487628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3487628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487628 prefixEnd_3487628 := by exact prefixLift 3487628
  have htrace : WordTrace (prefixWord ++ tailWord_3487628) baseStart_3487628 baseEnd_3487628 := by
    simpa [prefixWord, tailWord_3487628, baseEnd_3487628] using wordTrace_append hprefix tailTrace_3487628
  have hstable : (prefixWord ++ tailWord_3487628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487628).length < 2 ^ (prefixWord ++ tailWord_3487628).sum := by decide
  have hdescent : baseEnd_3487628 < baseStart_3487628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487634 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3487634 : Nat := 118140960795 + 3487634 * 2 ^ 59
def prefixEnd_3487634 : Nat := 4983230072969 + 3 ^ 40 * 3487634 * 2
def baseEnd_3487634 : Nat := 1193888392641941899757113

theorem tailTrace_3487634 : CollatzResearch.WordTrace tailWord_3487634 prefixEnd_3487634 1193888392641941899757113 := by
  unfold tailWord_3487634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801115561726283327737489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84802974831270088873966637 31801115561726283327737489)
  ·
    refine ⟨23850836671294712495803117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31801115561726283327737489 23850836671294712495803117)
    ·
      refine ⟨8944063751735517185926169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23850836671294712495803117 8944063751735517185926169)
      ·
        refine ⟨6708047813801637889444627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8944063751735517185926169 6708047813801637889444627)
        ·
          refine ⟨10062071720702456834166941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708047813801637889444627 10062071720702456834166941)
          ·
            refine ⟨3773276895263421312812603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10062071720702456834166941 3773276895263421312812603)
            ·
              refine ⟨5659915342895131969218905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773276895263421312812603 5659915342895131969218905)
              ·
                refine ⟨4244936507171348976914179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5659915342895131969218905 4244936507171348976914179)
                ·
                  refine ⟨6367404760757023465371269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244936507171348976914179 6367404760757023465371269)
                  ·
                    refine ⟨1193888392641941899757113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367404760757023465371269 1193888392641941899757113)
                    ·
                      rfl

theorem cell22_3487634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3487634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487634 prefixEnd_3487634 := by exact prefixLift 3487634
  have htrace : WordTrace (prefixWord ++ tailWord_3487634) baseStart_3487634 baseEnd_3487634 := by
    simpa [prefixWord, tailWord_3487634, baseEnd_3487634] using wordTrace_append hprefix tailTrace_3487634
  have hstable : (prefixWord ++ tailWord_3487634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487634).length < 2 ^ (prefixWord ++ tailWord_3487634).sum := by decide
  have hdescent : baseEnd_3487634 < baseStart_3487634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487645 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3487645 : Nat := 118140960795 + 3487645 * 2 ^ 59
def prefixEnd_3487645 : Nat := 4983230072969 + 3 ^ 40 * 3487645 * 2
def baseEnd_3487645 : Nat := 1193892158166741537732079

theorem tailTrace_3487645 : CollatzResearch.WordTrace tailWord_3487645 prefixEnd_3487645 1193892158166741537732079 := by
  unfold tailWord_3487645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127204863449865282189600389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84803242299910188126400259 127204863449865282189600389)
  ·
    refine ⟨23850911896849740410550073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127204863449865282189600389 23850911896849740410550073)
    ·
      refine ⟨17888183922637305307912555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23850911896849740410550073 17888183922637305307912555)
      ·
        refine ⟨26832275883955957961868833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17888183922637305307912555 26832275883955957961868833)
        ·
          refine ⟨20124206912966968471401625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26832275883955957961868833 20124206912966968471401625)
          ·
            refine ⟨15093155184725226353551219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20124206912966968471401625 15093155184725226353551219)
            ·
              refine ⟨22639732777087839530326829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15093155184725226353551219 22639732777087839530326829)
              ·
                refine ⟨8489899791407939823872561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22639732777087839530326829 8489899791407939823872561)
                ·
                  refine ⟨6367424843555954867904421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8489899791407939823872561 6367424843555954867904421)
                  ·
                    refine ⟨1193892158166741537732079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367424843555954867904421 1193892158166741537732079)
                    ·
                      rfl

theorem cell22_3487645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3487645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487645 prefixEnd_3487645 := by exact prefixLift 3487645
  have htrace : WordTrace (prefixWord ++ tailWord_3487645) baseStart_3487645 baseEnd_3487645 := by
    simpa [prefixWord, tailWord_3487645, baseEnd_3487645] using wordTrace_append hprefix tailTrace_3487645
  have hstable : (prefixWord ++ tailWord_3487645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487645).length < 2 ^ (prefixWord ++ tailWord_3487645).sum := by decide
  have hdescent : baseEnd_3487645 < baseStart_3487645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487673 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_3487673 : Nat := 118140960795 + 3487673 * 2 ^ 59
def prefixEnd_3487673 : Nat := 4983230072969 + 3 ^ 40 * 3487673 * 2
def baseEnd_3487673 : Nat := 1193901743138958798031993

theorem tailTrace_3487673 : CollatzResearch.WordTrace tailWord_3487673 prefixEnd_3487673 1193901743138958798031993 := by
  unfold tailWord_3487673
  simp only [CollatzResearch.WordTrace]
  refine ⟨127205884693763842971619673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84803923129175895314413115 127205884693763842971619673)
  ·
    refine ⟨95404413520322882228714755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127205884693763842971619673 95404413520322882228714755)
    ·
      refine ⟨143106620280484323343072133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95404413520322882228714755 143106620280484323343072133)
      ·
        refine ⟨26832491302590810626826025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143106620280484323343072133 26832491302590810626826025)
        ·
          refine ⟨20124368476943107970119519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26832491302590810626826025 20124368476943107970119519)
          ·
            refine ⟨30186552715414661955179279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20124368476943107970119519 30186552715414661955179279)
            ·
              refine ⟨45279829073121992932768919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30186552715414661955179279 45279829073121992932768919)
              ·
                refine ⟨67919743609682989399153379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45279829073121992932768919 67919743609682989399153379)
                ·
                  refine ⟨101879615414524484098730069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67919743609682989399153379 101879615414524484098730069)
                  ·
                    refine ⟨1193901743138958798031993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101879615414524484098730069 1193901743138958798031993)
                    ·
                      rfl

theorem cell22_3487673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_3487673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487673 prefixEnd_3487673 := by exact prefixLift 3487673
  have htrace : WordTrace (prefixWord ++ tailWord_3487673) baseStart_3487673 baseEnd_3487673 := by
    simpa [prefixWord, tailWord_3487673, baseEnd_3487673] using wordTrace_append hprefix tailTrace_3487673
  have hstable : (prefixWord ++ tailWord_3487673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487673).length < 2 ^ (prefixWord ++ tailWord_3487673).sum := by decide
  have hdescent : baseEnd_3487673 < baseStart_3487673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3487692 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_3487692 : Nat := 118140960795 + 3487692 * 2 ^ 59
def prefixEnd_3487692 : Nat := 4983230072969 + 3 ^ 40 * 3487692 * 2
def baseEnd_3487692 : Nat := 1193908247227249081806935

theorem tailTrace_3487692 : CollatzResearch.WordTrace tailWord_3487692 prefixEnd_3487692 1193908247227249081806935 := by
  unfold tailWord_3487692
  simp only [CollatzResearch.WordTrace]
  refine ⟨63603288840347504608280665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84804385120463339477707553 63603288840347504608280665)
  ·
    refine ⟨47702466630260628456210499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63603288840347504608280665 47702466630260628456210499)
    ·
      refine ⟨71553699945390942684315749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47702466630260628456210499 71553699945390942684315749)
      ·
        refine ⟨13416318739760801753309203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71553699945390942684315749 13416318739760801753309203)
        ·
          refine ⟨20124478109641202629963805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416318739760801753309203 20124478109641202629963805)
          ·
            refine ⟨7546679291115450986236427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20124478109641202629963805 7546679291115450986236427)
            ·
              refine ⟨11320018936673176479354641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546679291115450986236427 11320018936673176479354641)
              ·
                refine ⟨8490014202504882359515981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11320018936673176479354641 8490014202504882359515981)
                ·
                  refine ⟨3183755325939330884818493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8490014202504882359515981 3183755325939330884818493)
                  ·
                    refine ⟨1193908247227249081806935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3183755325939330884818493 1193908247227249081806935)
                    ·
                      rfl

theorem cell22_3487692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_3487692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3487692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3487692 prefixEnd_3487692 := by exact prefixLift 3487692
  have htrace : WordTrace (prefixWord ++ tailWord_3487692) baseStart_3487692 baseEnd_3487692 := by
    simpa [prefixWord, tailWord_3487692, baseEnd_3487692] using wordTrace_append hprefix tailTrace_3487692
  have hstable : (prefixWord ++ tailWord_3487692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3487692).length < 2 ^ (prefixWord ++ tailWord_3487692).sum := by decide
  have hdescent : baseEnd_3487692 < baseStart_3487692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3487692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
