import V185TrunkScan23Chunk0972

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5759341 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_5759341 : Nat := 118140960795 + 5759341 * 2 ^ 59
def prefixEnd_5759341 : Nat := 4983230072969 + 3 ^ 40 * 5759341 * 2
def baseEnd_5759341 : Nat := 985770062048752095183593

theorem tailTrace_5759341 : CollatzResearch.WordTrace tailWord_5759341 prefixEnd_5759341 985770062048752095183593 := by
  unfold tailWord_5759341
  simp only [CollatzResearch.WordTrace]
  refine ⟨210060423427898648978149877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140040282285265765985433251 210060423427898648978149877)
  ·
    refine ⟨19693164696365498341701551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210060423427898648978149877 19693164696365498341701551)
    ·
      refine ⟨29539747044548247512552327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19693164696365498341701551 29539747044548247512552327)
      ·
        refine ⟨44309620566822371268828491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29539747044548247512552327 44309620566822371268828491)
        ·
          refine ⟨66464430850233556903242737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44309620566822371268828491 66464430850233556903242737)
          ·
            refine ⟨49848323137675167677432053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66464430850233556903242737 49848323137675167677432053)
            ·
              refine ⟨4673280294157046969759255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49848323137675167677432053 4673280294157046969759255)
              ·
                refine ⟨7009920441235570454638883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673280294157046969759255 7009920441235570454638883)
                ·
                  refine ⟨10514880661853355681958325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7009920441235570454638883 10514880661853355681958325)
                  ·
                    refine ⟨985770062048752095183593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10514880661853355681958325 985770062048752095183593)
                    ·
                      rfl

theorem cell23_5759341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_5759341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759341 prefixEnd_5759341 := by exact prefixLift 5759341
  have htrace : WordTrace (prefixWord ++ tailWord_5759341) baseStart_5759341 baseEnd_5759341 := by
    simpa [prefixWord, tailWord_5759341, baseEnd_5759341] using wordTrace_append hprefix tailTrace_5759341
  have hstable : (prefixWord ++ tailWord_5759341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759341).length < 2 ^ (prefixWord ++ tailWord_5759341).sum := by decide
  have hdescent : baseEnd_5759341 < baseStart_5759341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759355 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 1, 1, 3]
def baseStart_5759355 : Nat := 118140960795 + 5759355 * 2 ^ 59
def prefixEnd_5759355 : Nat := 4983230072969 + 3 ^ 40 * 5759355 * 2
def baseEnd_5759355 : Nat := 2957317374875419230775715

theorem tailTrace_5759355 : CollatzResearch.WordTrace tailWord_5759355 prefixEnd_5759355 2957317374875419230775715 := by
  unfold tailWord_5759355
  simp only [CollatzResearch.WordTrace]
  refine ⟨210060934049847929369159519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140040622699898619579439679 210060934049847929369159519)
  ·
    refine ⟨315091401074771894053739279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210060934049847929369159519 315091401074771894053739279)
    ·
      refine ⟨472637101612157841080608919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315091401074771894053739279 472637101612157841080608919)
      ·
        refine ⟨708955652418236761620913379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472637101612157841080608919 708955652418236761620913379)
        ·
          refine ⟨1063433478627355142431370069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708955652418236761620913379 1063433478627355142431370069)
          ·
            refine ⟨6231055538832159037683809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1063433478627355142431370069 6231055538832159037683809)
            ·
              refine ⟨4673291654124119278262857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231055538832159037683809 4673291654124119278262857)
              ·
                refine ⟨3504968740593089458697143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673291654124119278262857 3504968740593089458697143)
                ·
                  refine ⟨5257453110889634188045715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504968740593089458697143 5257453110889634188045715)
                  ·
                    refine ⟨7886179666334451282068573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257453110889634188045715 7886179666334451282068573)
                    ·
                      refine ⟨2957317374875419230775715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886179666334451282068573 2957317374875419230775715)
                      ·
                        rfl

theorem cell23_5759355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 1, 3].length) (baseStart_5759355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759355 prefixEnd_5759355 := by exact prefixLift 5759355
  have htrace : WordTrace (prefixWord ++ tailWord_5759355) baseStart_5759355 baseEnd_5759355 := by
    simpa [prefixWord, tailWord_5759355, baseEnd_5759355] using wordTrace_append hprefix tailTrace_5759355
  have hstable : (prefixWord ++ tailWord_5759355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759355).length < 2 ^ (prefixWord ++ tailWord_5759355).sum := by decide
  have hdescent : baseEnd_5759355 < baseStart_5759355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759364 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5759364 : Nat := 118140960795 + 5759364 * 2 ^ 59
def prefixEnd_5759364 : Nat := 4983230072969 + 3 ^ 40 * 5759364 * 2
def baseEnd_5759364 : Nat := 2957321996201309695563173

theorem tailTrace_5759364 : CollatzResearch.WordTrace tailWord_5759364 prefixEnd_5759364 2957321996201309695563173 := by
  unfold tailWord_5759364
  simp only [CollatzResearch.WordTrace]
  refine ⟨105030631153407661953118573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140040841537876882604158097 105030631153407661953118573)
  ·
    refine ⟨39386486682527873232419465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105030631153407661953118573 39386486682527873232419465)
    ·
      refine ⟨29539865011895904924314599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39386486682527873232419465 29539865011895904924314599)
      ·
        refine ⟨44309797517843857386471899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29539865011895904924314599 44309797517843857386471899)
        ·
          refine ⟨66464696276765786079707849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44309797517843857386471899 66464696276765786079707849)
          ·
            refine ⟨49848522207574339559780887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66464696276765786079707849 49848522207574339559780887)
            ·
              refine ⟨74772783311361509339671331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49848522207574339559780887 74772783311361509339671331)
              ·
                refine ⟨112159174967042264009506997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74772783311361509339671331 112159174967042264009506997)
                ·
                  refine ⟨10514922653160212250891281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112159174967042264009506997 10514922653160212250891281)
                  ·
                    refine ⟨7886191989870159188168461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10514922653160212250891281 7886191989870159188168461)
                    ·
                      refine ⟨2957321996201309695563173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886191989870159188168461 2957321996201309695563173)
                      ·
                        rfl

theorem cell23_5759364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5759364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759364 prefixEnd_5759364 := by exact prefixLift 5759364
  have htrace : WordTrace (prefixWord ++ tailWord_5759364) baseStart_5759364 baseEnd_5759364 := by
    simpa [prefixWord, tailWord_5759364, baseEnd_5759364] using wordTrace_append hprefix tailTrace_5759364
  have hstable : (prefixWord ++ tailWord_5759364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759364).length < 2 ^ (prefixWord ++ tailWord_5759364).sum := by decide
  have hdescent : baseEnd_5759364 < baseStart_5759364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759382 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5759382 : Nat := 118140960795 + 5759382 * 2 ^ 59
def prefixEnd_5759382 : Nat := 4983230072969 + 3 ^ 40 * 5759382 * 2
def baseEnd_5759382 : Nat := 2957331238853090625138091

theorem tailTrace_5759382 : CollatzResearch.WordTrace tailWord_5759382 prefixEnd_5759382 2957331238853090625138091 := by
  unfold tailWord_5759382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128869926296882061274525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140041279213833408653594933 13128869926296882061274525)
  ·
    refine ⟨4923326222361330772977947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13128869926296882061274525 4923326222361330772977947)
    ·
      refine ⟨7384989333541996159466921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4923326222361330772977947 7384989333541996159466921)
      ·
        refine ⟨5538742000156497119600191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7384989333541996159466921 5538742000156497119600191)
        ·
          refine ⟨8308113000234745679400287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538742000156497119600191 8308113000234745679400287)
          ·
            refine ⟨12462169500352118519100431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308113000234745679400287 12462169500352118519100431)
            ·
              refine ⟨18693254250528177778650647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12462169500352118519100431 18693254250528177778650647)
              ·
                refine ⟨28039881375792266667975971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18693254250528177778650647 28039881375792266667975971)
                ·
                  refine ⟨42059822063688400001963957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28039881375792266667975971 42059822063688400001963957)
                  ·
                    refine ⟨3943108318470787500184121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42059822063688400001963957 3943108318470787500184121)
                    ·
                      refine ⟨2957331238853090625138091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943108318470787500184121 2957331238853090625138091)
                      ·
                        rfl

theorem cell23_5759382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5759382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759382 prefixEnd_5759382 := by exact prefixLift 5759382
  have htrace : WordTrace (prefixWord ++ tailWord_5759382) baseStart_5759382 baseEnd_5759382 := by
    simpa [prefixWord, tailWord_5759382, baseEnd_5759382] using wordTrace_append hprefix tailTrace_5759382
  have hstable : (prefixWord ++ tailWord_5759382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759382).length < 2 ^ (prefixWord ++ tailWord_5759382).sum := by decide
  have hdescent : baseEnd_5759382 < baseStart_5759382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759395 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 1, 2, 2]
def baseStart_5759395 : Nat := 118140960795 + 5759395 * 2 ^ 59
def prefixEnd_5759395 : Nat := 4983230072969 + 3 ^ 40 * 5759395 * 2
def baseEnd_5759395 : Nat := 2957337914101599074275531

theorem tailTrace_5759395 : CollatzResearch.WordTrace tailWord_5759395 prefixEnd_5759395 2957337914101599074275531 := by
  unfold tailWord_5759395
  simp only [CollatzResearch.WordTrace]
  refine ⟨210062392969703016200615639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140041595313135344133743759 210062392969703016200615639)
  ·
    refine ⟨315093589454554524300923459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210062392969703016200615639 315093589454554524300923459)
    ·
      refine ⟨472640384181831786451385189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315093589454554524300923459 472640384181831786451385189)
      ·
        refine ⟨88620072034093459959634723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 472640384181831786451385189 88620072034093459959634723)
        ·
          refine ⟨132930108051140189939452085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88620072034093459959634723 132930108051140189939452085)
          ·
            refine ⟨12462197629794392806823633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132930108051140189939452085 12462197629794392806823633)
            ·
              refine ⟨9346648222345794605117725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12462197629794392806823633 9346648222345794605117725)
              ·
                refine ⟨3504993083379672976919147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9346648222345794605117725 3504993083379672976919147)
                ·
                  refine ⟨5257489625069509465378721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504993083379672976919147 5257489625069509465378721)
                  ·
                    refine ⟨3943117218802132099034041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5257489625069509465378721 3943117218802132099034041)
                    ·
                      refine ⟨2957337914101599074275531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943117218802132099034041 2957337914101599074275531)
                      ·
                        rfl

theorem cell23_5759395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_5759395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759395 prefixEnd_5759395 := by exact prefixLift 5759395
  have htrace : WordTrace (prefixWord ++ tailWord_5759395) baseStart_5759395 baseEnd_5759395 := by
    simpa [prefixWord, tailWord_5759395, baseEnd_5759395] using wordTrace_append hprefix tailTrace_5759395
  have hstable : (prefixWord ++ tailWord_5759395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759395).length < 2 ^ (prefixWord ++ tailWord_5759395).sum := by decide
  have hdescent : baseEnd_5759395 < baseStart_5759395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759405 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_5759405 : Nat := 118140960795 + 5759405 * 2 ^ 59
def prefixEnd_5759405 : Nat := 4983230072969 + 3 ^ 40 * 5759405 * 2
def baseEnd_5759405 : Nat := 985781016302714678383495

theorem tailTrace_5759405 : CollatzResearch.WordTrace tailWord_5759405 prefixEnd_5759405 985781016302714678383495 := by
  unfold tailWord_5759405
  simp only [CollatzResearch.WordTrace]
  refine ⟨210062757699666787908479669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140041838466444525272319779 210062757699666787908479669)
  ·
    refine ⟨19693383534343761366419969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210062757699666787908479669 19693383534343761366419969)
    ·
      refine ⟨14770037650757821024814977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19693383534343761366419969 14770037650757821024814977)
      ·
        refine ⟨11077528238068365768611233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14770037650757821024814977 11077528238068365768611233)
        ·
          refine ⟨8308146178551274326458425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11077528238068365768611233 8308146178551274326458425)
          ·
            refine ⟨6231109633913455744843819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308146178551274326458425 6231109633913455744843819)
            ·
              refine ⟨9346664450870183617265729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231109633913455744843819 9346664450870183617265729)
              ·
                refine ⟨7009998338152637712949297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9346664450870183617265729 7009998338152637712949297)
                ·
                  refine ⟨5257498753614478284711973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7009998338152637712949297 5257498753614478284711973)
                  ·
                    refine ⟨985781016302714678383495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257498753614478284711973 985781016302714678383495)
                    ·
                      rfl

theorem cell23_5759405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_5759405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759405 prefixEnd_5759405 := by exact prefixLift 5759405
  have htrace : WordTrace (prefixWord ++ tailWord_5759405) baseStart_5759405 baseEnd_5759405 := by
    simpa [prefixWord, tailWord_5759405, baseEnd_5759405] using wordTrace_append hprefix tailTrace_5759405
  have hstable : (prefixWord ++ tailWord_5759405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759405).length < 2 ^ (prefixWord ++ tailWord_5759405).sum := by decide
  have hdescent : baseEnd_5759405 < baseStart_5759405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759467 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7]
def baseStart_5759467 : Nat := 118140960795 + 5759467 * 2 ^ 59
def prefixEnd_5759467 : Nat := 4983230072969 + 3 ^ 40 * 5759467 * 2
def baseEnd_5759467 : Nat := 2957374884708722792575199

theorem tailTrace_5759467 : CollatzResearch.WordTrace tailWord_5759467 prefixEnd_5759467 2957374884708722792575199 := by
  unfold tailWord_5759467
  simp only [CollatzResearch.WordTrace]
  refine ⟨210065019025442172497236655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140043346016961448331491103 210065019025442172497236655)
  ·
    refine ⟨315097528538163258745854983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210065019025442172497236655 315097528538163258745854983)
    ·
      refine ⟨472646292807244888118782475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315097528538163258745854983 472646292807244888118782475)
      ·
        refine ⟨708969439210867332178173713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472646292807244888118782475 708969439210867332178173713)
        ·
          refine ⟨531727079408150499133630285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708969439210867332178173713 531727079408150499133630285)
          ·
            refine ⟨199397654778056437175111357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531727079408150499133630285 199397654778056437175111357)
            ·
              refine ⟨74774120541771163940666759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199397654778056437175111357 74774120541771163940666759)
              ·
                refine ⟨112161180812656745911000139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74774120541771163940666759 112161180812656745911000139)
                ·
                  refine ⟨168241771218985118866500209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112161180812656745911000139 168241771218985118866500209)
                  ·
                    refine ⟨126181328414238839149875157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168241771218985118866500209 126181328414238839149875157)
                    ·
                      refine ⟨2957374884708722792575199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126181328414238839149875157 2957374884708722792575199)
                      ·
                        rfl

theorem cell23_5759467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_5759467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759467 prefixEnd_5759467 := by exact prefixLift 5759467
  have htrace : WordTrace (prefixWord ++ tailWord_5759467) baseStart_5759467 baseEnd_5759467 := by
    simpa [prefixWord, tailWord_5759467, baseEnd_5759467] using wordTrace_append hprefix tailTrace_5759467
  have hstable : (prefixWord ++ tailWord_5759467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759467).length < 2 ^ (prefixWord ++ tailWord_5759467).sum := by decide
  have hdescent : baseEnd_5759467 < baseStart_5759467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759468 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 2, 2, 2]
def baseStart_5759468 : Nat := 118140960795 + 5759468 * 2 ^ 59
def prefixEnd_5759468 : Nat := 4983230072969 + 3 ^ 40 * 5759468 * 2
def baseEnd_5759468 : Nat := 2957375398189377288662695

theorem tailTrace_5759468 : CollatzResearch.WordTrace tailWord_5759468 prefixEnd_5759468 2957375398189377288662695 := by
  unfold tailWord_5759468
  simp only [CollatzResearch.WordTrace]
  refine ⟨105032527749219274834011529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140043370332292366445348705 105032527749219274834011529)
  ·
    refine ⟨78774395811914456125508647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105032527749219274834011529 78774395811914456125508647)
    ·
      refine ⟨118161593717871684188262971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78774395811914456125508647 118161593717871684188262971)
      ·
        refine ⟨177242390576807526282394457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118161593717871684188262971 177242390576807526282394457)
        ·
          refine ⟨132931792932605644711795843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177242390576807526282394457 132931792932605644711795843)
          ·
            refine ⟨199397689398908467067693765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132931792932605644711795843 199397689398908467067693765)
            ·
              refine ⟨37387066762295337575192581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199397689398908467067693765 37387066762295337575192581)
              ·
                refine ⟨7010075017930375795348609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37387066762295337575192581 7010075017930375795348609)
                ·
                  refine ⟨5257556263447781846511457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7010075017930375795348609 5257556263447781846511457)
                  ·
                    refine ⟨3943167197585836384883593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5257556263447781846511457 3943167197585836384883593)
                    ·
                      refine ⟨2957375398189377288662695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943167197585836384883593 2957375398189377288662695)
                      ·
                        rfl

theorem cell23_5759468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_5759468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759468 prefixEnd_5759468 := by exact prefixLift 5759468
  have htrace : WordTrace (prefixWord ++ tailWord_5759468) baseStart_5759468 baseEnd_5759468 := by
    simpa [prefixWord, tailWord_5759468, baseEnd_5759468] using wordTrace_append hprefix tailTrace_5759468
  have hstable : (prefixWord ++ tailWord_5759468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759468).length < 2 ^ (prefixWord ++ tailWord_5759468).sum := by decide
  have hdescent : baseEnd_5759468 < baseStart_5759468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759484 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_5759484 : Nat := 118140960795 + 5759484 * 2 ^ 59
def prefixEnd_5759484 : Nat := 4983230072969 + 3 ^ 40 * 5759484 * 2
def baseEnd_5759484 : Nat := 2957383613879849226062621

theorem tailTrace_5759484 : CollatzResearch.WordTrace tailWord_5759484 prefixEnd_5759484 2957383613879849226062621 := by
  unfold tailWord_5759484
  simp only [CollatzResearch.WordTrace]
  refine ⟨105032819533190292200302753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140043759377587056267070337 105032819533190292200302753)
  ·
    refine ⟨78774614649892719150227065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105032819533190292200302753 78774614649892719150227065)
    ·
      refine ⟨59080960987419539362670299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78774614649892719150227065 59080960987419539362670299)
      ·
        refine ⟨88621441481129309044005449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59080960987419539362670299 88621441481129309044005449)
        ·
          refine ⟨66466081110846981783004087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88621441481129309044005449 66466081110846981783004087)
          ·
            refine ⟨99699121666270472674506131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66466081110846981783004087 99699121666270472674506131)
            ·
              refine ⟨149548682499405709011759197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99699121666270472674506131 149548682499405709011759197)
              ·
                refine ⟨56080755937277140879409699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149548682499405709011759197 56080755937277140879409699)
                ·
                  refine ⟨84121133905915711319114549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56080755937277140879409699 84121133905915711319114549)
                  ·
                    refine ⟨7886356303679597936166989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84121133905915711319114549 7886356303679597936166989)
                    ·
                      refine ⟨2957383613879849226062621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886356303679597936166989 2957383613879849226062621)
                      ·
                        rfl

theorem cell23_5759484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_5759484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759484 prefixEnd_5759484 := by exact prefixLift 5759484
  have htrace : WordTrace (prefixWord ++ tailWord_5759484) baseStart_5759484 baseEnd_5759484 := by
    simpa [prefixWord, tailWord_5759484, baseEnd_5759484] using wordTrace_append hprefix tailTrace_5759484
  have hstable : (prefixWord ++ tailWord_5759484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759484).length < 2 ^ (prefixWord ++ tailWord_5759484).sum := by decide
  have hdescent : baseEnd_5759484 < baseStart_5759484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759514 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_5759514 : Nat := 118140960795 + 5759514 * 2 ^ 59
def prefixEnd_5759514 : Nat := 4983230072969 + 3 ^ 40 * 5759514 * 2
def baseEnd_5759514 : Nat := 2957399018299484108687483

theorem tailTrace_5759514 : CollatzResearch.WordTrace tailWord_5759514 prefixEnd_5759514 2957399018299484108687483 := by
  unfold tailWord_5759514
  simp only [CollatzResearch.WordTrace]
  refine ⟨52516683314067974881049399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140044488837514599682798397 52516683314067974881049399)
  ·
    refine ⟨78775024971101962321574099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52516683314067974881049399 78775024971101962321574099)
    ·
      refine ⟨118162537456652943482361149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78775024971101962321574099 118162537456652943482361149)
      ·
        refine ⟨44310951546244853805885431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118162537456652943482361149 44310951546244853805885431)
        ·
          refine ⟨66466427319367280708828147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44310951546244853805885431 66466427319367280708828147)
          ·
            refine ⟨99699640979050921063242221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66466427319367280708828147 99699640979050921063242221)
            ·
              refine ⟨37387365367144095398715833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99699640979050921063242221 37387365367144095398715833)
              ·
                refine ⟨28040524025358071549036875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37387365367144095398715833 28040524025358071549036875)
                ·
                  refine ⟨42060786038037107323555313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28040524025358071549036875 42060786038037107323555313)
                  ·
                    refine ⟨31545589528527830492666485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42060786038037107323555313 31545589528527830492666485)
                    ·
                      refine ⟨2957399018299484108687483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31545589528527830492666485 2957399018299484108687483)
                      ·
                        rfl

theorem cell23_5759514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_5759514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759514 prefixEnd_5759514 := by exact prefixLift 5759514
  have htrace : WordTrace (prefixWord ++ tailWord_5759514) baseStart_5759514 baseEnd_5759514 := by
    simpa [prefixWord, tailWord_5759514, baseEnd_5759514] using wordTrace_append hprefix tailTrace_5759514
  have hstable : (prefixWord ++ tailWord_5759514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759514).length < 2 ^ (prefixWord ++ tailWord_5759514).sum := by decide
  have hdescent : baseEnd_5759514 < baseStart_5759514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759528 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5759528 : Nat := 118140960795 + 5759528 * 2 ^ 59
def prefixEnd_5759528 : Nat := 4983230072969 + 3 ^ 40 * 5759528 * 2
def baseEnd_5759528 : Nat := 2957406207028647053912419

theorem tailTrace_5759528 : CollatzResearch.WordTrace tailWord_5759528 prefixEnd_5759528 2957406207028647053912419 := by
  unfold tailWord_5759528
  simp only [CollatzResearch.WordTrace]
  refine ⟨105033621939110589957603619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140044829252147453276804825 105033621939110589957603619)
  ·
    refine ⟨157550432908665884936405429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105033621939110589957603619 157550432908665884936405429)
    ·
      refine ⟨14770353085187426712788009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157550432908665884936405429 14770353085187426712788009)
      ·
        refine ⟨11077764813890570034591007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14770353085187426712788009 11077764813890570034591007)
        ·
          refine ⟨16616647220835855051886511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11077764813890570034591007 16616647220835855051886511)
          ·
            refine ⟨24924970831253782577829767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16616647220835855051886511 24924970831253782577829767)
            ·
              refine ⟨37387456246880673866744651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24924970831253782577829767 37387456246880673866744651)
              ·
                refine ⟨56081184370321010800116977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37387456246880673866744651 56081184370321010800116977)
                ·
                  refine ⟨42060888277740758100087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56081184370321010800116977 42060888277740758100087733)
                  ·
                    refine ⟨3943208276038196071883225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42060888277740758100087733 3943208276038196071883225)
                    ·
                      refine ⟨2957406207028647053912419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943208276038196071883225 2957406207028647053912419)
                      ·
                        rfl

theorem cell23_5759528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5759528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759528 prefixEnd_5759528 := by exact prefixLift 5759528
  have htrace : WordTrace (prefixWord ++ tailWord_5759528) baseStart_5759528 baseEnd_5759528 := by
    simpa [prefixWord, tailWord_5759528, baseEnd_5759528] using wordTrace_append hprefix tailTrace_5759528
  have hstable : (prefixWord ++ tailWord_5759528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759528).length < 2 ^ (prefixWord ++ tailWord_5759528).sum := by decide
  have hdescent : baseEnd_5759528 < baseStart_5759528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759551 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 3, 4]
def baseStart_5759551 : Nat := 118140960795 + 5759551 * 2 ^ 59
def prefixEnd_5759551 : Nat := 4983230072969 + 3 ^ 40 * 5759551 * 2
def baseEnd_5759551 : Nat := 985806005694566821308271

theorem tailTrace_5759551 : CollatzResearch.WordTrace tailWord_5759551 prefixEnd_5759551 985806005694566821308271 := by
  unfold tailWord_5759551
  simp only [CollatzResearch.WordTrace]
  refine ⟨210068082757137854843294507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140045388504758569895529671 210068082757137854843294507)
  ·
    refine ⟨315102124135706782264941761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210068082757137854843294507 315102124135706782264941761)
    ·
      refine ⟨236326593101780086698706321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315102124135706782264941761 236326593101780086698706321)
      ·
        refine ⟨177244944826335065024029741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236326593101780086698706321 177244944826335065024029741)
        ·
          refine ⟨66466854309875649384011153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177244944826335065024029741 66466854309875649384011153)
          ·
            refine ⟨49850140732406737038008365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66466854309875649384011153 49850140732406737038008365)
            ·
              refine ⟨18693802774652526389253137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49850140732406737038008365 18693802774652526389253137)
              ·
                refine ⟨14020352080989394791939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18693802774652526389253137 14020352080989394791939853)
                ·
                  refine ⟨5257632030371023046977445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14020352080989394791939853 5257632030371023046977445)
                  ·
                    refine ⟨985806005694566821308271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257632030371023046977445 985806005694566821308271)
                    ·
                      rfl

theorem cell23_5759551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 4].length) (baseStart_5759551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759551 prefixEnd_5759551 := by exact prefixLift 5759551
  have htrace : WordTrace (prefixWord ++ tailWord_5759551) baseStart_5759551 baseEnd_5759551 := by
    simpa [prefixWord, tailWord_5759551, baseEnd_5759551] using wordTrace_append hprefix tailTrace_5759551
  have hstable : (prefixWord ++ tailWord_5759551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759551).length < 2 ^ (prefixWord ++ tailWord_5759551).sum := by decide
  have hdescent : baseEnd_5759551 < baseStart_5759551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759564 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 8]
def baseStart_5759564 : Nat := 118140960795 + 5759564 * 2 ^ 59
def prefixEnd_5759564 : Nat := 4983230072969 + 3 ^ 40 * 5759564 * 2
def baseEnd_5759564 : Nat := 328602743592467657006917

theorem tailTrace_5759564 : CollatzResearch.WordTrace tailWord_5759564 prefixEnd_5759564 328602743592467657006917 := by
  unfold tailWord_5759564
  simp only [CollatzResearch.WordTrace]
  refine ⟨105034278453045379031758873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140045704604060505375678497 105034278453045379031758873)
  ·
    refine ⟨78775708839784034273819155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105034278453045379031758873 78775708839784034273819155)
    ·
      refine ⟨118163563259676051410728733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78775708839784034273819155 118163563259676051410728733)
      ·
        refine ⟨44311336222378519279023275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118163563259676051410728733 44311336222378519279023275)
        ·
          refine ⟨66467004333567778918534913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44311336222378519279023275 66467004333567778918534913)
          ·
            refine ⟨49850253250175834188901185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66467004333567778918534913 49850253250175834188901185)
            ·
              refine ⟨37387689937631875641675889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49850253250175834188901185 37387689937631875641675889)
              ·
                refine ⟨28040767453223906731256917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37387689937631875641675889 28040767453223906731256917)
                ·
                  refine ⟨328602743592467657006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28040767453223906731256917 328602743592467657006917)
                  ·
                    rfl

theorem cell23_5759564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_5759564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759564 prefixEnd_5759564 := by exact prefixLift 5759564
  have htrace : WordTrace (prefixWord ++ tailWord_5759564) baseStart_5759564 baseEnd_5759564 := by
    simpa [prefixWord, tailWord_5759564, baseEnd_5759564] using wordTrace_append hprefix tailTrace_5759564
  have hstable : (prefixWord ++ tailWord_5759564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759564).length < 2 ^ (prefixWord ++ tailWord_5759564).sum := by decide
  have hdescent : baseEnd_5759564 < baseStart_5759564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759584 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_5759584 : Nat := 118140960795 + 5759584 * 2 ^ 59
def prefixEnd_5759584 : Nat := 4983230072969 + 3 ^ 40 * 5759584 * 2
def baseEnd_5759584 : Nat := 2957434961945298834812161

theorem tailTrace_5759584 : CollatzResearch.WordTrace tailWord_5759584 prefixEnd_5759584 2957434961945298834812161 := by
  unfold tailWord_5759584
  simp only [CollatzResearch.WordTrace]
  refine ⟨105034643183009150739622903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140046190910678867652830537 105034643183009150739622903)
  ·
    refine ⟨157551964774513726109434355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105034643183009150739622903 157551964774513726109434355)
    ·
      refine ⟨236327947161770589164151533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157551964774513726109434355 236327947161770589164151533)
      ·
        refine ⟨88622980185663970936556825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236327947161770589164151533 88622980185663970936556825)
        ·
          refine ⟨66467235139247978202417619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88622980185663970936556825 66467235139247978202417619)
          ·
            refine ⟨99700852708871967303626429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66467235139247978202417619 99700852708871967303626429)
            ·
              refine ⟨37387819765826987738859911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99700852708871967303626429 37387819765826987738859911)
              ·
                refine ⟨56081729648740481608289867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37387819765826987738859911 56081729648740481608289867)
                ·
                  refine ⟨84122594473110722412434801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56081729648740481608289867 84122594473110722412434801)
                  ·
                    refine ⟨63091945854833041809326101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84122594473110722412434801 63091945854833041809326101)
                    ·
                      refine ⟨2957434961945298834812161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63091945854833041809326101 2957434961945298834812161)
                      ·
                        rfl

theorem cell23_5759584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_5759584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759584 prefixEnd_5759584 := by exact prefixLift 5759584
  have htrace : WordTrace (prefixWord ++ tailWord_5759584) baseStart_5759584 baseEnd_5759584 := by
    simpa [prefixWord, tailWord_5759584, baseEnd_5759584] using wordTrace_append hprefix tailTrace_5759584
  have hstable : (prefixWord ++ tailWord_5759584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759584).length < 2 ^ (prefixWord ++ tailWord_5759584).sum := by decide
  have hdescent : baseEnd_5759584 < baseStart_5759584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759631 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 8, 2]
def baseStart_5759631 : Nat := 118140960795 + 5759631 * 2 ^ 59
def prefixEnd_5759631 : Nat := 4983230072969 + 3 ^ 40 * 5759631 * 2
def baseEnd_5759631 : Nat := 2957459095536060150924445

theorem tailTrace_5759631 : CollatzResearch.WordTrace tailWord_5759631 prefixEnd_5759631 2957459095536060150924445 := by
  unfold tailWord_5759631
  simp only [CollatzResearch.WordTrace]
  refine ⟨210071000596848028506206747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140047333731232019004137831 210071000596848028506206747)
  ·
    refine ⟨315106500895272042759310121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210071000596848028506206747 315106500895272042759310121)
    ·
      refine ⟨236329875671454032069482591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315106500895272042759310121 236329875671454032069482591)
      ·
        refine ⟨354494813507181048104223887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236329875671454032069482591 354494813507181048104223887)
        ·
          refine ⟨531742220260771572156335831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354494813507181048104223887 531742220260771572156335831)
          ·
            refine ⟨797613330391157358234503747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531742220260771572156335831 797613330391157358234503747)
            ·
              refine ⟨1196419995586736037351755621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797613330391157358234503747 1196419995586736037351755621)
              ·
                refine ⟨224328749172513007003454179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1196419995586736037351755621 224328749172513007003454179)
                ·
                  refine ⟨336493123758769510505181269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224328749172513007003454179 336493123758769510505181269)
                  ·
                    refine ⟨3943278794048080201232593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 336493123758769510505181269 3943278794048080201232593)
                    ·
                      refine ⟨2957459095536060150924445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943278794048080201232593 2957459095536060150924445)
                      ·
                        rfl

theorem cell23_5759631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8, 2].length) (baseStart_5759631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759631 prefixEnd_5759631 := by exact prefixLift 5759631
  have htrace : WordTrace (prefixWord ++ tailWord_5759631) baseStart_5759631 baseEnd_5759631 := by
    simpa [prefixWord, tailWord_5759631, baseEnd_5759631] using wordTrace_append hprefix tailTrace_5759631
  have hstable : (prefixWord ++ tailWord_5759631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759631).length < 2 ^ (prefixWord ++ tailWord_5759631).sum := by decide
  have hdescent : baseEnd_5759631 < baseStart_5759631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759641 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 4, 4]
def baseStart_5759641 : Nat := 118140960795 + 5759641 * 2 ^ 59
def prefixEnd_5759641 : Nat := 4983230072969 + 3 ^ 40 * 5759641 * 2
def baseEnd_5759641 : Nat := 985821410114201703933133

theorem tailTrace_5759641 : CollatzResearch.WordTrace tailWord_5759641 prefixEnd_5759641 985821410114201703933133 := by
  unfold tailWord_5759641
  simp only [CollatzResearch.WordTrace]
  refine ⟨210071365326811800214070777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140047576884541200142713851 210071365326811800214070777)
  ·
    refine ⟨157553523995108850160553083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210071365326811800214070777 157553523995108850160553083)
    ·
      refine ⟨236330285992663275240829625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157553523995108850160553083 236330285992663275240829625)
      ·
        refine ⟨177247714494497456430622219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236330285992663275240829625 177247714494497456430622219)
        ·
          refine ⟨265871571741746184645933329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177247714494497456430622219 265871571741746184645933329)
          ·
            refine ⟨199403678806309638484449997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265871571741746184645933329 199403678806309638484449997)
            ·
              refine ⟨74776379552366114431668749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199403678806309638484449997 74776379552366114431668749)
              ·
                refine ⟨28041142332137292911875781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74776379552366114431668749 28041142332137292911875781)
                ·
                  refine ⟨5257714187275742420976709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28041142332137292911875781 5257714187275742420976709)
                  ·
                    refine ⟨985821410114201703933133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257714187275742420976709 985821410114201703933133)
                    ·
                      rfl

theorem cell23_5759641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_5759641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759641 prefixEnd_5759641 := by exact prefixLift 5759641
  have htrace : WordTrace (prefixWord ++ tailWord_5759641) baseStart_5759641 baseEnd_5759641 := by
    simpa [prefixWord, tailWord_5759641, baseEnd_5759641] using wordTrace_append hprefix tailTrace_5759641
  have hstable : (prefixWord ++ tailWord_5759641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759641).length < 2 ^ (prefixWord ++ tailWord_5759641).sum := by decide
  have hdescent : baseEnd_5759641 < baseStart_5759641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759662 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5759662 : Nat := 118140960795 + 5759662 * 2 ^ 59
def prefixEnd_5759662 : Nat := 4983230072969 + 3 ^ 40 * 5759662 * 2
def baseEnd_5759662 : Nat := 985825004478783176545601

theorem tailTrace_5759662 : CollatzResearch.WordTrace tailWord_5759662 prefixEnd_5759662 985825004478783176545601 := by
  unfold tailWord_5759662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259016407466965100073155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140048087506490480533723493 26259016407466965100073155)
  ·
    refine ⟨39388524611200447650109733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26259016407466965100073155 39388524611200447650109733)
    ·
      refine ⟨7385348364600083934395575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39388524611200447650109733 7385348364600083934395575)
      ·
        refine ⟨11078022546900125901593363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385348364600083934395575 11078022546900125901593363)
        ·
          refine ⟨16617033820350188852390045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078022546900125901593363 16617033820350188852390045)
          ·
            refine ⟨6231387682631320819646267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16617033820350188852390045 6231387682631320819646267)
            ·
              refine ⟨9347081523946981229469401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231387682631320819646267 9347081523946981229469401)
              ·
                refine ⟨7010311142960235922102051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9347081523946981229469401 7010311142960235922102051)
                ·
                  refine ⟨10515466714440353883153077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7010311142960235922102051 10515466714440353883153077)
                  ·
                    refine ⟨985825004478783176545601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515466714440353883153077 985825004478783176545601)
                    ·
                      rfl

theorem cell23_5759662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5759662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759662 prefixEnd_5759662 := by exact prefixLift 5759662
  have htrace : WordTrace (prefixWord ++ tailWord_5759662) baseStart_5759662 baseEnd_5759662 := by
    simpa [prefixWord, tailWord_5759662, baseEnd_5759662] using wordTrace_append hprefix tailTrace_5759662
  have hstable : (prefixWord ++ tailWord_5759662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759662).length < 2 ^ (prefixWord ++ tailWord_5759662).sum := by decide
  have hdescent : baseEnd_5759662 < baseStart_5759662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759665 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5759665 : Nat := 118140960795 + 5759665 * 2 ^ 59
def prefixEnd_5759665 : Nat := 4983230072969 + 3 ^ 40 * 5759665 * 2
def baseEnd_5759665 : Nat := 2957476553878313017899289

theorem tailTrace_5759665 : CollatzResearch.WordTrace tailWord_5759665 prefixEnd_5759665 2957476553878313017899289 := by
  unfold tailWord_5759665
  simp only [CollatzResearch.WordTrace]
  refine ⟨210072240678724852312944449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140048160452483234875296299 210072240678724852312944449)
  ·
    refine ⟨157554180509043639234708337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210072240678724852312944449 157554180509043639234708337)
    ·
      refine ⟨118165635381782729426031253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157554180509043639234708337 118165635381782729426031253)
      ·
        refine ⟨5539014158521065441845215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118165635381782729426031253 5539014158521065441845215)
        ·
          refine ⟨8308521237781598162767823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539014158521065441845215 8308521237781598162767823)
          ·
            refine ⟨12462781856672397244151735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308521237781598162767823 12462781856672397244151735)
            ·
              refine ⟨18694172785008595866227603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12462781856672397244151735 18694172785008595866227603)
              ·
                refine ⟨28041259177512893799341405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18694172785008595866227603 28041259177512893799341405)
                ·
                  refine ⟨10515472191567335174753027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28041259177512893799341405 10515472191567335174753027)
                  ·
                    refine ⟨15773208287351002762129541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10515472191567335174753027 15773208287351002762129541)
                    ·
                      refine ⟨2957476553878313017899289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15773208287351002762129541 2957476553878313017899289)
                      ·
                        rfl

theorem cell23_5759665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5759665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759665 prefixEnd_5759665 := by exact prefixLift 5759665
  have htrace : WordTrace (prefixWord ++ tailWord_5759665) baseStart_5759665 baseEnd_5759665 := by
    simpa [prefixWord, tailWord_5759665, baseEnd_5759665] using wordTrace_append hprefix tailTrace_5759665
  have hstable : (prefixWord ++ tailWord_5759665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759665).length < 2 ^ (prefixWord ++ tailWord_5759665).sum := by decide
  have hdescent : baseEnd_5759665 < baseStart_5759665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759678 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5759678 : Nat := 118140960795 + 5759678 * 2 ^ 59
def prefixEnd_5759678 : Nat := 4983230072969 + 3 ^ 40 * 5759678 * 2
def baseEnd_5759678 : Nat := 2957483229126821467036729

theorem tailTrace_5759678 : CollatzResearch.WordTrace tailWord_5759678 prefixEnd_5759678 2957483229126821467036729 := by
  unfold tailWord_5759678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259089353459719441645961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140048476551785170355445125 26259089353459719441645961)
  ·
    refine ⟨19694317015094789581234471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26259089353459719441645961 19694317015094789581234471)
    ·
      refine ⟨29541475522642184371851707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694317015094789581234471 29541475522642184371851707)
      ·
        refine ⟨44312213283963276557777561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29541475522642184371851707 44312213283963276557777561)
        ·
          refine ⟨33234159962972457418333171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44312213283963276557777561 33234159962972457418333171)
          ·
            refine ⟨49851239944458686127499757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33234159962972457418333171 49851239944458686127499757)
            ·
              refine ⟨18694214979172007297812409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49851239944458686127499757 18694214979172007297812409)
              ·
                refine ⟨14020661234379005473359307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18694214979172007297812409 14020661234379005473359307)
                ·
                  refine ⟨21030991851568508210038961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14020661234379005473359307 21030991851568508210038961)
                  ·
                    refine ⟨15773243888676381157529221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21030991851568508210038961 15773243888676381157529221)
                    ·
                      refine ⟨2957483229126821467036729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15773243888676381157529221 2957483229126821467036729)
                      ·
                        rfl

theorem cell23_5759678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5759678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759678 prefixEnd_5759678 := by exact prefixLift 5759678
  have htrace : WordTrace (prefixWord ++ tailWord_5759678) baseStart_5759678 baseEnd_5759678 := by
    simpa [prefixWord, tailWord_5759678, baseEnd_5759678] using wordTrace_append hprefix tailTrace_5759678
  have hstable : (prefixWord ++ tailWord_5759678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759678).length < 2 ^ (prefixWord ++ tailWord_5759678).sum := by decide
  have hdescent : baseEnd_5759678 < baseStart_5759678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759693 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5759693 : Nat := 118140960795 + 5759693 * 2 ^ 59
def prefixEnd_5759693 : Nat := 4983230072969 + 3 ^ 40 * 5759693 * 2
def baseEnd_5759693 : Nat := 2957490931336638908349161

theorem tailTrace_5759693 : CollatzResearch.WordTrace tailWord_5759693 prefixEnd_5759693 2957490931336638908349161 := by
  unfold tailWord_5759693
  simp only [CollatzResearch.WordTrace]
  refine ⟨210073261922623413094963733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140048841281748942063309155 210073261922623413094963733)
  ·
    refine ⟨9847184152622972488826425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 210073261922623413094963733 9847184152622972488826425)
    ·
      refine ⟨7385388114467229366619819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9847184152622972488826425 7385388114467229366619819)
      ·
        refine ⟨11078082171700844049929729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385388114467229366619819 11078082171700844049929729)
        ·
          refine ⟨8308561628775633037447297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11078082171700844049929729 8308561628775633037447297)
          ·
            refine ⟨6231421221581724778085473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308561628775633037447297 6231421221581724778085473)
            ·
              refine ⟨4673565916186293583564105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231421221581724778085473 4673565916186293583564105)
              ·
                refine ⟨3505174437139720187673079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673565916186293583564105 3505174437139720187673079)
                ·
                  refine ⟨5257761655709580281509619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505174437139720187673079 5257761655709580281509619)
                  ·
                    refine ⟨7886642483564370422264429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257761655709580281509619 7886642483564370422264429)
                    ·
                      refine ⟨2957490931336638908349161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886642483564370422264429 2957490931336638908349161)
                      ·
                        rfl

theorem cell23_5759693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5759693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759693 prefixEnd_5759693 := by exact prefixLift 5759693
  have htrace : WordTrace (prefixWord ++ tailWord_5759693) baseStart_5759693 baseEnd_5759693 := by
    simpa [prefixWord, tailWord_5759693, baseEnd_5759693] using wordTrace_append hprefix tailTrace_5759693
  have hstable : (prefixWord ++ tailWord_5759693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759693).length < 2 ^ (prefixWord ++ tailWord_5759693).sum := by decide
  have hdescent : baseEnd_5759693 < baseStart_5759693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759715 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5759715 : Nat := 118140960795 + 5759715 * 2 ^ 59
def prefixEnd_5759715 : Nat := 4983230072969 + 3 ^ 40 * 5759715 * 2
def baseEnd_5759715 : Nat := 2957502227911037822274059

theorem tailTrace_5759715 : CollatzResearch.WordTrace tailWord_5759715 prefixEnd_5759715 2957502227911037822274059 := by
  unfold tailWord_5759715
  simp only [CollatzResearch.WordTrace]
  refine ⟨210074064328543710852264599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140049376219029140568176399 210074064328543710852264599)
  ·
    refine ⟨315111096492815566278396899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210074064328543710852264599 315111096492815566278396899)
    ·
      refine ⟨472666644739223349417595349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315111096492815566278396899 472666644739223349417595349)
      ·
        refine ⟨11078124486075547251974891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 472666644739223349417595349 11078124486075547251974891)
        ·
          refine ⟨16617186729113320877962337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078124486075547251974891 16617186729113320877962337)
          ·
            refine ⟨12462890046834990658471753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16617186729113320877962337 12462890046834990658471753)
            ·
              refine ⟨9347167535126242993853815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12462890046834990658471753 9347167535126242993853815)
              ·
                refine ⟨14020751302689364490780723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347167535126242993853815 14020751302689364490780723)
                ·
                  refine ⟨21031126954034046736171085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14020751302689364490780723 21031126954034046736171085)
                  ·
                    refine ⟨7886672607762767526064157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21031126954034046736171085 7886672607762767526064157)
                    ·
                      refine ⟨2957502227911037822274059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886672607762767526064157 2957502227911037822274059)
                      ·
                        rfl

theorem cell23_5759715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5759715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759715 prefixEnd_5759715 := by exact prefixLift 5759715
  have htrace : WordTrace (prefixWord ++ tailWord_5759715) baseStart_5759715 baseEnd_5759715 := by
    simpa [prefixWord, tailWord_5759715, baseEnd_5759715] using wordTrace_append hprefix tailTrace_5759715
  have hstable : (prefixWord ++ tailWord_5759715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759715).length < 2 ^ (prefixWord ++ tailWord_5759715).sum := by decide
  have hdescent : baseEnd_5759715 < baseStart_5759715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759725 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5759725 : Nat := 118140960795 + 5759725 * 2 ^ 59
def prefixEnd_5759725 : Nat := 4983230072969 + 3 ^ 40 * 5759725 * 2
def baseEnd_5759725 : Nat := 2957507362717582783149013

theorem tailTrace_5759725 : CollatzResearch.WordTrace tailWord_5759725 prefixEnd_5759725 2957507362717582783149013 := by
  unfold tailWord_5759725
  simp only [CollatzResearch.WordTrace]
  refine ⟨210074429058507482560128629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140049619372338321706752419 210074429058507482560128629)
  ·
    refine ⟨19694477724235076490012059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210074429058507482560128629 19694477724235076490012059)
    ·
      refine ⟨29541716586352614735018089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694477724235076490012059 29541716586352614735018089)
      ·
        refine ⟨22156287439764461051263567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29541716586352614735018089 22156287439764461051263567)
        ·
          refine ⟨33234431159646691576895351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22156287439764461051263567 33234431159646691576895351)
          ·
            refine ⟨49851646739470037365343027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33234431159646691576895351 49851646739470037365343027)
            ·
              refine ⟨74777470109205056048014541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49851646739470037365343027 74777470109205056048014541)
              ·
                refine ⟨28041551290951896018005453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74777470109205056048014541 28041551290951896018005453)
                ·
                  refine ⟨10515581734106961006752045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28041551290951896018005453 10515581734106961006752045)
                  ·
                    refine ⟨3943343150290110377532017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10515581734106961006752045 3943343150290110377532017)
                    ·
                      refine ⟨2957507362717582783149013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943343150290110377532017 2957507362717582783149013)
                      ·
                        rfl

theorem cell23_5759725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5759725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759725 prefixEnd_5759725 := by exact prefixLift 5759725
  have htrace : WordTrace (prefixWord ++ tailWord_5759725) baseStart_5759725 baseEnd_5759725 := by
    simpa [prefixWord, tailWord_5759725, baseEnd_5759725] using wordTrace_append hprefix tailTrace_5759725
  have hstable : (prefixWord ++ tailWord_5759725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759725).length < 2 ^ (prefixWord ++ tailWord_5759725).sum := by decide
  have hdescent : baseEnd_5759725 < baseStart_5759725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759733 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5759733 : Nat := 118140960795 + 5759733 * 2 ^ 59
def prefixEnd_5759733 : Nat := 4983230072969 + 3 ^ 40 * 5759733 * 2
def baseEnd_5759733 : Nat := 2957511470562818751848977

theorem tailTrace_5759733 : CollatzResearch.WordTrace tailWord_5759733 prefixEnd_5759733 2957511470562818751848977 := by
  unfold tailWord_5759733
  simp only [CollatzResearch.WordTrace]
  refine ⟨210074720842478499926419853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140049813894985666617613235 210074720842478499926419853)
  ·
    refine ⟨78778020315929437472407445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210074720842478499926419853 78778020315929437472407445)
    ·
      refine ⟨3692719702309192381519099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78778020315929437472407445 3692719702309192381519099)
      ·
        refine ⟨5539079553463788572278649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692719702309192381519099 5539079553463788572278649)
        ·
          refine ⟨4154309665097841429208987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5539079553463788572278649 4154309665097841429208987)
          ·
            refine ⟨6231464497646762143813481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154309665097841429208987 6231464497646762143813481)
            ·
              refine ⟨4673598373235071607860111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231464497646762143813481 4673598373235071607860111)
              ·
                refine ⟨7010397559852607411790167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673598373235071607860111 7010397559852607411790167)
                ·
                  refine ⟨10515596339778911117685251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7010397559852607411790167 10515596339778911117685251)
                  ·
                    refine ⟨15773394509668366676527877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10515596339778911117685251 15773394509668366676527877)
                    ·
                      refine ⟨2957511470562818751848977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15773394509668366676527877 2957511470562818751848977)
                      ·
                        rfl

theorem cell23_5759733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5759733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759733 prefixEnd_5759733 := by exact prefixLift 5759733
  have htrace : WordTrace (prefixWord ++ tailWord_5759733) baseStart_5759733 baseEnd_5759733 := by
    simpa [prefixWord, tailWord_5759733, baseEnd_5759733] using wordTrace_append hprefix tailTrace_5759733
  have hstable : (prefixWord ++ tailWord_5759733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759733).length < 2 ^ (prefixWord ++ tailWord_5759733).sum := by decide
  have hdescent : baseEnd_5759733 < baseStart_5759733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759741 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_5759741 : Nat := 118140960795 + 5759741 * 2 ^ 59
def prefixEnd_5759741 : Nat := 4983230072969 + 3 ^ 40 * 5759741 * 2
def baseEnd_5759741 : Nat := 2957515578408054720548939

theorem tailTrace_5759741 : CollatzResearch.WordTrace tailWord_5759741 prefixEnd_5759741 2957515578408054720548939 := by
  unfold tailWord_5759741
  simp only [CollatzResearch.WordTrace]
  refine ⟨210075012626449517292711077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140050008417633011528474051 210075012626449517292711077)
  ·
    refine ⟨39389064867459284492383327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210075012626449517292711077 39389064867459284492383327)
    ·
      refine ⟨59083597301188926738574991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39389064867459284492383327 59083597301188926738574991)
      ·
        refine ⟨88625395951783390107862487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59083597301188926738574991 88625395951783390107862487)
        ·
          refine ⟨132938093927675085161793731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88625395951783390107862487 132938093927675085161793731)
          ·
            refine ⟨199407140891512627742690597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132938093927675085161793731 199407140891512627742690597)
            ·
              refine ⟨37388838917158617701754487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199407140891512627742690597 37388838917158617701754487)
              ·
                refine ⟨56083258375737926552631731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37388838917158617701754487 56083258375737926552631731)
                ·
                  refine ⟨84124887563606889828947597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56083258375737926552631731 84124887563606889828947597)
                  ·
                    refine ⟨31546832836352583685855349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84124887563606889828947597 31546832836352583685855349)
                    ·
                      refine ⟨2957515578408054720548939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31546832836352583685855349 2957515578408054720548939)
                      ·
                        rfl

theorem cell23_5759741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_5759741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759741 prefixEnd_5759741 := by exact prefixLift 5759741
  have htrace : WordTrace (prefixWord ++ tailWord_5759741) baseStart_5759741 baseEnd_5759741 := by
    simpa [prefixWord, tailWord_5759741, baseEnd_5759741] using wordTrace_append hprefix tailTrace_5759741
  have hstable : (prefixWord ++ tailWord_5759741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759741).length < 2 ^ (prefixWord ++ tailWord_5759741).sum := by decide
  have hdescent : baseEnd_5759741 < baseStart_5759741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759761 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 7]
def baseStart_5759761 : Nat := 118140960795 + 5759761 * 2 ^ 59
def prefixEnd_5759761 : Nat := 4983230072969 + 3 ^ 40 * 5759761 * 2
def baseEnd_5759761 : Nat := 328613983113460515810983

theorem tailTrace_5759761 : CollatzResearch.WordTrace tailWord_5759761 prefixEnd_5759761 328613983113460515810983 := by
  unfold tailWord_5759761
  simp only [CollatzResearch.WordTrace]
  refine ⟨210075742086377060708439137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140050494724251373805626091 210075742086377060708439137)
  ·
    refine ⟨157556806564782795531329353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210075742086377060708439137 157556806564782795531329353)
    ·
      refine ⟨118167604923587096648497015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157556806564782795531329353 118167604923587096648497015)
      ·
        refine ⟨177251407385380644972745523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118167604923587096648497015 177251407385380644972745523)
        ·
          refine ⟨265877111078070967459118285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177251407385380644972745523 265877111078070967459118285)
          ·
            refine ⟨99703916654276612797169357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265877111078070967459118285 99703916654276612797169357)
            ·
              refine ⟨37388968745353729798938509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99703916654276612797169357 37388968745353729798938509)
              ·
                refine ⟨14020863279507648674601941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37388968745353729798938509 14020863279507648674601941)
                ·
                  refine ⟨328613983113460515810983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14020863279507648674601941 328613983113460515810983)
                  ·
                    rfl

theorem cell23_5759761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 7].length) (baseStart_5759761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759761 prefixEnd_5759761 := by exact prefixLift 5759761
  have htrace : WordTrace (prefixWord ++ tailWord_5759761) baseStart_5759761 baseEnd_5759761 := by
    simpa [prefixWord, tailWord_5759761, baseEnd_5759761] using wordTrace_append hprefix tailTrace_5759761
  have hstable : (prefixWord ++ tailWord_5759761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759761).length < 2 ^ (prefixWord ++ tailWord_5759761).sum := by decide
  have hdescent : baseEnd_5759761 < baseStart_5759761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759772 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_5759772 : Nat := 118140960795 + 5759772 * 2 ^ 59
def prefixEnd_5759772 : Nat := 4983230072969 + 3 ^ 40 * 5759772 * 2
def baseEnd_5759772 : Nat := 2957531496308344099261297

theorem tailTrace_5759772 : CollatzResearch.WordTrace tailWord_5759772 prefixEnd_5759772 2957531496308344099261297 := by
  unfold tailWord_5759772
  simp only [CollatzResearch.WordTrace]
  refine ⟨105038071644668604793544785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140050762192891473058059713 105038071644668604793544785)
  ·
    refine ⟨78778553733501453595158589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105038071644668604793544785 78778553733501453595158589)
    ·
      refine ⟨29541957650063045098184471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78778553733501453595158589 29541957650063045098184471)
      ·
        refine ⟨44312936475094567647276707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29541957650063045098184471 44312936475094567647276707)
        ·
          refine ⟨66469404712641851470915061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44312936475094567647276707 66469404712641851470915061)
          ·
            refine ⟨6231506691810173575398287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66469404712641851470915061 6231506691810173575398287)
            ·
              refine ⟨9347260037715260363097431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6231506691810173575398287 9347260037715260363097431)
              ·
                refine ⟨14020890056572890544646147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347260037715260363097431 14020890056572890544646147)
                ·
                  refine ⟨21031335084859335816969221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14020890056572890544646147 21031335084859335816969221)
                  ·
                    refine ⟨3943375328411125465681729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21031335084859335816969221 3943375328411125465681729)
                    ·
                      refine ⟨2957531496308344099261297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943375328411125465681729 2957531496308344099261297)
                      ·
                        rfl

theorem cell23_5759772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_5759772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759772 prefixEnd_5759772 := by exact prefixLift 5759772
  have htrace : WordTrace (prefixWord ++ tailWord_5759772) baseStart_5759772 baseEnd_5759772 := by
    simpa [prefixWord, tailWord_5759772, baseEnd_5759772] using wordTrace_append hprefix tailTrace_5759772
  have hstable : (prefixWord ++ tailWord_5759772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759772).length < 2 ^ (prefixWord ++ tailWord_5759772).sum := by decide
  have hdescent : baseEnd_5759772 < baseStart_5759772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759778 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_5759778 : Nat := 118140960795 + 5759778 * 2 ^ 59
def prefixEnd_5759778 : Nat := 4983230072969 + 3 ^ 40 * 5759778 * 2
def baseEnd_5759778 : Nat := 328614953021363452865141

theorem tailTrace_5759778 : CollatzResearch.WordTrace tailWord_5759778 prefixEnd_5759778 328614953021363452865141 := by
  unfold tailWord_5759778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52519090531828868152951997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140050908084876981741205325 52519090531828868152951997)
  ·
    refine ⟨19694658949435825557356999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52519090531828868152951997 19694658949435825557356999)
    ·
      refine ⟨29541988424153738336035499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694658949435825557356999 29541988424153738336035499)
      ·
        refine ⟨44312982636230607504053249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29541988424153738336035499 44312982636230607504053249)
        ·
          refine ⟨33234736977172955628039937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44312982636230607504053249 33234736977172955628039937)
          ·
            refine ⟨24926052732879716721029953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33234736977172955628039937 24926052732879716721029953)
            ·
              refine ⟨18694539549659787540772465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24926052732879716721029953 18694539549659787540772465)
              ·
                refine ⟨14020904662244840655579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18694539549659787540772465 14020904662244840655579349)
                ·
                  refine ⟨328614953021363452865141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14020904662244840655579349 328614953021363452865141)
                  ·
                    rfl

theorem cell23_5759778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_5759778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759778 prefixEnd_5759778 := by exact prefixLift 5759778
  have htrace : WordTrace (prefixWord ++ tailWord_5759778) baseStart_5759778 baseEnd_5759778 := by
    simpa [prefixWord, tailWord_5759778, baseEnd_5759778] using wordTrace_append hprefix tailTrace_5759778
  have hstable : (prefixWord ++ tailWord_5759778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759778).length < 2 ^ (prefixWord ++ tailWord_5759778).sum := by decide
  have hdescent : baseEnd_5759778 < baseStart_5759778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759795 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 5]
def baseStart_5759795 : Nat := 118140960795 + 5759795 * 2 ^ 59
def prefixEnd_5759795 : Nat := 4983230072969 + 3 ^ 40 * 5759795 * 2
def baseEnd_5759795 : Nat := 328615922929266389919299

theorem tailTrace_5759795 : CollatzResearch.WordTrace tailWord_5759795 prefixEnd_5759795 328615922929266389919299 := by
  unfold tailWord_5759795
  simp only [CollatzResearch.WordTrace]
  refine ⟨210076982168253884515176839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140051321445502589676784559 210076982168253884515176839)
  ·
    refine ⟨315115473252380826772765259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210076982168253884515176839 315115473252380826772765259)
    ·
      refine ⟨472673209878571240159147889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315115473252380826772765259 472673209878571240159147889)
      ·
        refine ⟨354504907408928430119360917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472673209878571240159147889 354504907408928430119360917)
        ·
          refine ⟨16617417534793520161845043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354504907408928430119360917 16617417534793520161845043)
          ·
            refine ⟨24926126302190280242767565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16617417534793520161845043 24926126302190280242767565)
            ·
              refine ⟨9347297363321355091037837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24926126302190280242767565 9347297363321355091037837)
              ·
                refine ⟨3505236511245508159139189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9347297363321355091037837 3505236511245508159139189)
                ·
                  refine ⟨328615922929266389919299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3505236511245508159139189 328615922929266389919299)
                  ·
                    rfl

theorem cell23_5759795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 5].length) (baseStart_5759795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759795 prefixEnd_5759795 := by exact prefixLift 5759795
  have htrace : WordTrace (prefixWord ++ tailWord_5759795) baseStart_5759795 baseEnd_5759795 := by
    simpa [prefixWord, tailWord_5759795, baseEnd_5759795] using wordTrace_append hprefix tailTrace_5759795
  have hstable : (prefixWord ++ tailWord_5759795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759795).length < 2 ^ (prefixWord ++ tailWord_5759795).sum := by decide
  have hdescent : baseEnd_5759795 < baseStart_5759795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759842 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5759842 : Nat := 118140960795 + 5759842 * 2 ^ 59
def prefixEnd_5759842 : Nat := 4983230072969 + 3 ^ 40 * 5759842 * 2
def baseEnd_5759842 : Nat := 985855813318052941795325

theorem tailTrace_5759842 : CollatzResearch.WordTrace tailWord_5759842 prefixEnd_5759842 985855813318052941795325 := by
  unfold tailWord_5759842
  simp only [CollatzResearch.WordTrace]
  refine ⟨52519674099770902885534445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140052464266055741028091853 52519674099770902885534445)
  ·
    refine ⟨19694877787414088582075417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52519674099770902885534445 19694877787414088582075417)
    ·
      refine ⟨14771158340560566436556563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19694877787414088582075417 14771158340560566436556563)
      ·
        refine ⟨22156737510840849654834845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14771158340560566436556563 22156737510840849654834845)
        ·
          refine ⟨8308776566565318620563067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22156737510840849654834845 8308776566565318620563067)
          ·
            refine ⟨12463164849847977930844601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308776566565318620563067 12463164849847977930844601)
            ·
              refine ⟨9347373637385983448133451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12463164849847977930844601 9347373637385983448133451)
              ·
                refine ⟨14021060456078975172200177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9347373637385983448133451 14021060456078975172200177)
                ·
                  refine ⟨10515795342059231379150133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14021060456078975172200177 10515795342059231379150133)
                  ·
                    refine ⟨985855813318052941795325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515795342059231379150133 985855813318052941795325)
                    ·
                      rfl

theorem cell23_5759842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5759842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759842 prefixEnd_5759842 := by exact prefixLift 5759842
  have htrace : WordTrace (prefixWord ++ tailWord_5759842) baseStart_5759842 baseEnd_5759842 := by
    simpa [prefixWord, tailWord_5759842, baseEnd_5759842] using wordTrace_append hprefix tailTrace_5759842
  have hstable : (prefixWord ++ tailWord_5759842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759842).length < 2 ^ (prefixWord ++ tailWord_5759842).sum := by decide
  have hdescent : baseEnd_5759842 < baseStart_5759842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759851 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 10]
def baseStart_5759851 : Nat := 118140960795 + 5759851 * 2 ^ 59
def prefixEnd_5759851 : Nat := 4983230072969 + 3 ^ 40 * 5759851 * 2
def baseEnd_5759851 : Nat := 328619117920005476685937

theorem tailTrace_5759851 : CollatzResearch.WordTrace tailWord_5759851 prefixEnd_5759851 328619117920005476685937 := by
  unfold tailWord_5759851
  simp only [CollatzResearch.WordTrace]
  refine ⟨210079024656051006079215407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140052683104034004052810271 210079024656051006079215407)
  ·
    refine ⟨315118536984076509118823111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210079024656051006079215407 315118536984076509118823111)
    ·
      refine ⟨472677805476114763678234667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315118536984076509118823111 472677805476114763678234667)
      ·
        refine ⟨709016708214172145517352001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472677805476114763678234667 709016708214172145517352001)
        ·
          refine ⟨531762531160629109138014001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709016708214172145517352001 531762531160629109138014001)
          ·
            refine ⟨398821898370471831853510501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531762531160629109138014001 398821898370471831853510501)
            ·
              refine ⟨74779105944463468472533219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398821898370471831853510501 74779105944463468472533219)
              ·
                refine ⟨112168658916695202708799829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74779105944463468472533219 112168658916695202708799829)
                ·
                  refine ⟨328619117920005476685937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112168658916695202708799829 328619117920005476685937)
                  ·
                    rfl

theorem cell23_5759851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 10].length) (baseStart_5759851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759851 prefixEnd_5759851 := by exact prefixLift 5759851
  have htrace : WordTrace (prefixWord ++ tailWord_5759851) baseStart_5759851 baseEnd_5759851 := by
    simpa [prefixWord, tailWord_5759851, baseEnd_5759851] using wordTrace_append hprefix tailTrace_5759851
  have hstable : (prefixWord ++ tailWord_5759851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759851).length < 2 ^ (prefixWord ++ tailWord_5759851).sum := by decide
  have hdescent : baseEnd_5759851 < baseStart_5759851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759862 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5759862 : Nat := 118140960795 + 5759862 * 2 ^ 59
def prefixEnd_5759862 : Nat := 4983230072969 + 3 ^ 40 * 5759862 * 2
def baseEnd_5759862 : Nat := 2957577709567248747135883

theorem tailTrace_5759862 : CollatzResearch.WordTrace tailWord_5759862 prefixEnd_5759862 2957577709567248747135883 := by
  unfold tailWord_5759862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129964116188197184866615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140052950572674103305243893 13129964116188197184866615)
  ·
    refine ⟨19694946174282295777299923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13129964116188197184866615 19694946174282295777299923)
    ·
      refine ⟨29542419261423443665949885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694946174282295777299923 29542419261423443665949885)
      ·
        refine ⟨11078407223033791374731207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29542419261423443665949885 11078407223033791374731207)
        ·
          refine ⟨16617610834550687062096811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078407223033791374731207 16617610834550687062096811)
          ·
            refine ⟨24926416251826030593145217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16617610834550687062096811 24926416251826030593145217)
            ·
              refine ⟨18694812188869522944858913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24926416251826030593145217 18694812188869522944858913)
              ·
                refine ⟨14021109141652142208644185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18694812188869522944858913 14021109141652142208644185)
                ·
                  refine ⟨10515831856239106656483139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14021109141652142208644185 10515831856239106656483139)
                  ·
                    refine ⟨15773747784358659984724709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10515831856239106656483139 15773747784358659984724709)
                    ·
                      refine ⟨2957577709567248747135883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15773747784358659984724709 2957577709567248747135883)
                      ·
                        rfl

theorem cell23_5759862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5759862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759862 prefixEnd_5759862 := by exact prefixLift 5759862
  have htrace : WordTrace (prefixWord ++ tailWord_5759862) baseStart_5759862 baseEnd_5759862 := by
    simpa [prefixWord, tailWord_5759862, baseEnd_5759862] using wordTrace_append hprefix tailTrace_5759862
  have hstable : (prefixWord ++ tailWord_5759862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759862).length < 2 ^ (prefixWord ++ tailWord_5759862).sum := by decide
  have hdescent : baseEnd_5759862 < baseStart_5759862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759865 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_5759865 : Nat := 118140960795 + 5759865 * 2 ^ 59
def prefixEnd_5759865 : Nat := 4983230072969 + 3 ^ 40 * 5759865 * 2
def baseEnd_5759865 : Nat := 2957579250009212235398369

theorem tailTrace_5759865 : CollatzResearch.WordTrace tailWord_5759865 prefixEnd_5759865 2957579250009212235398369 := by
  unfold tailWord_5759865
  simp only [CollatzResearch.WordTrace]
  refine ⟨210079535278000286470225049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140053023518666857646816699 210079535278000286470225049)
  ·
    refine ⟨157559651458500214852668787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210079535278000286470225049 157559651458500214852668787)
    ·
      refine ⟨236339477187750322279003181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157559651458500214852668787 236339477187750322279003181)
      ·
        refine ⟨88627303945406370854626193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236339477187750322279003181 88627303945406370854626193)
        ·
          refine ⟨66470477959054778140969645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88627303945406370854626193 66470477959054778140969645)
          ·
            refine ⟨24926429234645541802863617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66470477959054778140969645 24926429234645541802863617)
            ·
              refine ⟨18694821925984156352147713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24926429234645541802863617 18694821925984156352147713)
              ·
                refine ⟨14021116444488117264110785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18694821925984156352147713 14021116444488117264110785)
                ·
                  refine ⟨10515837333366087948083089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14021116444488117264110785 10515837333366087948083089)
                  ·
                    refine ⟨7886878000024565961062317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10515837333366087948083089 7886878000024565961062317)
                    ·
                      refine ⟨2957579250009212235398369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886878000024565961062317 2957579250009212235398369)
                      ·
                        rfl

theorem cell23_5759865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_5759865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759865 prefixEnd_5759865 := by exact prefixLift 5759865
  have htrace : WordTrace (prefixWord ++ tailWord_5759865) baseStart_5759865 baseEnd_5759865 := by
    simpa [prefixWord, tailWord_5759865, baseEnd_5759865] using wordTrace_append hprefix tailTrace_5759865
  have hstable : (prefixWord ++ tailWord_5759865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759865).length < 2 ^ (prefixWord ++ tailWord_5759865).sum := by decide
  have hdescent : baseEnd_5759865 < baseStart_5759865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759929 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5759929 : Nat := 118140960795 + 5759929 * 2 ^ 59
def prefixEnd_5759929 : Nat := 4983230072969 + 3 ^ 40 * 5759929 * 2
def baseEnd_5759929 : Nat := 2957612112771099984998075

theorem tailTrace_5759929 : CollatzResearch.WordTrace tailWord_5759929 prefixEnd_5759929 2957612112771099984998075 := by
  unfold tailWord_5759929
  simp only [CollatzResearch.WordTrace]
  refine ⟨210081869549768425400554841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140054579699845616933703227 210081869549768425400554841)
  ·
    refine ⟨157561402162326319050416131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210081869549768425400554841 157561402162326319050416131)
    ·
      refine ⟨236342103243489478575624197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157561402162326319050416131 236342103243489478575624197)
      ·
        refine ⟨44314144358154277232929537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236342103243489478575624197 44314144358154277232929537)
        ·
          refine ⟨33235608268615707924697153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44314144358154277232929537 33235608268615707924697153)
          ·
            refine ⟨24926706201461780943522865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33235608268615707924697153 24926706201461780943522865)
            ·
              refine ⟨18695029651096335707642149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24926706201461780943522865 18695029651096335707642149)
              ·
                refine ⟨3505318059580562945182903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18695029651096335707642149 3505318059580562945182903)
                ·
                  refine ⟨5257977089370844417774355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505318059580562945182903 5257977089370844417774355)
                  ·
                    refine ⟨7886965634056266626661533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5257977089370844417774355 7886965634056266626661533)
                    ·
                      refine ⟨2957612112771099984998075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7886965634056266626661533 2957612112771099984998075)
                      ·
                        rfl

theorem cell23_5759929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5759929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759929 prefixEnd_5759929 := by exact prefixLift 5759929
  have htrace : WordTrace (prefixWord ++ tailWord_5759929) baseStart_5759929 baseEnd_5759929 := by
    simpa [prefixWord, tailWord_5759929, baseEnd_5759929] using wordTrace_append hprefix tailTrace_5759929
  have hstable : (prefixWord ++ tailWord_5759929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759929).length < 2 ^ (prefixWord ++ tailWord_5759929).sum := by decide
  have hdescent : baseEnd_5759929 < baseStart_5759929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759975 : List Nat := [1, 1, 5, 2, 2, 3, 9]
def baseStart_5759975 : Nat := 118140960795 + 5759975 * 2 ^ 59
def prefixEnd_5759975 : Nat := 4983230072969 + 3 ^ 40 * 5759975 * 2
def baseEnd_5759975 : Nat := 36514021393595145741023

theorem tailTrace_5759975 : CollatzResearch.WordTrace tailWord_5759975 prefixEnd_5759975 36514021393595145741023 := by
  unfold tailWord_5759975
  simp only [CollatzResearch.WordTrace]
  refine ⟨210083547307601775256729379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140055698205067850171152919 210083547307601775256729379)
  ·
    refine ⟨315125320961402662885094069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210083547307601775256729379 315125320961402662885094069)
    ·
      refine ⟨29542998840131499645477569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315125320961402662885094069 29542998840131499645477569)
      ·
        refine ⟨22157249130098624734108177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29542998840131499645477569 22157249130098624734108177)
        ·
          refine ⟨16617936847573968550581133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22157249130098624734108177 16617936847573968550581133)
          ·
            refine ⟨6231726317840238206467925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16617936847573968550581133 6231726317840238206467925)
            ·
              refine ⟨36514021393595145741023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6231726317840238206467925 36514021393595145741023)
              ·
                rfl

theorem cell23_5759975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 9].length) (baseStart_5759975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759975 prefixEnd_5759975 := by exact prefixLift 5759975
  have htrace : WordTrace (prefixWord ++ tailWord_5759975) baseStart_5759975 baseEnd_5759975 := by
    simpa [prefixWord, tailWord_5759975, baseEnd_5759975] using wordTrace_append hprefix tailTrace_5759975
  have hstable : (prefixWord ++ tailWord_5759975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759975).length < 2 ^ (prefixWord ++ tailWord_5759975).sum := by decide
  have hdescent : baseEnd_5759975 < baseStart_5759975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5759995 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 7, 2]
def baseStart_5759995 : Nat := 118140960795 + 5759995 * 2 ^ 59
def prefixEnd_5759995 : Nat := 4983230072969 + 3 ^ 40 * 5759995 * 2
def baseEnd_5759995 : Nat := 2957646002494296726772771

theorem tailTrace_5759995 : CollatzResearch.WordTrace tailWord_5759995 prefixEnd_5759995 2957646002494296726772771 := by
  unfold tailWord_5759995
  simp only [CollatzResearch.WordTrace]
  refine ⟨210084276767529318672457439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140056184511686212448304959 210084276767529318672457439)
  ·
    refine ⟨315126415151293978008686159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210084276767529318672457439 315126415151293978008686159)
    ·
      refine ⟨472689622726940967013029239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315126415151293978008686159 472689622726940967013029239)
      ·
        refine ⟨709034434090411450519543859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472689622726940967013029239 709034434090411450519543859)
        ·
          refine ⟨1063551651135617175779315789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709034434090411450519543859 1063551651135617175779315789)
          ·
            refine ⟨398831869175856440917243421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1063551651135617175779315789 398831869175856440917243421)
            ·
              refine ⟨149561950940946165343966283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398831869175856440917243421 149561950940946165343966283)
              ·
                refine ⟨224342926411419248015949425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149561950940946165343966283 224342926411419248015949425)
                ·
                  refine ⟨168257194808564436011962069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224342926411419248015949425 168257194808564436011962069)
                  ·
                    refine ⟨3943528003325728969030361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168257194808564436011962069 3943528003325728969030361)
                    ·
                      refine ⟨2957646002494296726772771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943528003325728969030361 2957646002494296726772771)
                      ·
                        rfl

theorem cell23_5759995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7, 2].length) (baseStart_5759995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5759995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5759995 prefixEnd_5759995 := by exact prefixLift 5759995
  have htrace : WordTrace (prefixWord ++ tailWord_5759995) baseStart_5759995 baseEnd_5759995 := by
    simpa [prefixWord, tailWord_5759995, baseEnd_5759995] using wordTrace_append hprefix tailTrace_5759995
  have hstable : (prefixWord ++ tailWord_5759995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5759995).length < 2 ^ (prefixWord ++ tailWord_5759995).sum := by decide
  have hdescent : baseEnd_5759995 < baseStart_5759995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5759995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760036 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5760036 : Nat := 118140960795 + 5760036 * 2 ^ 59
def prefixEnd_5760036 : Nat := 4983230072969 + 3 ^ 40 * 5760036 * 2
def baseEnd_5760036 : Nat := 2957667055201131066360083

theorem tailTrace_5760036 : CollatzResearch.WordTrace tailWord_5760036 prefixEnd_5760036 2957667055201131066360083 := by
  unfold tailWord_5760036
  simp only [CollatzResearch.WordTrace]
  refine ⟨105042886080190391337349981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140057181440253855116466641 105042886080190391337349981)
  ·
    refine ⟨39391082280071396751506243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105042886080190391337349981 39391082280071396751506243)
    ·
      refine ⟨59086623420107095127259365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391082280071396751506243 59086623420107095127259365)
      ·
        refine ⟨11078741891270080336361131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59086623420107095127259365 11078741891270080336361131)
        ·
          refine ⟨16618112836905120504541697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078741891270080336361131 16618112836905120504541697)
          ·
            refine ⟨12463584627678840378406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16618112836905120504541697 12463584627678840378406273)
            ·
              refine ⟨9347688470759130283804705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12463584627678840378406273 9347688470759130283804705)
              ·
                refine ⟨7010766353069347712853529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9347688470759130283804705 7010766353069347712853529)
                ·
                  refine ⟨5258074764802010784640147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7010766353069347712853529 5258074764802010784640147)
                  ·
                    refine ⟨7887112147203016176960221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258074764802010784640147 7887112147203016176960221)
                    ·
                      refine ⟨2957667055201131066360083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887112147203016176960221 2957667055201131066360083)
                      ·
                        rfl

theorem cell23_5760036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5760036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760036 prefixEnd_5760036 := by exact prefixLift 5760036
  have htrace : WordTrace (prefixWord ++ tailWord_5760036) baseStart_5760036 baseEnd_5760036 := by
    simpa [prefixWord, tailWord_5760036, baseEnd_5760036] using wordTrace_append hprefix tailTrace_5760036
  have hstable : (prefixWord ++ tailWord_5760036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760036).length < 2 ^ (prefixWord ++ tailWord_5760036).sum := by decide
  have hdescent : baseEnd_5760036 < baseStart_5760036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760052 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_5760052 : Nat := 118140960795 + 5760052 * 2 ^ 59
def prefixEnd_5760052 : Nat := 4983230072969 + 3 ^ 40 * 5760052 * 2
def baseEnd_5760052 : Nat := 985891756963867667920003

theorem tailTrace_5760052 : CollatzResearch.WordTrace tailWord_5760052 prefixEnd_5760052 985891756963867667920003 := by
  unfold tailWord_5760052
  simp only [CollatzResearch.WordTrace]
  refine ⟨105043177864161408703641205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140057570485548544938188273 105043177864161408703641205)
  ·
    refine ⟨9847797924765132065966363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105043177864161408703641205 9847797924765132065966363)
    ·
      refine ⟨14771696887147698098949545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9847797924765132065966363 14771696887147698098949545)
      ·
        refine ⟨11078772665360773574212159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14771696887147698098949545 11078772665360773574212159)
        ·
          refine ⟨16618158998041160361318239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11078772665360773574212159 16618158998041160361318239)
          ·
            refine ⟨24927238497061740541977359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16618158998041160361318239 24927238497061740541977359)
            ·
              refine ⟨37390857745592610812966039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24927238497061740541977359 37390857745592610812966039)
              ·
                refine ⟨56086286618388916219449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37390857745592610812966039 56086286618388916219449059)
                ·
                  refine ⟨84129429927583374329173589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56086286618388916219449059 84129429927583374329173589)
                  ·
                    refine ⟨985891756963867667920003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84129429927583374329173589 985891756963867667920003)
                    ·
                      rfl

theorem cell23_5760052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_5760052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760052 prefixEnd_5760052 := by exact prefixLift 5760052
  have htrace : WordTrace (prefixWord ++ tailWord_5760052) baseStart_5760052 baseEnd_5760052 := by
    simpa [prefixWord, tailWord_5760052, baseEnd_5760052] using wordTrace_append hprefix tailTrace_5760052
  have hstable : (prefixWord ++ tailWord_5760052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760052).length < 2 ^ (prefixWord ++ tailWord_5760052).sum := by decide
  have hdescent : baseEnd_5760052 < baseStart_5760052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760075 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3]
def baseStart_5760075 : Nat := 118140960795 + 5760075 * 2 ^ 59
def prefixEnd_5760075 : Nat := 4983230072969 + 3 ^ 40 * 5760075 * 2
def baseEnd_5760075 : Nat := 2957687080946656413772403

theorem tailTrace_5760075 : CollatzResearch.WordTrace tailWord_5760075 prefixEnd_5760075 2957687080946656413772403 := by
  unfold tailWord_5760075
  simp only [CollatzResearch.WordTrace]
  refine ⟨210087194607239492335369679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140058129738159661556913119 210087194607239492335369679)
  ·
    refine ⟨315130791910859238503054519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210087194607239492335369679 315130791910859238503054519)
    ·
      refine ⟨472696187866288857754581779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315130791910859238503054519 472696187866288857754581779)
      ·
        refine ⟨709044281799433286631872669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472696187866288857754581779 709044281799433286631872669)
        ·
          refine ⟨265891605674787482486952251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709044281799433286631872669 265891605674787482486952251)
          ·
            refine ⟨398837408512181223730428377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265891605674787482486952251 398837408512181223730428377)
            ·
              refine ⟨299128056384135917797821283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398837408512181223730428377 299128056384135917797821283)
              ·
                refine ⟨448692084576203876696731925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299128056384135917797821283 448692084576203876696731925)
                ·
                  refine ⟨21032441464509556720159309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 448692084576203876696731925 21032441464509556720159309)
                  ·
                    refine ⟨7887165549191083770059741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21032441464509556720159309 7887165549191083770059741)
                    ·
                      refine ⟨2957687080946656413772403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887165549191083770059741 2957687080946656413772403)
                      ·
                        rfl

theorem cell23_5760075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 3].length) (baseStart_5760075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760075 prefixEnd_5760075 := by exact prefixLift 5760075
  have htrace : WordTrace (prefixWord ++ tailWord_5760075) baseStart_5760075 baseEnd_5760075 := by
    simpa [prefixWord, tailWord_5760075, baseEnd_5760075] using wordTrace_append hprefix tailTrace_5760075
  have hstable : (prefixWord ++ tailWord_5760075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760075).length < 2 ^ (prefixWord ++ tailWord_5760075).sum := by decide
  have hdescent : baseEnd_5760075 < baseStart_5760075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760092 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5760092 : Nat := 118140960795 + 5760092 * 2 ^ 59
def prefixEnd_5760092 : Nat := 4983230072969 + 3 ^ 40 * 5760092 * 2
def baseEnd_5760092 : Nat := 2957695810117782847259825

theorem tailTrace_5760092 : CollatzResearch.WordTrace tailWord_5760092 prefixEnd_5760092 2957695810117782847259825 := by
  unfold tailWord_5760092
  simp only [CollatzResearch.WordTrace]
  refine ⟨105043907324088952119369265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140058543098785269492492353 105043907324088952119369265)
  ·
    refine ⟨78782930493066714089526949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105043907324088952119369265 78782930493066714089526949)
    ·
      refine ⟨14771799467450008891786303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78782930493066714089526949 14771799467450008891786303)
      ·
        refine ⟨22157699201175013337679455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14771799467450008891786303 22157699201175013337679455)
        ·
          refine ⟨33236548801762520006519183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22157699201175013337679455 33236548801762520006519183)
          ·
            refine ⟨49854823202643780009778775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33236548801762520006519183 49854823202643780009778775)
            ·
              refine ⟨74782234803965670014668163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49854823202643780009778775 74782234803965670014668163)
              ·
                refine ⟨112173352205948505022002245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74782234803965670014668163 112173352205948505022002245)
                ·
                  refine ⟨21032503538615344691625421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112173352205948505022002245 21032503538615344691625421)
                  ·
                    refine ⟨7887188826980754259359533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21032503538615344691625421 7887188826980754259359533)
                    ·
                      refine ⟨2957695810117782847259825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887188826980754259359533 2957695810117782847259825)
                      ·
                        rfl

theorem cell23_5760092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5760092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760092 prefixEnd_5760092 := by exact prefixLift 5760092
  have htrace : WordTrace (prefixWord ++ tailWord_5760092) baseStart_5760092 baseEnd_5760092 := by
    simpa [prefixWord, tailWord_5760092, baseEnd_5760092] using wordTrace_append hprefix tailTrace_5760092
  have hstable : (prefixWord ++ tailWord_5760092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760092).length < 2 ^ (prefixWord ++ tailWord_5760092).sum := by decide
  have hdescent : baseEnd_5760092 < baseStart_5760092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760093 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5760093 : Nat := 118140960795 + 5760093 * 2 ^ 59
def prefixEnd_5760093 : Nat := 4983230072969 + 3 ^ 40 * 5760093 * 2
def baseEnd_5760093 : Nat := 2957696323598437343347321

theorem tailTrace_5760093 : CollatzResearch.WordTrace tailWord_5760093 prefixEnd_5760093 2957696323598437343347321 := by
  unfold tailWord_5760093
  simp only [CollatzResearch.WordTrace]
  refine ⟨210087851121174281409524933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140058567414116187606349955 210087851121174281409524933)
  ·
    refine ⟨39391472085220177764285925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210087851121174281409524933 39391472085220177764285925)
    ·
      refine ⟨7385901015978783330803611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39391472085220177764285925 7385901015978783330803611)
      ·
        refine ⟨11078851523968174996205417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385901015978783330803611 11078851523968174996205417)
        ·
          refine ⟨8309138642976131247154063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11078851523968174996205417 8309138642976131247154063)
          ·
            refine ⟨12463707964464196870731095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309138642976131247154063 12463707964464196870731095)
            ·
              refine ⟨18695561946696295306096643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12463707964464196870731095 18695561946696295306096643)
              ·
                refine ⟨28043342920044442959144965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18695561946696295306096643 28043342920044442959144965)
                ·
                  refine ⟨5258126797508333054839681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28043342920044442959144965 5258126797508333054839681)
                  ·
                    refine ⟨3943595098131249791129761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258126797508333054839681 3943595098131249791129761)
                    ·
                      refine ⟨2957696323598437343347321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943595098131249791129761 2957696323598437343347321)
                      ·
                        rfl

theorem cell23_5760093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5760093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760093 prefixEnd_5760093 := by exact prefixLift 5760093
  have htrace : WordTrace (prefixWord ++ tailWord_5760093) baseStart_5760093 baseEnd_5760093 := by
    simpa [prefixWord, tailWord_5760093, baseEnd_5760093] using wordTrace_append hprefix tailTrace_5760093
  have hstable : (prefixWord ++ tailWord_5760093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760093).length < 2 ^ (prefixWord ++ tailWord_5760093).sum := by decide
  have hdescent : baseEnd_5760093 < baseStart_5760093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760095 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 4, 5]
def baseStart_5760095 : Nat := 118140960795 + 5760095 * 2 ^ 59
def prefixEnd_5760095 : Nat := 4983230072969 + 3 ^ 40 * 5760095 * 2
def baseEnd_5760095 : Nat := 985899116853248778507437

theorem tailTrace_5760095 : CollatzResearch.WordTrace tailWord_5760095 prefixEnd_5760095 985899116853248778507437 := by
  unfold tailWord_5760095
  simp only [CollatzResearch.WordTrace]
  refine ⟨210087924067167035751097739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140058616044778023834065159 210087924067167035751097739)
  ·
    refine ⟨315131886100750553626646609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210087924067167035751097739 315131886100750553626646609)
    ·
      refine ⟨236348914575562915219984957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315131886100750553626646609 236348914575562915219984957)
      ·
        refine ⟨88630842965836093207494359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236348914575562915219984957 88630842965836093207494359)
        ·
          refine ⟨132946264448754139811241539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88630842965836093207494359 132946264448754139811241539)
          ·
            refine ⟨199419396673131209716862309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132946264448754139811241539 199419396673131209716862309)
            ·
              refine ⟨37391136876212101821911683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199419396673131209716862309 37391136876212101821911683)
              ·
                refine ⟨56086705314318152732867525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37391136876212101821911683 56086705314318152732867525)
                ·
                  refine ⟨10516257246434653637412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56086705314318152732867525 10516257246434653637412661)
                  ·
                    refine ⟨985899116853248778507437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10516257246434653637412661 985899116853248778507437)
                    ·
                      rfl

theorem cell23_5760095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 5].length) (baseStart_5760095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760095 prefixEnd_5760095 := by exact prefixLift 5760095
  have htrace : WordTrace (prefixWord ++ tailWord_5760095) baseStart_5760095 baseEnd_5760095 := by
    simpa [prefixWord, tailWord_5760095, baseEnd_5760095] using wordTrace_append hprefix tailTrace_5760095
  have hstable : (prefixWord ++ tailWord_5760095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760095).length < 2 ^ (prefixWord ++ tailWord_5760095).sum := by decide
  have hdescent : baseEnd_5760095 < baseStart_5760095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760125 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_5760125 : Nat := 118140960795 + 5760125 * 2 ^ 59
def prefixEnd_5760125 : Nat := 4983230072969 + 3 ^ 40 * 5760125 * 2
def baseEnd_5760125 : Nat := 985904251659793739382391

theorem tailTrace_5760125 : CollatzResearch.WordTrace tailWord_5760125 prefixEnd_5760125 985904251659793739382391 := by
  unfold tailWord_5760125
  simp only [CollatzResearch.WordTrace]
  refine ⟨210089018257058350874689829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140059345504705567249793219 210089018257058350874689829)
  ·
    refine ⟨39391690923198440789004343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210089018257058350874689829 39391690923198440789004343)
    ·
      refine ⟨59087536384797661183506515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391690923198440789004343 59087536384797661183506515)
      ·
        refine ⟨88631304577196491775259773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59087536384797661183506515 88631304577196491775259773)
        ·
          refine ⟨33236739216448684415722415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88631304577196491775259773 33236739216448684415722415)
          ·
            refine ⟨49855108824673026623583623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33236739216448684415722415 49855108824673026623583623)
            ·
              refine ⟨74782663237009539935375435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49855108824673026623583623 74782663237009539935375435)
              ·
                refine ⟨112173994855514309903063153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74782663237009539935375435 112173994855514309903063153)
                ·
                  refine ⟨84130496141635732427297365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112173994855514309903063153 84130496141635732427297365)
                  ·
                    refine ⟨985904251659793739382391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84130496141635732427297365 985904251659793739382391)
                    ·
                      rfl

theorem cell23_5760125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_5760125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760125 prefixEnd_5760125 := by exact prefixLift 5760125
  have htrace : WordTrace (prefixWord ++ tailWord_5760125) baseStart_5760125 baseEnd_5760125 := by
    simpa [prefixWord, tailWord_5760125, baseEnd_5760125] using wordTrace_append hprefix tailTrace_5760125
  have hstable : (prefixWord ++ tailWord_5760125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760125).length < 2 ^ (prefixWord ++ tailWord_5760125).sum := by decide
  have hdescent : baseEnd_5760125 < baseStart_5760125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760132 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5760132 : Nat := 118140960795 + 5760132 * 2 ^ 59
def prefixEnd_5760132 : Nat := 4983230072969 + 3 ^ 40 * 5760132 * 2
def baseEnd_5760132 : Nat := 2957716349343962690759641

theorem tailTrace_5760132 : CollatzResearch.WordTrace tailWord_5760132 prefixEnd_5760132 2957716349343962690759641 := by
  unfold tailWord_5760132
  simp only [CollatzResearch.WordTrace]
  refine ⟨105044636784016495535097325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140059515712021994046796433 105044636784016495535097325)
  ·
    refine ⟨39391738794006185825661497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105044636784016495535097325 39391738794006185825661497)
    ·
      refine ⟨29543804095504639369246123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39391738794006185825661497 29543804095504639369246123)
      ·
        refine ⟨44315706143256959053869185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29543804095504639369246123 44315706143256959053869185)
        ·
          refine ⟨33236779607442719290401889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44315706143256959053869185 33236779607442719290401889)
          ·
            refine ⟨24927584705582039467801417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33236779607442719290401889 24927584705582039467801417)
            ·
              refine ⟨18695688529186529600851063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24927584705582039467801417 18695688529186529600851063)
              ·
                refine ⟨28043532793779794401276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18695688529186529600851063 28043532793779794401276595)
                ·
                  refine ⟨42065299190669691601914893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28043532793779794401276595 42065299190669691601914893)
                  ·
                    refine ⟨15774487196501134350718085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42065299190669691601914893 15774487196501134350718085)
                    ·
                      refine ⟨2957716349343962690759641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15774487196501134350718085 2957716349343962690759641)
                      ·
                        rfl

theorem cell23_5760132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5760132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760132 prefixEnd_5760132 := by exact prefixLift 5760132
  have htrace : WordTrace (prefixWord ++ tailWord_5760132) baseStart_5760132 baseEnd_5760132 := by
    simpa [prefixWord, tailWord_5760132, baseEnd_5760132] using wordTrace_append hprefix tailTrace_5760132
  have hstable : (prefixWord ++ tailWord_5760132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760132).length < 2 ^ (prefixWord ++ tailWord_5760132).sum := by decide
  have hdescent : baseEnd_5760132 < baseStart_5760132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760135 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5760135 : Nat := 118140960795 + 5760135 * 2 ^ 59
def prefixEnd_5760135 : Nat := 4983230072969 + 3 ^ 40 * 5760135 * 2
def baseEnd_5760135 : Nat := 2957717889785926179022127

theorem tailTrace_5760135 : CollatzResearch.WordTrace tailWord_5760135 prefixEnd_5760135 2957717889785926179022127 := by
  unfold tailWord_5760135
  simp only [CollatzResearch.WordTrace]
  refine ⟨210089382987022122582553859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140059588658014748388369239 210089382987022122582553859)
  ·
    refine ⟨315134074480533183873830789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210089382987022122582553859 315134074480533183873830789)
    ·
      refine ⟨59087638965099971976343273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315134074480533183873830789 59087638965099971976343273)
      ·
        refine ⟨44315729223824978982257455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59087638965099971976343273 44315729223824978982257455)
        ·
          refine ⟨66473593835737468473386183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44315729223824978982257455 66473593835737468473386183)
          ·
            refine ⟨99710390753606202710079275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66473593835737468473386183 99710390753606202710079275)
            ·
              refine ⟨149565586130409304065118913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99710390753606202710079275 149565586130409304065118913)
              ·
                refine ⟨112174189597806978048839185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149565586130409304065118913 112174189597806978048839185)
                ·
                  refine ⟨84130642198355233536629389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112174189597806978048839185 84130642198355233536629389)
                  ·
                    refine ⟨31548990824383212576236021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84130642198355233536629389 31548990824383212576236021)
                    ·
                      refine ⟨2957717889785926179022127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31548990824383212576236021 2957717889785926179022127)
                      ·
                        rfl

theorem cell23_5760135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5760135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760135 prefixEnd_5760135 := by exact prefixLift 5760135
  have htrace : WordTrace (prefixWord ++ tailWord_5760135) baseStart_5760135 baseEnd_5760135 := by
    simpa [prefixWord, tailWord_5760135, baseEnd_5760135] using wordTrace_append hprefix tailTrace_5760135
  have hstable : (prefixWord ++ tailWord_5760135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760135).length < 2 ^ (prefixWord ++ tailWord_5760135).sum := by decide
  have hdescent : baseEnd_5760135 < baseStart_5760135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760175 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_5760175 : Nat := 118140960795 + 5760175 * 2 ^ 59
def prefixEnd_5760175 : Nat := 4983230072969 + 3 ^ 40 * 5760175 * 2
def baseEnd_5760175 : Nat := 2957738429012106022521943

theorem tailTrace_5760175 : CollatzResearch.WordTrace tailWord_5760175 prefixEnd_5760175 2957738429012106022521943 := by
  unfold tailWord_5760175
  simp only [CollatzResearch.WordTrace]
  refine ⟨210090841906877209414009979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140060561271251472942673319 210090841906877209414009979)
  ·
    refine ⟨315136262860315814121014969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210090841906877209414009979 315136262860315814121014969)
    ·
      refine ⟨236352197145236860590761227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315136262860315814121014969 236352197145236860590761227)
      ·
        refine ⟨354528295717855290886141841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236352197145236860590761227 354528295717855290886141841)
        ·
          refine ⟨265896221788391468164606381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354528295717855290886141841 265896221788391468164606381)
          ·
            refine ⟨99711083170646800561727393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265896221788391468164606381 99711083170646800561727393)
            ·
              refine ⟨74783312377985100421295545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99711083170646800561727393 74783312377985100421295545)
              ·
                refine ⟨56087484283488825315971659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74783312377985100421295545 56087484283488825315971659)
                ·
                  refine ⟨84131226425233237973957489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56087484283488825315971659 84131226425233237973957489)
                  ·
                    refine ⟨63098419818924928480468117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84131226425233237973957489 63098419818924928480468117)
                    ·
                      refine ⟨2957738429012106022521943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63098419818924928480468117 2957738429012106022521943)
                      ·
                        rfl

theorem cell23_5760175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_5760175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760175 prefixEnd_5760175 := by exact prefixLift 5760175
  have htrace : WordTrace (prefixWord ++ tailWord_5760175) baseStart_5760175 baseEnd_5760175 := by
    simpa [prefixWord, tailWord_5760175, baseEnd_5760175] using wordTrace_append hprefix tailTrace_5760175
  have hstable : (prefixWord ++ tailWord_5760175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760175).length < 2 ^ (prefixWord ++ tailWord_5760175).sum := by decide
  have hdescent : baseEnd_5760175 < baseStart_5760175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760195 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_5760195 : Nat := 118140960795 + 5760195 * 2 ^ 59
def prefixEnd_5760195 : Nat := 4983230072969 + 3 ^ 40 * 5760195 * 2
def baseEnd_5760195 : Nat := 2957748698625195944271851

theorem tailTrace_5760195 : CollatzResearch.WordTrace tailWord_5760195 prefixEnd_5760195 2957748698625195944271851 := by
  unfold tailWord_5760195
  simp only [CollatzResearch.WordTrace]
  refine ⟨210091571366804752829738039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140061047577869835219825359 210091571366804752829738039)
  ·
    refine ⟨315137357050207129244607059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210091571366804752829738039 315137357050207129244607059)
    ·
      refine ⟨472706035575310693866910589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315137357050207129244607059 472706035575310693866910589)
      ·
        refine ⟨177264763340741510200091471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472706035575310693866910589 177264763340741510200091471)
        ·
          refine ⟨265897145011112265300137207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177264763340741510200091471 265897145011112265300137207)
          ·
            refine ⟨398845717516668397950205811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265897145011112265300137207 398845717516668397950205811)
            ·
              refine ⟨598268576275002596925308717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398845717516668397950205811 598268576275002596925308717)
              ·
                refine ⟨224350716103125973846990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598268576275002596925308717 224350716103125973846990769)
                ·
                  refine ⟨168263037077344480385243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224350716103125973846990769 168263037077344480385243077)
                  ·
                    refine ⟨31549319452002090072233077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168263037077344480385243077 31549319452002090072233077)
                    ·
                      refine ⟨2957748698625195944271851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31549319452002090072233077 2957748698625195944271851)
                      ·
                        rfl

theorem cell23_5760195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_5760195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760195 prefixEnd_5760195 := by exact prefixLift 5760195
  have htrace : WordTrace (prefixWord ++ tailWord_5760195) baseStart_5760195 baseEnd_5760195 := by
    simpa [prefixWord, tailWord_5760195, baseEnd_5760195] using wordTrace_append hprefix tailTrace_5760195
  have hstable : (prefixWord ++ tailWord_5760195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760195).length < 2 ^ (prefixWord ++ tailWord_5760195).sum := by decide
  have hdescent : baseEnd_5760195 < baseStart_5760195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760273 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_5760273 : Nat := 118140960795 + 5760273 * 2 ^ 59
def prefixEnd_5760273 : Nat := 4983230072969 + 3 ^ 40 * 5760273 * 2
def baseEnd_5760273 : Nat := 2957788750116246639096493

theorem tailTrace_5760273 : CollatzResearch.WordTrace tailWord_5760273 prefixEnd_5760273 2957788750116246639096493 := by
  unfold tailWord_5760273
  simp only [CollatzResearch.WordTrace]
  refine ⟨210094416260522172151077473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140062944173681448100718315 210094416260522172151077473)
  ·
    refine ⟨157570812195391629113308105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210094416260522172151077473 157570812195391629113308105)
    ·
      refine ⟨118178109146543721834981079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157570812195391629113308105 118178109146543721834981079)
      ·
        refine ⟨177267163719815582752471619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118178109146543721834981079 177267163719815582752471619)
        ·
          refine ⟨265900745579723374128707429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177267163719815582752471619 265900745579723374128707429)
          ·
            refine ⟨49856389796198132649132643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265900745579723374128707429 49856389796198132649132643)
            ·
              refine ⟨74784584694297198973698965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49856389796198132649132643 74784584694297198973698965)
              ·
                refine ⟨3505527407545181201892139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74784584694297198973698965 3505527407545181201892139)
                ·
                  refine ⟨5258291111317771802838209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505527407545181201892139 5258291111317771802838209)
                  ·
                    refine ⟨3943718333488328852128657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258291111317771802838209 3943718333488328852128657)
                    ·
                      refine ⟨2957788750116246639096493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943718333488328852128657 2957788750116246639096493)
                      ·
                        rfl

theorem cell23_5760273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_5760273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760273 prefixEnd_5760273 := by exact prefixLift 5760273
  have htrace : WordTrace (prefixWord ++ tailWord_5760273) baseStart_5760273 baseEnd_5760273 := by
    simpa [prefixWord, tailWord_5760273, baseEnd_5760273] using wordTrace_append hprefix tailTrace_5760273
  have hstable : (prefixWord ++ tailWord_5760273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760273).length < 2 ^ (prefixWord ++ tailWord_5760273).sum := by decide
  have hdescent : baseEnd_5760273 < baseStart_5760273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760296 : List Nat := [2, 1, 5, 1, 2, 3, 2, 7]
def baseStart_5760296 : Nat := 118140960795 + 5760296 * 2 ^ 59
def prefixEnd_5760296 : Nat := 4983230072969 + 3 ^ 40 * 5760296 * 2
def baseEnd_5760296 : Nat := 109548168895233335152181

theorem tailTrace_5760296 : CollatzResearch.WordTrace tailWord_5760296 prefixEnd_5760296 109548168895233335152181 := by
  unfold tailWord_5760296
  simp only [CollatzResearch.WordTrace]
  refine ⟨105047627569719423539582371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140063503426292564719443161 105047627569719423539582371)
  ·
    refine ⟨157571441354579135309373557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105047627569719423539582371 157571441354579135309373557)
    ·
      refine ⟨14772322626991793935253771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157571441354579135309373557 14772322626991793935253771)
      ·
        refine ⟨22158483940487690902880657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772322626991793935253771 22158483940487690902880657)
        ·
          refine ⟨16618862955365768177160493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22158483940487690902880657 16618862955365768177160493)
          ·
            refine ⟨6232073608262163066435185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16618862955365768177160493 6232073608262163066435185)
            ·
              refine ⟨4674055206196622299826389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232073608262163066435185 4674055206196622299826389)
              ·
                refine ⟨109548168895233335152181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4674055206196622299826389 109548168895233335152181)
                ·
                  rfl

theorem cell23_5760296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 7].length) (baseStart_5760296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760296 prefixEnd_5760296 := by exact prefixLift 5760296
  have htrace : WordTrace (prefixWord ++ tailWord_5760296) baseStart_5760296 baseEnd_5760296 := by
    simpa [prefixWord, tailWord_5760296, baseEnd_5760296] using wordTrace_append hprefix tailTrace_5760296
  have hstable : (prefixWord ++ tailWord_5760296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760296).length < 2 ^ (prefixWord ++ tailWord_5760296).sum := by decide
  have hdescent : baseEnd_5760296 < baseStart_5760296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760306 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_5760306 : Nat := 118140960795 + 5760306 * 2 ^ 59
def prefixEnd_5760306 : Nat := 4983230072969 + 3 ^ 40 * 5760306 * 2
def baseEnd_5760306 : Nat := 2957805694977845009983841

theorem tailTrace_5760306 : CollatzResearch.WordTrace tailWord_5760306 prefixEnd_5760306 2957805694977845009983841 := by
  unfold tailWord_5760306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52523904967350654696757193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140063746579601745858019181 52523904967350654696757193)
  ·
    refine ⟨39392928725512991022567895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52523904967350654696757193 39392928725512991022567895)
    ·
      refine ⟨59089393088269486533851843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39392928725512991022567895 59089393088269486533851843)
      ·
        refine ⟨88634089632404229800777765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59089393088269486533851843 88634089632404229800777765)
        ·
          refine ⟨16618891806075793087645831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88634089632404229800777765 16618891806075793087645831)
          ·
            refine ⟨24928337709113689631468747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16618891806075793087645831 24928337709113689631468747)
            ·
              refine ⟨37392506563670534447203121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24928337709113689631468747 37392506563670534447203121)
              ·
                refine ⟨28044379922752900835402341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37392506563670534447203121 28044379922752900835402341)
                ·
                  refine ⟨5258321235516168906637939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28044379922752900835402341 5258321235516168906637939)
                  ·
                    refine ⟨7887481853274253359956909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258321235516168906637939 7887481853274253359956909)
                    ·
                      refine ⟨2957805694977845009983841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887481853274253359956909 2957805694977845009983841)
                      ·
                        rfl

theorem cell23_5760306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_5760306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760306 prefixEnd_5760306 := by exact prefixLift 5760306
  have htrace : WordTrace (prefixWord ++ tailWord_5760306) baseStart_5760306 baseEnd_5760306 := by
    simpa [prefixWord, tailWord_5760306, baseEnd_5760306] using wordTrace_append hprefix tailTrace_5760306
  have hstable : (prefixWord ++ tailWord_5760306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760306).length < 2 ^ (prefixWord ++ tailWord_5760306).sum := by decide
  have hdescent : baseEnd_5760306 < baseStart_5760306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760312 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_5760312 : Nat := 118140960795 + 5760312 * 2 ^ 59
def prefixEnd_5760312 : Nat := 4983230072969 + 3 ^ 40 * 5760312 * 2
def baseEnd_5760312 : Nat := 2957808775861771986508813

theorem tailTrace_5760312 : CollatzResearch.WordTrace tailWord_5760312 prefixEnd_5760312 2957808775861771986508813 := by
  unfold tailWord_5760312
  simp only [CollatzResearch.WordTrace]
  refine ⟨105047919353690440905873595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140063892471587254541164793 105047919353690440905873595)
  ·
    refine ⟨157571879030535661358810393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105047919353690440905873595 157571879030535661358810393)
    ·
      refine ⟨118178909272901746019107795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157571879030535661358810393 118178909272901746019107795)
      ·
        refine ⟨177268363909352619028661693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118178909272901746019107795 177268363909352619028661693)
        ·
          refine ⟨66475636466007232135748135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177268363909352619028661693 66475636466007232135748135)
          ·
            refine ⟨99713454699010848203622203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66475636466007232135748135 99713454699010848203622203)
            ·
              refine ⟨149570182048516272305433305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99713454699010848203622203 149570182048516272305433305)
              ·
                refine ⟨112177636536387204229074979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149570182048516272305433305 112177636536387204229074979)
                ·
                  refine ⟨168266454804580806343612469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112177636536387204229074979 168266454804580806343612469)
                  ·
                    refine ⟨15774980137929450594713669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168266454804580806343612469 15774980137929450594713669)
                    ·
                      refine ⟨2957808775861771986508813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15774980137929450594713669 2957808775861771986508813)
                      ·
                        rfl

theorem cell23_5760312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_5760312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760312 prefixEnd_5760312 := by exact prefixLift 5760312
  have htrace : WordTrace (prefixWord ++ tailWord_5760312) baseStart_5760312 baseEnd_5760312 := by
    simpa [prefixWord, tailWord_5760312, baseEnd_5760312] using wordTrace_append hprefix tailTrace_5760312
  have hstable : (prefixWord ++ tailWord_5760312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760312).length < 2 ^ (prefixWord ++ tailWord_5760312).sum := by decide
  have hdescent : baseEnd_5760312 < baseStart_5760312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760324 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5760324 : Nat := 118140960795 + 5760324 * 2 ^ 59
def prefixEnd_5760324 : Nat := 4983230072969 + 3 ^ 40 * 5760324 * 2
def baseEnd_5760324 : Nat := 2957814937629625939558759

theorem tailTrace_5760324 : CollatzResearch.WordTrace tailWord_5760324 prefixEnd_5760324 2957814937629625939558759 := by
  unfold tailWord_5760324
  simp only [CollatzResearch.WordTrace]
  refine ⟨105048138191668703930592013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140064184255558271907456017 105048138191668703930592013)
  ·
    refine ⟨39393051821875763973972005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105048138191668703930592013 39393051821875763973972005)
    ·
      refine ⟨7386197216601705745119751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39393051821875763973972005 7386197216601705745119751)
      ·
        refine ⟨11079295824902558617679627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386197216601705745119751 11079295824902558617679627)
        ·
          refine ⟨16618943737353837926519441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11079295824902558617679627 16618943737353837926519441)
          ·
            refine ⟨12464207803015378444889581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16618943737353837926519441 12464207803015378444889581)
            ·
              refine ⟨4674077926130766916833593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12464207803015378444889581 4674077926130766916833593)
              ·
                refine ⟨3505558444598075187625195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674077926130766916833593 3505558444598075187625195)
                ·
                  refine ⟨5258337666897112781437793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505558444598075187625195 5258337666897112781437793)
                  ·
                    refine ⟨3943753250172834586078345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258337666897112781437793 3943753250172834586078345)
                    ·
                      refine ⟨2957814937629625939558759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943753250172834586078345 2957814937629625939558759)
                      ·
                        rfl

theorem cell23_5760324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5760324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760324 prefixEnd_5760324 := by exact prefixLift 5760324
  have htrace : WordTrace (prefixWord ++ tailWord_5760324) baseStart_5760324 baseEnd_5760324 := by
    simpa [prefixWord, tailWord_5760324, baseEnd_5760324] using wordTrace_append hprefix tailTrace_5760324
  have hstable : (prefixWord ++ tailWord_5760324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760324).length < 2 ^ (prefixWord ++ tailWord_5760324).sum := by decide
  have hdescent : baseEnd_5760324 < baseStart_5760324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760379 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3]
def baseStart_5760379 : Nat := 118140960795 + 5760379 * 2 ^ 59
def prefixEnd_5760379 : Nat := 4983230072969 + 3 ^ 40 * 5760379 * 2
def baseEnd_5760379 : Nat := 2957843179065623224371005

theorem tailTrace_5760379 : CollatzResearch.WordTrace tailWord_5760379 prefixEnd_5760379 2957843179065623224371005 := by
  unfold tailWord_5760379
  simp only [CollatzResearch.WordTrace]
  refine ⟨210098282398138152254436191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140065521598758768169624127 210098282398138152254436191)
  ·
    refine ⟨315147423597207228381654287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210098282398138152254436191 315147423597207228381654287)
    ·
      refine ⟨472721135395810842572481431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315147423597207228381654287 472721135395810842572481431)
      ·
        refine ⟨709081703093716263858722147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472721135395810842572481431 709081703093716263858722147)
        ·
          refine ⟨1063622554640574395788083221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709081703093716263858722147 1063622554640574395788083221)
          ·
            refine ⟨49857307248776924802566401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1063622554640574395788083221 49857307248776924802566401)
            ·
              refine ⟨37392980436582693601924801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49857307248776924802566401 37392980436582693601924801)
              ·
                refine ⟨28044735327437020201443601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37392980436582693601924801 28044735327437020201443601)
                ·
                  refine ⟨21033551495577765151082701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28044735327437020201443601 21033551495577765151082701)
                  ·
                    refine ⟨7887581810841661931656013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21033551495577765151082701 7887581810841661931656013)
                    ·
                      refine ⟨2957843179065623224371005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887581810841661931656013 2957843179065623224371005)
                      ·
                        rfl

theorem cell23_5760379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 3, 3].length) (baseStart_5760379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760379 prefixEnd_5760379 := by exact prefixLift 5760379
  have htrace : WordTrace (prefixWord ++ tailWord_5760379) baseStart_5760379 baseEnd_5760379 := by
    simpa [prefixWord, tailWord_5760379, baseEnd_5760379] using wordTrace_append hprefix tailTrace_5760379
  have hstable : (prefixWord ++ tailWord_5760379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760379).length < 2 ^ (prefixWord ++ tailWord_5760379).sum := by decide
  have hdescent : baseEnd_5760379 < baseStart_5760379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760419 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4]
def baseStart_5760419 : Nat := 118140960795 + 5760419 * 2 ^ 59
def prefixEnd_5760419 : Nat := 4983230072969 + 3 ^ 40 * 5760419 * 2
def baseEnd_5760419 : Nat := 2957863718291803067870821

theorem tailTrace_5760419 : CollatzResearch.WordTrace tailWord_5760419 prefixEnd_5760419 2957863718291803067870821 := by
  unfold tailWord_5760419
  simp only [CollatzResearch.WordTrace]
  refine ⟨210099741317993239085892311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140066494211995492723928207 210099741317993239085892311)
  ·
    refine ⟨315149611976989858628838467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210099741317993239085892311 315149611976989858628838467)
    ·
      refine ⟨472724417965484787943257701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315149611976989858628838467 472724417965484787943257701)
      ·
        refine ⟨88635828368528397739360819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 472724417965484787943257701 88635828368528397739360819)
        ·
          refine ⟨132953742552792596609041229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88635828368528397739360819 132953742552792596609041229)
          ·
            refine ⟨49857653457297223728390461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132953742552792596609041229 49857653457297223728390461)
            ·
              refine ⟨18696620046486458898146423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49857653457297223728390461 18696620046486458898146423)
              ·
                refine ⟨28044930069729688347219635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18696620046486458898146423 28044930069729688347219635)
                ·
                  refine ⟨42067395104594532520829453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28044930069729688347219635 42067395104594532520829453)
                  ·
                    refine ⟨15775273164222949695311045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42067395104594532520829453 15775273164222949695311045)
                    ·
                      refine ⟨2957863718291803067870821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15775273164222949695311045 2957863718291803067870821)
                      ·
                        rfl

theorem cell23_5760419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_5760419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760419 prefixEnd_5760419 := by exact prefixLift 5760419
  have htrace : WordTrace (prefixWord ++ tailWord_5760419) baseStart_5760419 baseEnd_5760419 := by
    simpa [prefixWord, tailWord_5760419, baseEnd_5760419] using wordTrace_append hprefix tailTrace_5760419
  have hstable : (prefixWord ++ tailWord_5760419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760419).length < 2 ^ (prefixWord ++ tailWord_5760419).sum := by decide
  have hdescent : baseEnd_5760419 < baseStart_5760419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760459 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 6]
def baseStart_5760459 : Nat := 118140960795 + 5760459 * 2 ^ 59
def prefixEnd_5760459 : Nat := 4983230072969 + 3 ^ 40 * 5760459 * 2
def baseEnd_5760459 : Nat := 328653806390886990152293

theorem tailTrace_5760459 : CollatzResearch.WordTrace tailWord_5760459 prefixEnd_5760459 328653806390886990152293 := by
  unfold tailWord_5760459
  simp only [CollatzResearch.WordTrace]
  refine ⟨210101200237848325917348431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140067466825232217278232287 210101200237848325917348431)
  ·
    refine ⟨315151800356772488876022647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210101200237848325917348431 315151800356772488876022647)
    ·
      refine ⟨472727700535158733314033971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315151800356772488876022647 472727700535158733314033971)
      ·
        refine ⟨709091550802738099971050957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472727700535158733314033971 709091550802738099971050957)
        ·
          refine ⟨265909331551026787489144109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709091550802738099971050957 265909331551026787489144109)
          ·
            refine ⟨99715999331635045308429041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265909331551026787489144109 99715999331635045308429041)
            ·
              refine ⟨74786999498726283981321781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99715999331635045308429041 74786999498726283981321781)
              ·
                refine ⟨7011281203005589123248917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74786999498726283981321781 7011281203005589123248917)
                ·
                  refine ⟨328653806390886990152293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7011281203005589123248917 328653806390886990152293)
                  ·
                    rfl

theorem cell23_5760459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 6].length) (baseStart_5760459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760459 prefixEnd_5760459 := by exact prefixLift 5760459
  have htrace : WordTrace (prefixWord ++ tailWord_5760459) baseStart_5760459 baseEnd_5760459 := by
    simpa [prefixWord, tailWord_5760459, baseEnd_5760459] using wordTrace_append hprefix tailTrace_5760459
  have hstable : (prefixWord ++ tailWord_5760459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760459).length < 2 ^ (prefixWord ++ tailWord_5760459).sum := by decide
  have hdescent : baseEnd_5760459 < baseStart_5760459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760510 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_5760510 : Nat := 118140960795 + 5760510 * 2 ^ 59
def prefixEnd_5760510 : Nat := 4983230072969 + 3 ^ 40 * 5760510 * 2
def baseEnd_5760510 : Nat := 328656716114595801314767

theorem tailTrace_5760510 : CollatzResearch.WordTrace tailWord_5760510 prefixEnd_5760510 328656716114595801314767 := by
  unfold tailWord_5760510
  simp only [CollatzResearch.WordTrace]
  refine ⟨26262882545082945203431873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140068706907109041084969989 26262882545082945203431873)
  ·
    refine ⟨19697161908812208902573905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26262882545082945203431873 19697161908812208902573905)
    ·
      refine ⟨14772871431609156676930429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19697161908812208902573905 14772871431609156676930429)
      ·
        refine ⟨5539826786853433753848911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14772871431609156676930429 5539826786853433753848911)
        ·
          refine ⟨8309740180280150630773367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539826786853433753848911 8309740180280150630773367)
          ·
            refine ⟨12464610270420225946160051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309740180280150630773367 12464610270420225946160051)
            ·
              refine ⟨18696915405630338919240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12464610270420225946160051 18696915405630338919240077)
              ·
                refine ⟨7011343277111377094715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18696915405630338919240077 7011343277111377094715029)
                ·
                  refine ⟨328656716114595801314767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7011343277111377094715029 328656716114595801314767)
                  ·
                    rfl

theorem cell23_5760510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_5760510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760510 prefixEnd_5760510 := by exact prefixLift 5760510
  have htrace : WordTrace (prefixWord ++ tailWord_5760510) baseStart_5760510 baseEnd_5760510 := by
    simpa [prefixWord, tailWord_5760510, baseEnd_5760510] using wordTrace_append hprefix tailTrace_5760510
  have hstable : (prefixWord ++ tailWord_5760510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760510).length < 2 ^ (prefixWord ++ tailWord_5760510).sum := by decide
  have hdescent : baseEnd_5760510 < baseStart_5760510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760583 : List Nat := [1, 1, 4, 1, 5, 1, 3, 7]
def baseStart_5760583 : Nat := 118140960795 + 5760583 * 2 ^ 59
def prefixEnd_5760583 : Nat := 4983230072969 + 3 ^ 40 * 5760583 * 2
def baseEnd_5760583 : Nat := 109553627004412608378521

theorem tailTrace_5760583 : CollatzResearch.WordTrace tailWord_5760583 prefixEnd_5760583 109553627004412608378521 := by
  unfold tailWord_5760583
  simp only [CollatzResearch.WordTrace]
  refine ⟨210105722889399095094862403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140070481926266063396574935 210105722889399095094862403)
  ·
    refine ⟨315158584334098642642293605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210105722889399095094862403 315158584334098642642293605)
    ·
      refine ⟨59092234562643495495430051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315158584334098642642293605 59092234562643495495430051)
      ·
        refine ⟨88638351843965243243145077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59092234562643495495430051 88638351843965243243145077)
        ·
          refine ⟨8309845485371741554044851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88638351843965243243145077 8309845485371741554044851)
          ·
            refine ⟨12464768228057612331067277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8309845485371741554044851 12464768228057612331067277)
            ·
              refine ⟨4674288085521604624150229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12464768228057612331067277 4674288085521604624150229)
              ·
                refine ⟨109553627004412608378521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4674288085521604624150229 109553627004412608378521)
                ·
                  rfl

theorem cell23_5760583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 7].length) (baseStart_5760583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760583 prefixEnd_5760583 := by exact prefixLift 5760583
  have htrace : WordTrace (prefixWord ++ tailWord_5760583) baseStart_5760583 baseEnd_5760583 := by
    simpa [prefixWord, tailWord_5760583, baseEnd_5760583] using wordTrace_append hprefix tailTrace_5760583
  have hstable : (prefixWord ++ tailWord_5760583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760583).length < 2 ^ (prefixWord ++ tailWord_5760583).sum := by decide
  have hdescent : baseEnd_5760583 < baseStart_5760583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760593 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_5760593 : Nat := 118140960795 + 5760593 * 2 ^ 59
def prefixEnd_5760593 : Nat := 4983230072969 + 3 ^ 40 * 5760593 * 2
def baseEnd_5760593 : Nat := 2957953063925685387095021

theorem tailTrace_5760593 : CollatzResearch.WordTrace tailWord_5760593 prefixEnd_5760593 2957953063925685387095021 := by
  unfold tailWord_5760593
  simp only [CollatzResearch.WordTrace]
  refine ⟨210106087619362866802726433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140070725079575244535150955 210106087619362866802726433)
  ·
    refine ⟨157579565714522150102044825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210106087619362866802726433 157579565714522150102044825)
    ·
      refine ⟨118184674285891612576533619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157579565714522150102044825 118184674285891612576533619)
      ·
        refine ⟨177277011428837418864800429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118184674285891612576533619 177277011428837418864800429)
        ·
          refine ⟨66478879285814032074300161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177277011428837418864800429 66478879285814032074300161)
          ·
            refine ⟨49859159464360524055725121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66478879285814032074300161 49859159464360524055725121)
            ·
              refine ⟨37394369598270393041793841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49859159464360524055725121 37394369598270393041793841)
              ·
                refine ⟨28045777198702794781345381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37394369598270393041793841 28045777198702794781345381)
                ·
                  refine ⟨5258583224756774021502259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28045777198702794781345381 5258583224756774021502259)
                  ·
                    refine ⟨7887874837135161032253389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258583224756774021502259 7887874837135161032253389)
                    ·
                      refine ⟨2957953063925685387095021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7887874837135161032253389 2957953063925685387095021)
                      ·
                        rfl

theorem cell23_5760593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_5760593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760593 prefixEnd_5760593 := by exact prefixLift 5760593
  have htrace : WordTrace (prefixWord ++ tailWord_5760593) baseStart_5760593 baseEnd_5760593 := by
    simpa [prefixWord, tailWord_5760593, baseEnd_5760593] using wordTrace_append hprefix tailTrace_5760593
  have hstable : (prefixWord ++ tailWord_5760593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760593).length < 2 ^ (prefixWord ++ tailWord_5760593).sum := by decide
  have hdescent : baseEnd_5760593 < baseStart_5760593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760594 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_5760594 : Nat := 118140960795 + 5760594 * 2 ^ 59
def prefixEnd_5760594 : Nat := 4983230072969 + 3 ^ 40 * 5760594 * 2
def baseEnd_5760594 : Nat := 2957953577406339883182517

theorem tailTrace_5760594 : CollatzResearch.WordTrace tailWord_5760594 prefixEnd_5760594 2957953577406339883182517 := by
  unfold tailWord_5760594
  simp only [CollatzResearch.WordTrace]
  refine ⟨52526531023089810993378209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140070749394906162649008557 52526531023089810993378209)
  ·
    refine ⟨39394898267317358245033657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52526531023089810993378209 39394898267317358245033657)
    ·
      refine ⟨29546173700488018683775243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39394898267317358245033657 29546173700488018683775243)
      ·
        refine ⟨44319260550732028025662865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29546173700488018683775243 44319260550732028025662865)
        ·
          refine ⟨33239445413049021019247149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44319260550732028025662865 33239445413049021019247149)
          ·
            refine ⟨12464792029893382882217681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33239445413049021019247149 12464792029893382882217681)
            ·
              refine ⟨9348594022420037161663261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12464792029893382882217681 9348594022420037161663261)
              ·
                refine ⟨3505722758407513935623723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9348594022420037161663261 3505722758407513935623723)
                ·
                  refine ⟨5258584137611270903435585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505722758407513935623723 5258584137611270903435585)
                  ·
                    refine ⟨3943938103208453177576689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258584137611270903435585 3943938103208453177576689)
                    ·
                      refine ⟨2957953577406339883182517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943938103208453177576689 2957953577406339883182517)
                      ·
                        rfl

theorem cell23_5760594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_5760594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760594 prefixEnd_5760594 := by exact prefixLift 5760594
  have htrace : WordTrace (prefixWord ++ tailWord_5760594) baseStart_5760594 baseEnd_5760594 := by
    simpa [prefixWord, tailWord_5760594, baseEnd_5760594] using wordTrace_append hprefix tailTrace_5760594
  have hstable : (prefixWord ++ tailWord_5760594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760594).length < 2 ^ (prefixWord ++ tailWord_5760594).sum := by decide
  have hdescent : baseEnd_5760594 < baseStart_5760594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760636 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_5760636 : Nat := 118140960795 + 5760636 * 2 ^ 59
def prefixEnd_5760636 : Nat := 4983230072969 + 3 ^ 40 * 5760636 * 2
def baseEnd_5760636 : Nat := 2957975143593828718857323

theorem tailTrace_5760636 : CollatzResearch.WordTrace tailWord_5760636 prefixEnd_5760636 2957975143593828718857323 := by
  unfold tailWord_5760636
  simp only [CollatzResearch.WordTrace]
  refine ⟨105053827979103542573270881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140071770638804723431027841 105053827979103542573270881)
  ·
    refine ⟨78790370984327656929953161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105053827979103542573270881 78790370984327656929953161)
    ·
      refine ⟨59092778238245742697464871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78790370984327656929953161 59092778238245742697464871)
      ·
        refine ⟨88639167357368614046197307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59092778238245742697464871 88639167357368614046197307)
        ·
          refine ⟨132958751036052921069295961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88639167357368614046197307 132958751036052921069295961)
          ·
            refine ⟨99719063277039690801971971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132958751036052921069295961 99719063277039690801971971)
            ·
              refine ⟨149578594915559536202957957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99719063277039690801971971 149578594915559536202957957)
              ·
                refine ⟨28045986546667413038054617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149578594915559536202957957 28045986546667413038054617)
                ·
                  refine ⟨21034489910000559778540963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28045986546667413038054617 21034489910000559778540963)
                  ·
                    refine ⟨31551734865000839667811445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21034489910000559778540963 31551734865000839667811445)
                    ·
                      refine ⟨2957975143593828718857323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31551734865000839667811445 2957975143593828718857323)
                      ·
                        rfl

theorem cell23_5760636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_5760636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760636 prefixEnd_5760636 := by exact prefixLift 5760636
  have htrace : WordTrace (prefixWord ++ tailWord_5760636) baseStart_5760636 baseEnd_5760636 := by
    simpa [prefixWord, tailWord_5760636, baseEnd_5760636] using wordTrace_append hprefix tailTrace_5760636
  have hstable : (prefixWord ++ tailWord_5760636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760636).length < 2 ^ (prefixWord ++ tailWord_5760636).sum := by decide
  have hdescent : baseEnd_5760636 < baseStart_5760636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760637 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_5760637 : Nat := 118140960795 + 5760637 * 2 ^ 59
def prefixEnd_5760637 : Nat := 4983230072969 + 3 ^ 40 * 5760637 * 2
def baseEnd_5760637 : Nat := 2957975657074483214944819

theorem tailTrace_5760637 : CollatzResearch.WordTrace tailWord_5760637 prefixEnd_5760637 2957975657074483214944819 := by
  unfold tailWord_5760637
  simp only [CollatzResearch.WordTrace]
  refine ⟨210107692431203462317328165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140071794954135641544885443 210107692431203462317328165)
  ·
    refine ⟨39395192330850649184499031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210107692431203462317328165 39395192330850649184499031)
    ·
      refine ⟨59092788496275973776748547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39395192330850649184499031 59092788496275973776748547)
      ·
        refine ⟨88639182744413960665122821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59092788496275973776748547 88639182744413960665122821)
        ·
          refine ⟨16619846764577617624710529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88639182744413960665122821 16619846764577617624710529)
          ·
            refine ⟨12464885073433213218532897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16619846764577617624710529 12464885073433213218532897)
            ·
              refine ⟨9348663805074909913899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12464885073433213218532897 9348663805074909913899673)
              ·
                refine ⟨7011497853806182435424755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9348663805074909913899673 7011497853806182435424755)
                ·
                  refine ⟨10517246780709273653137133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7011497853806182435424755 10517246780709273653137133)
                  ·
                    refine ⟨3943967542765977619926425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10517246780709273653137133 3943967542765977619926425)
                    ·
                      refine ⟨2957975657074483214944819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3943967542765977619926425 2957975657074483214944819)
                      ·
                        rfl

theorem cell23_5760637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_5760637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760637 prefixEnd_5760637 := by exact prefixLift 5760637
  have htrace : WordTrace (prefixWord ++ tailWord_5760637) baseStart_5760637 baseEnd_5760637 := by
    simpa [prefixWord, tailWord_5760637, baseEnd_5760637] using wordTrace_append hprefix tailTrace_5760637
  have hstable : (prefixWord ++ tailWord_5760637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760637).length < 2 ^ (prefixWord ++ tailWord_5760637).sum := by decide
  have hdescent : baseEnd_5760637 < baseStart_5760637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760673 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 7]
def baseStart_5760673 : Nat := 118140960795 + 5760673 * 2 ^ 59
def prefixEnd_5760673 : Nat := 4983230072969 + 3 ^ 40 * 5760673 * 2
def baseEnd_5760673 : Nat := 328666015819782786010517

theorem tailTrace_5760673 : CollatzResearch.WordTrace tailWord_5760673 prefixEnd_5760673 328666015819782786010517 := by
  unfold tailWord_5760673
  simp only [CollatzResearch.WordTrace]
  refine ⟨210109005459073040465638673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140072670306048693643759115 210109005459073040465638673)
  ·
    refine ⟨157581754094304780349229005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210109005459073040465638673 157581754094304780349229005)
    ·
      refine ⟨59093157785364292630960877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157581754094304780349229005 59093157785364292630960877)
      ·
        refine ⟨22159934169511609736610329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59093157785364292630960877 22159934169511609736610329)
        ·
          refine ⟨16619950627133707302457747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22159934169511609736610329 16619950627133707302457747)
          ·
            refine ⟨24929925940700560953686621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16619950627133707302457747 24929925940700560953686621)
            ·
              refine ⟨9348722227762710357632483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24929925940700560953686621 9348722227762710357632483)
              ·
                refine ⟨14023083341644065536448725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9348722227762710357632483 14023083341644065536448725)
                ·
                  refine ⟨328666015819782786010517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14023083341644065536448725 328666015819782786010517)
                  ·
                    rfl

theorem cell23_5760673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 7].length) (baseStart_5760673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760673 prefixEnd_5760673 := by exact prefixLift 5760673
  have htrace : WordTrace (prefixWord ++ tailWord_5760673) baseStart_5760673 baseEnd_5760673 := by
    simpa [prefixWord, tailWord_5760673, baseEnd_5760673] using wordTrace_append hprefix tailTrace_5760673
  have hstable : (prefixWord ++ tailWord_5760673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760673).length < 2 ^ (prefixWord ++ tailWord_5760673).sum := by decide
  have hdescent : baseEnd_5760673 < baseStart_5760673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760703 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 2, 5]
def baseStart_5760703 : Nat := 118140960795 + 5760703 * 2 ^ 59
def prefixEnd_5760703 : Nat := 4983230072969 + 3 ^ 40 * 5760703 * 2
def baseEnd_5760703 : Nat := 986003182265893318906505

theorem tailTrace_5760703 : CollatzResearch.WordTrace tailWord_5760703 prefixEnd_5760703 986003182265893318906505 := by
  unfold tailWord_5760703
  simp only [CollatzResearch.WordTrace]
  refine ⟨210110099648964355589230763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140073399765976237059487175 210110099648964355589230763)
  ·
    refine ⟨315165149473446533383846145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210110099648964355589230763 315165149473446533383846145)
    ·
      refine ⟨236373862105084900037884609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315165149473446533383846145 236373862105084900037884609)
      ·
        refine ⟨177280396578813675028413457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236373862105084900037884609 177280396578813675028413457)
        ·
          refine ⟨132960297434110256271310093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177280396578813675028413457 132960297434110256271310093)
          ·
            refine ⟨49860111537791346101741285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132960297434110256271310093 49860111537791346101741285)
            ·
              refine ⟨9348770913335877394076491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49860111537791346101741285 9348770913335877394076491)
              ·
                refine ⟨14023156370003816091114737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9348770913335877394076491 14023156370003816091114737)
                ·
                  refine ⟨10517367277502862068336053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14023156370003816091114737 10517367277502862068336053)
                  ·
                    refine ⟨986003182265893318906505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10517367277502862068336053 986003182265893318906505)
                    ·
                      rfl

theorem cell23_5760703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 5].length) (baseStart_5760703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760703 prefixEnd_5760703 := by exact prefixLift 5760703
  have htrace : WordTrace (prefixWord ++ tailWord_5760703) baseStart_5760703 baseEnd_5760703 := by
    simpa [prefixWord, tailWord_5760703, baseEnd_5760703] using wordTrace_append hprefix tailTrace_5760703
  have hstable : (prefixWord ++ tailWord_5760703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760703).length < 2 ^ (prefixWord ++ tailWord_5760703).sum := by decide
  have hdescent : baseEnd_5760703 < baseStart_5760703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760724 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 5]
def baseStart_5760724 : Nat := 118140960795 + 5760724 * 2 ^ 59
def prefixEnd_5760724 : Nat := 4983230072969 + 3 ^ 40 * 5760724 * 2
def baseEnd_5760724 : Nat := 328668925543491597172991

theorem tailTrace_5760724 : CollatzResearch.WordTrace tailWord_5760724 prefixEnd_5760724 328668925543491597172991 := by
  unfold tailWord_5760724
  simp only [CollatzResearch.WordTrace]
  refine ⟨105055432790944138087872613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140073910387925517450496817 105055432790944138087872613)
  ·
    refine ⟨19697893648302025891476115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105055432790944138087872613 19697893648302025891476115)
    ·
      refine ⟨29546840472453038837214173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19697893648302025891476115 29546840472453038837214173)
      ·
        refine ⟨11080065177169889563955315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29546840472453038837214173 11080065177169889563955315)
        ·
          refine ⟨16620097765754834345932973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080065177169889563955315 16620097765754834345932973)
          ·
            refine ⟨6232536662158062879724865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16620097765754834345932973 6232536662158062879724865)
            ·
              refine ⟨4674402496618547159793649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232536662158062879724865 4674402496618547159793649)
              ·
                refine ⟨3505801872463910369845237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674402496618547159793649 3505801872463910369845237)
                ·
                  refine ⟨328668925543491597172991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3505801872463910369845237 328668925543491597172991)
                  ·
                    rfl

theorem cell23_5760724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_5760724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760724 prefixEnd_5760724 := by exact prefixLift 5760724
  have htrace : WordTrace (prefixWord ++ tailWord_5760724) baseStart_5760724 baseEnd_5760724 := by
    simpa [prefixWord, tailWord_5760724, baseEnd_5760724] using wordTrace_append hprefix tailTrace_5760724
  have hstable : (prefixWord ++ tailWord_5760724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760724).length < 2 ^ (prefixWord ++ tailWord_5760724).sum := by decide
  have hdescent : baseEnd_5760724 < baseStart_5760724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760740 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_5760740 : Nat := 118140960795 + 5760740 * 2 ^ 59
def prefixEnd_5760740 : Nat := 4983230072969 + 3 ^ 40 * 5760740 * 2
def baseEnd_5760740 : Nat := 2958028545581896311956845

theorem tailTrace_5760740 : CollatzResearch.WordTrace tailWord_5760740 prefixEnd_5760740 2958028545581896311956845 := by
  unfold tailWord_5760740
  simp only [CollatzResearch.WordTrace]
  refine ⟨105055724574915155454163837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140074299433220207272218449 105055724574915155454163837)
  ·
    refine ⟨39395896715593183295311439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105055724574915155454163837 39395896715593183295311439)
    ·
      refine ⟨59093845073389774942967159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39395896715593183295311439 59093845073389774942967159)
      ·
        refine ⟨88640767610084662414450739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59093845073389774942967159 88640767610084662414450739)
        ·
          refine ⟨132961151415126993621676109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88640767610084662414450739 132961151415126993621676109)
          ·
            refine ⟨49860431780672622608128541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132961151415126993621676109 49860431780672622608128541)
            ·
              refine ⟨18697661917752233478048203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49860431780672622608128541 18697661917752233478048203)
              ·
                refine ⟨28046492876628350217072305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18697661917752233478048203 28046492876628350217072305)
                ·
                  refine ⟨21034869657471262662804229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28046492876628350217072305 21034869657471262662804229)
                  ·
                    refine ⟨3944038060775861749275793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21034869657471262662804229 3944038060775861749275793)
                    ·
                      refine ⟨2958028545581896311956845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944038060775861749275793 2958028545581896311956845)
                      ·
                        rfl

theorem cell23_5760740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_5760740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760740 prefixEnd_5760740 := by exact prefixLift 5760740
  have htrace : WordTrace (prefixWord ++ tailWord_5760740) baseStart_5760740 baseEnd_5760740 := by
    simpa [prefixWord, tailWord_5760740, baseEnd_5760740] using wordTrace_append hprefix tailTrace_5760740
  have hstable : (prefixWord ++ tailWord_5760740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760740).length < 2 ^ (prefixWord ++ tailWord_5760740).sum := by decide
  have hdescent : baseEnd_5760740 < baseStart_5760740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760750 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_5760750 : Nat := 118140960795 + 5760750 * 2 ^ 59
def prefixEnd_5760750 : Nat := 4983230072969 + 3 ^ 40 * 5760750 * 2
def baseEnd_5760750 : Nat := 986011226796147090943933

theorem tailTrace_5760750 : CollatzResearch.WordTrace tailWord_5760750 prefixEnd_5760750 986011226796147090943933 := by
  unfold tailWord_5760750
  simp only [CollatzResearch.WordTrace]
  refine ⟨26263976734974260327023963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140074542586529388410794469 26263976734974260327023963)
  ·
    refine ⟨39395965102461390490535945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26263976734974260327023963 39395965102461390490535945)
    ·
      refine ⟨29546973826846042867901959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39395965102461390490535945 29546973826846042867901959)
      ·
        refine ⟨44320460740269064301852939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29546973826846042867901959 44320460740269064301852939)
        ·
          refine ⟨66480691110403596452779409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44320460740269064301852939 66480691110403596452779409)
          ·
            refine ⟨49860518332802697339584557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66480691110403596452779409 49860518332802697339584557)
            ·
              refine ⟨18697694374801011502344209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49860518332802697339584557 18697694374801011502344209)
              ·
                refine ⟨14023270781100758626758157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18697694374801011502344209 14023270781100758626758157)
                ·
                  refine ⟨5258726542912784485034309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14023270781100758626758157 5258726542912784485034309)
                  ·
                    refine ⟨986011226796147090943933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5258726542912784485034309 986011226796147090943933)
                    ·
                      rfl

theorem cell23_5760750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_5760750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760750 prefixEnd_5760750 := by exact prefixLift 5760750
  have htrace : WordTrace (prefixWord ++ tailWord_5760750) baseStart_5760750 baseEnd_5760750 := by
    simpa [prefixWord, tailWord_5760750, baseEnd_5760750] using wordTrace_append hprefix tailTrace_5760750
  have hstable : (prefixWord ++ tailWord_5760750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760750).length < 2 ^ (prefixWord ++ tailWord_5760750).sum := by decide
  have hdescent : baseEnd_5760750 < baseStart_5760750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760800 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5760800 : Nat := 118140960795 + 5760800 * 2 ^ 59
def prefixEnd_5760800 : Nat := 4983230072969 + 3 ^ 40 * 5760800 * 2
def baseEnd_5760800 : Nat := 2958059354421166077206569

theorem tailTrace_5760800 : CollatzResearch.WordTrace tailWord_5760800 prefixEnd_5760800 2958059354421166077206569 := by
  unfold tailWord_5760800
  simp only [CollatzResearch.WordTrace]
  refine ⟨105056818764806470577755927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140075758353075294103674569 105056818764806470577755927)
  ·
    refine ⟨157585228147209705866633891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105056818764806470577755927 157585228147209705866633891)
    ·
      refine ⟨236377842220814558799950837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157585228147209705866633891 236377842220814558799950837)
      ·
        refine ⟨22160422708201364887495391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236377842220814558799950837 22160422708201364887495391)
        ·
          refine ⟨33240634062302047331243087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22160422708201364887495391 33240634062302047331243087)
          ·
            refine ⟨49860951093453070996864631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33240634062302047331243087 49860951093453070996864631)
            ·
              refine ⟨74791426640179606495296947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49860951093453070996864631 74791426640179606495296947)
              ·
                refine ⟨112187139960269409742945421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74791426640179606495296947 112187139960269409742945421)
                ·
                  refine ⟨42070177485101028653604533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112187139960269409742945421 42070177485101028653604533)
                  ·
                    refine ⟨3944079139228221436275425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42070177485101028653604533 3944079139228221436275425)
                    ·
                      refine ⟨2958059354421166077206569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944079139228221436275425 2958059354421166077206569)
                      ·
                        rfl

theorem cell23_5760800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5760800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760800 prefixEnd_5760800 := by exact prefixLift 5760800
  have htrace : WordTrace (prefixWord ++ tailWord_5760800) baseStart_5760800 baseEnd_5760800 := by
    simpa [prefixWord, tailWord_5760800, baseEnd_5760800] using wordTrace_append hprefix tailTrace_5760800
  have hstable : (prefixWord ++ tailWord_5760800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760800).length < 2 ^ (prefixWord ++ tailWord_5760800).sum := by decide
  have hdescent : baseEnd_5760800 < baseStart_5760800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760824 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_5760824 : Nat := 118140960795 + 5760824 * 2 ^ 59
def prefixEnd_5760824 : Nat := 4983230072969 + 3 ^ 40 * 5760824 * 2
def baseEnd_5760824 : Nat := 2958071677956873983306459

theorem tailTrace_5760824 : CollatzResearch.WordTrace tailWord_5760824 prefixEnd_5760824 2958071677956873983306459 := by
  unfold tailWord_5760824
  simp only [CollatzResearch.WordTrace]
  refine ⟨105057256440762996627192763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140076341921017328836257017 105057256440762996627192763)
  ·
    refine ⟨157585884661144494940789145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105057256440762996627192763 157585884661144494940789145)
    ·
      refine ⟨118189413495858371205591859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157585884661144494940789145 118189413495858371205591859)
      ·
        refine ⟨177284120243787556808387789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118189413495858371205591859 177284120243787556808387789)
        ·
          refine ⟨66481545091420333803145421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177284120243787556808387789 66481545091420333803145421)
          ·
            refine ⟨24930579409282625176179533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66481545091420333803145421 24930579409282625176179533)
            ·
              refine ⟨9348967278480984441067325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24930579409282625176179533 9348967278480984441067325)
              ·
                refine ⟨3505862729430369165400247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9348967278480984441067325 3505862729430369165400247)
                ·
                  refine ⟨5258794094145553748100371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505862729430369165400247 5258794094145553748100371)
                  ·
                    refine ⟨7888191141218330622150557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5258794094145553748100371 7888191141218330622150557)
                    ·
                      refine ⟨2958071677956873983306459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888191141218330622150557 2958071677956873983306459)
                      ·
                        rfl

theorem cell23_5760824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_5760824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760824 prefixEnd_5760824 := by exact prefixLift 5760824
  have htrace : WordTrace (prefixWord ++ tailWord_5760824) baseStart_5760824 baseEnd_5760824 := by
    simpa [prefixWord, tailWord_5760824, baseEnd_5760824] using wordTrace_append hprefix tailTrace_5760824
  have hstable : (prefixWord ++ tailWord_5760824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760824).length < 2 ^ (prefixWord ++ tailWord_5760824).sum := by decide
  have hdescent : baseEnd_5760824 < baseStart_5760824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760840 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_5760840 : Nat := 118140960795 + 5760840 * 2 ^ 59
def prefixEnd_5760840 : Nat := 4983230072969 + 3 ^ 40 * 5760840 * 2
def baseEnd_5760840 : Nat := 986026631215781973568795

theorem tailTrace_5760840 : CollatzResearch.WordTrace tailWord_5760840 prefixEnd_5760840 986026631215781973568795 := by
  unfold tailWord_5760840
  simp only [CollatzResearch.WordTrace]
  refine ⟨105057548224734013993483987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140076730966312018657978649 105057548224734013993483987)
  ·
    refine ⟨157586322337101020990225981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105057548224734013993483987 157586322337101020990225981)
    ·
      refine ⟨59094870876412882871334743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157586322337101020990225981 59094870876412882871334743)
      ·
        refine ⟨88642306314619324307002115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59094870876412882871334743 88642306314619324307002115)
        ·
          refine ⟨132963459471928986460503173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88642306314619324307002115 132963459471928986460503173)
          ·
            refine ⟨24930648650986684961344345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132963459471928986460503173 24930648650986684961344345)
            ·
              refine ⟨18697986488240013721008259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24930648650986684961344345 18697986488240013721008259)
              ·
                refine ⟨28046979732360020581512389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18697986488240013721008259 28046979732360020581512389)
                ·
                  refine ⟨5258808699817503859033573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28046979732360020581512389 5258808699817503859033573)
                  ·
                    refine ⟨986026631215781973568795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5258808699817503859033573 986026631215781973568795)
                    ·
                      rfl

theorem cell23_5760840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_5760840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760840 prefixEnd_5760840 := by exact prefixLift 5760840
  have htrace : WordTrace (prefixWord ++ tailWord_5760840) baseStart_5760840 baseEnd_5760840 := by
    simpa [prefixWord, tailWord_5760840, baseEnd_5760840] using wordTrace_append hprefix tailTrace_5760840
  have hstable : (prefixWord ++ tailWord_5760840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760840).length < 2 ^ (prefixWord ++ tailWord_5760840).sum := by decide
  have hdescent : baseEnd_5760840 < baseStart_5760840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760850 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5760850 : Nat := 118140960795 + 5760850 * 2 ^ 59
def prefixEnd_5760850 : Nat := 4983230072969 + 3 ^ 40 * 5760850 * 2
def baseEnd_5760850 : Nat := 2958085028453890881581339

theorem tailTrace_5760850 : CollatzResearch.WordTrace tailWord_5760850 prefixEnd_5760850 2958085028453890881581339 := by
  unfold tailWord_5760850
  simp only [CollatzResearch.WordTrace]
  refine ⟨52528865294857949923708001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140076974119621199796554669 52528865294857949923708001)
  ·
    refine ⟨39396648971143462442781001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52528865294857949923708001 39396648971143462442781001)
    ·
      refine ⟨29547486728357596832085751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39396648971143462442781001 29547486728357596832085751)
      ·
        refine ⟨44321230092536395248128627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29547486728357596832085751 44321230092536395248128627)
        ·
          refine ⟨66481845138804592872192941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44321230092536395248128627 66481845138804592872192941)
          ·
            refine ⟨24930691927051722327072353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66481845138804592872192941 24930691927051722327072353)
            ·
              refine ⟨18698018945288791745304265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24930691927051722327072353 18698018945288791745304265)
              ·
                refine ⟨14023514208966593808978199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18698018945288791745304265 14023514208966593808978199)
                ·
                  refine ⟨21035271313449890713467299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14023514208966593808978199 21035271313449890713467299)
                  ·
                    refine ⟨31552906970174836070200949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21035271313449890713467299 31552906970174836070200949)
                    ·
                      refine ⟨2958085028453890881581339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31552906970174836070200949 2958085028453890881581339)
                      ·
                        rfl

theorem cell23_5760850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5760850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760850 prefixEnd_5760850 := by exact prefixLift 5760850
  have htrace : WordTrace (prefixWord ++ tailWord_5760850) baseStart_5760850 baseEnd_5760850 := by
    simpa [prefixWord, tailWord_5760850, baseEnd_5760850] using wordTrace_append hprefix tailTrace_5760850
  have hstable : (prefixWord ++ tailWord_5760850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760850).length < 2 ^ (prefixWord ++ tailWord_5760850).sum := by decide
  have hdescent : baseEnd_5760850 < baseStart_5760850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760853 : List Nat := [1, 3, 2, 2, 2, 2, 1, 10]
def baseStart_5760853 : Nat := 118140960795 + 5760853 * 2 ^ 59
def prefixEnd_5760853 : Nat := 4983230072969 + 3 ^ 40 * 5760853 * 2
def baseEnd_5760853 : Nat := 109558761810957569253475

theorem tailTrace_5760853 : CollatzResearch.WordTrace tailWord_5760853 prefixEnd_5760853 109558761810957569253475 := by
  unfold tailWord_5760853
  simp only [CollatzResearch.WordTrace]
  refine ⟨210115570598420931207191213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140077047065613954138127475 210115570598420931207191213)
  ·
    refine ⟨78793338974407849202696705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210115570598420931207191213 78793338974407849202696705)
    ·
      refine ⟨59095004230805886902022529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78793338974407849202696705 59095004230805886902022529)
      ·
        refine ⟨44321253173104415176516897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59095004230805886902022529 44321253173104415176516897)
        ·
          refine ⟨33240939879828311382387673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44321253173104415176516897 33240939879828311382387673)
          ·
            refine ⟨24930704909871233536790755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33240939879828311382387673 24930704909871233536790755)
            ·
              refine ⟨37396057364806850305186133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24930704909871233536790755 37396057364806850305186133)
              ·
                refine ⟨109558761810957569253475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37396057364806850305186133 109558761810957569253475)
                ·
                  rfl

theorem cell23_5760853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 10].length) (baseStart_5760853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760853 prefixEnd_5760853 := by exact prefixLift 5760853
  have htrace : WordTrace (prefixWord ++ tailWord_5760853) baseStart_5760853 baseEnd_5760853 := by
    simpa [prefixWord, tailWord_5760853, baseEnd_5760853] using wordTrace_append hprefix tailTrace_5760853
  have hstable : (prefixWord ++ tailWord_5760853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760853).length < 2 ^ (prefixWord ++ tailWord_5760853).sum := by decide
  have hdescent : baseEnd_5760853 < baseStart_5760853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760867 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5760867 : Nat := 118140960795 + 5760867 * 2 ^ 59
def prefixEnd_5760867 : Nat := 4983230072969 + 3 ^ 40 * 5760867 * 2
def baseEnd_5760867 : Nat := 2958093757625017315068761

theorem tailTrace_5760867 : CollatzResearch.WordTrace tailWord_5760867 prefixEnd_5760867 2958093757625017315068761 := by
  unfold tailWord_5760867
  simp only [CollatzResearch.WordTrace]
  refine ⟨210116081220370211598200855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140077387480246807732133903 210116081220370211598200855)
  ·
    refine ⟨315174121830555317397301283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210116081220370211598200855 315174121830555317397301283)
    ·
      refine ⟨472761182745832976095951925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315174121830555317397301283 472761182745832976095951925)
      ·
        refine ⟨44321360882421841508995493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 472761182745832976095951925 44321360882421841508995493)
        ·
          refine ⟨8310255165454095282936655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44321360882421841508995493 8310255165454095282936655)
          ·
            refine ⟨12465382748181142924404983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310255165454095282936655 12465382748181142924404983)
            ·
              refine ⟨18698074122271714386607475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12465382748181142924404983 18698074122271714386607475)
              ·
                refine ⟨28047111183407571579911213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18698074122271714386607475 28047111183407571579911213)
                ·
                  refine ⟨10517666693777839342466705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28047111183407571579911213 10517666693777839342466705)
                  ·
                    refine ⟨7888250020333379506850029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10517666693777839342466705 7888250020333379506850029)
                    ·
                      refine ⟨2958093757625017315068761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888250020333379506850029 2958093757625017315068761)
                      ·
                        rfl

theorem cell23_5760867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5760867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760867 prefixEnd_5760867 := by exact prefixLift 5760867
  have htrace : WordTrace (prefixWord ++ tailWord_5760867) baseStart_5760867 baseEnd_5760867 := by
    simpa [prefixWord, tailWord_5760867, baseEnd_5760867] using wordTrace_append hprefix tailTrace_5760867
  have hstable : (prefixWord ++ tailWord_5760867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760867).length < 2 ^ (prefixWord ++ tailWord_5760867).sum := by decide
  have hdescent : baseEnd_5760867 < baseStart_5760867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760913 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 8]
def baseStart_5760913 : Nat := 118140960795 + 5760913 * 2 ^ 59
def prefixEnd_5760913 : Nat := 4983230072969 + 3 ^ 40 * 5760913 * 2
def baseEnd_5760913 : Nat := 986039125911708045031183

theorem tailTrace_5760913 : CollatzResearch.WordTrace tailWord_5760913 prefixEnd_5760913 986039125911708045031183 := by
  unfold tailWord_5760913
  simp only [CollatzResearch.WordTrace]
  refine ⟨210117758978203561454375393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140078505985469040969583595 210117758978203561454375393)
  ·
    refine ⟨157588319233652671090781545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210117758978203561454375393 157588319233652671090781545)
    ·
      refine ⟨118191239425239503318086159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157588319233652671090781545 118191239425239503318086159)
      ·
        refine ⟨177286859137859254977129239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118191239425239503318086159 177286859137859254977129239)
        ·
          refine ⟨265930288706788882465693859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177286859137859254977129239 265930288706788882465693859)
          ·
            refine ⟨398895433060183323698540789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265930288706788882465693859 398895433060183323698540789)
            ·
              refine ⟨37396446849392186596738199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398895433060183323698540789 37396446849392186596738199)
              ·
                refine ⟨56094670274088279895107299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37396446849392186596738199 56094670274088279895107299)
                ·
                  refine ⟨84142005411132419842660949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56094670274088279895107299 84142005411132419842660949)
                  ·
                    refine ⟨986039125911708045031183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84142005411132419842660949 986039125911708045031183)
                    ·
                      rfl

theorem cell23_5760913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_5760913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760913 prefixEnd_5760913 := by exact prefixLift 5760913
  have htrace : WordTrace (prefixWord ++ tailWord_5760913) baseStart_5760913 baseEnd_5760913 := by
    simpa [prefixWord, tailWord_5760913, baseEnd_5760913] using wordTrace_append hprefix tailTrace_5760913
  have hstable : (prefixWord ++ tailWord_5760913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760913).length < 2 ^ (prefixWord ++ tailWord_5760913).sum := by decide
  have hdescent : baseEnd_5760913 < baseStart_5760913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760914 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5760914 : Nat := 118140960795 + 5760914 * 2 ^ 59
def prefixEnd_5760914 : Nat := 4983230072969 + 3 ^ 40 * 5760914 * 2
def baseEnd_5760914 : Nat := 2958117891215778631181045

theorem tailTrace_5760914 : CollatzResearch.WordTrace tailWord_5760914 prefixEnd_5760914 2958117891215778631181045 := by
  unfold tailWord_5760914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52529448862799984656290449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140078530300799959083441197 52529448862799984656290449)
  ·
    refine ⟨39397086647099988492217837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52529448862799984656290449 39397086647099988492217837)
    ·
      refine ⟨14773907492662495684581689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39397086647099988492217837 14773907492662495684581689)
      ·
        refine ⟨11080430619496871763436267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14773907492662495684581689 11080430619496871763436267)
        ·
          refine ⟨16620645929245307645154401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080430619496871763436267 16620645929245307645154401)
          ·
            refine ⟨12465484446933980733865801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16620645929245307645154401 12465484446933980733865801)
            ·
              refine ⟨9349113335200485550399351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12465484446933980733865801 9349113335200485550399351)
              ·
                refine ⟨14023670002800728325599027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9349113335200485550399351 14023670002800728325599027)
                ·
                  refine ⟨21035505004201092488398541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14023670002800728325599027 21035505004201092488398541)
                  ·
                    refine ⟨7888314376575409683149453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21035505004201092488398541 7888314376575409683149453)
                    ·
                      refine ⟨2958117891215778631181045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888314376575409683149453 2958117891215778631181045)
                      ·
                        rfl

theorem cell23_5760914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5760914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760914 prefixEnd_5760914 := by exact prefixLift 5760914
  have htrace : WordTrace (prefixWord ++ tailWord_5760914) baseStart_5760914 baseEnd_5760914 := by
    simpa [prefixWord, tailWord_5760914, baseEnd_5760914] using wordTrace_append hprefix tailTrace_5760914
  have hstable : (prefixWord ++ tailWord_5760914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760914).length < 2 ^ (prefixWord ++ tailWord_5760914).sum := by decide
  have hdescent : baseEnd_5760914 < baseStart_5760914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760924 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5760924 : Nat := 118140960795 + 5760924 * 2 ^ 59
def prefixEnd_5760924 : Nat := 4983230072969 + 3 ^ 40 * 5760924 * 2
def baseEnd_5760924 : Nat := 2958123026022323592055999

theorem tailTrace_5760924 : CollatzResearch.WordTrace tailWord_5760924 prefixEnd_5760924 2958123026022323592055999 := by
  unfold tailWord_5760924
  simp only [CollatzResearch.WordTrace]
  refine ⟨105059080090581855166512913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140078773454109140222017217 105059080090581855166512913)
  ·
    refine ⟨78794310067936391374884685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105059080090581855166512913 78794310067936391374884685)
    ·
      refine ⟨29547866275476146765581757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78794310067936391374884685 29547866275476146765581757)
      ·
        refine ⟨11080449853303555037093159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29547866275476146765581757 11080449853303555037093159)
        ·
          refine ⟨16620674779955332555639739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080449853303555037093159 16620674779955332555639739)
          ·
            refine ⟨24931012169932998833459609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16620674779955332555639739 24931012169932998833459609)
            ·
              refine ⟨18698259127449749125094707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24931012169932998833459609 18698259127449749125094707)
              ·
                refine ⟨28047388691174623687642061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18698259127449749125094707 28047388691174623687642061)
                ·
                  refine ⟨10517770759190483882865773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28047388691174623687642061 10517770759190483882865773)
                  ·
                    refine ⟨3944164034696431456074665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10517770759190483882865773 3944164034696431456074665)
                    ·
                      refine ⟨2958123026022323592055999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944164034696431456074665 2958123026022323592055999)
                      ·
                        rfl

theorem cell23_5760924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5760924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760924 prefixEnd_5760924 := by exact prefixLift 5760924
  have htrace : WordTrace (prefixWord ++ tailWord_5760924) baseStart_5760924 baseEnd_5760924 := by
    simpa [prefixWord, tailWord_5760924, baseEnd_5760924] using wordTrace_append hprefix tailTrace_5760924
  have hstable : (prefixWord ++ tailWord_5760924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760924).length < 2 ^ (prefixWord ++ tailWord_5760924).sum := by decide
  have hdescent : baseEnd_5760924 < baseStart_5760924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760943 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 9]
def baseStart_5760943 : Nat := 118140960795 + 5760943 * 2 ^ 59
def prefixEnd_5760943 : Nat := 4983230072969 + 3 ^ 40 * 5760943 * 2
def baseEnd_5760943 : Nat := 328681420239417668635379

theorem tailTrace_5760943 : CollatzResearch.WordTrace tailWord_5760943 prefixEnd_5760943 328681420239417668635379 := by
  unfold tailWord_5760943
  simp only [CollatzResearch.WordTrace]
  refine ⟨210118853168094876577967483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140079235445396584385311655 210118853168094876577967483)
  ·
    refine ⟨315178279752142314866951225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210118853168094876577967483 315178279752142314866951225)
    ·
      refine ⟨236383709814106736150213419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315178279752142314866951225 236383709814106736150213419)
      ·
        refine ⟨354575564721160104225320129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236383709814106736150213419 354575564721160104225320129)
        ·
          refine ⟨265931673540870078168990097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354575564721160104225320129 265931673540870078168990097)
          ·
            refine ⟨199448755155652558626742573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265931673540870078168990097 199448755155652558626742573)
            ·
              refine ⟨74793283183369709485028465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199448755155652558626742573 74793283183369709485028465)
              ·
                refine ⟨56094962387527282113771349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74793283183369709485028465 56094962387527282113771349)
                ·
                  refine ⟨328681420239417668635379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56094962387527282113771349 328681420239417668635379)
                  ·
                    rfl

theorem cell23_5760943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 9].length) (baseStart_5760943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760943 prefixEnd_5760943 := by exact prefixLift 5760943
  have htrace : WordTrace (prefixWord ++ tailWord_5760943) baseStart_5760943 baseEnd_5760943 := by
    simpa [prefixWord, tailWord_5760943, baseEnd_5760943] using wordTrace_append hprefix tailTrace_5760943
  have hstable : (prefixWord ++ tailWord_5760943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760943).length < 2 ^ (prefixWord ++ tailWord_5760943).sum := by decide
  have hdescent : baseEnd_5760943 < baseStart_5760943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760954 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2]
def baseStart_5760954 : Nat := 118140960795 + 5760954 * 2 ^ 59
def prefixEnd_5760954 : Nat := 4983230072969 + 3 ^ 40 * 5760954 * 2
def baseEnd_5760954 : Nat := 2958138430441958474680861

theorem tailTrace_5760954 : CollatzResearch.WordTrace tailWord_5760954 prefixEnd_5760954 2958138430441958474680861 := by
  unfold tailWord_5760954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52529813592763756364154479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140079502914036683637745277 52529813592763756364154479)
  ·
    refine ⟨78794720389145634546231719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52529813592763756364154479 78794720389145634546231719)
    ·
      refine ⟨118192080583718451819347579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78794720389145634546231719 118192080583718451819347579)
      ·
        refine ⟨177288120875577677729021369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118192080583718451819347579 177288120875577677729021369)
        ·
          refine ⟨132966090656683258296766027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177288120875577677729021369 132966090656683258296766027)
          ·
            refine ⟨199449135985024887445149041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132966090656683258296766027 199449135985024887445149041)
            ·
              refine ⟨149586851988768665583861781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199449135985024887445149041 149586851988768665583861781)
              ·
                refine ⟨7011883686973531199243521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149586851988768665583861781 7011883686973531199243521)
                ·
                  refine ⟨5258912765230148399432641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7011883686973531199243521 5258912765230148399432641)
                  ·
                    refine ⟨3944184573922611299574481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258912765230148399432641 3944184573922611299574481)
                    ·
                      refine ⟨2958138430441958474680861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944184573922611299574481 2958138430441958474680861)
                      ·
                        rfl

theorem cell23_5760954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_5760954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760954 prefixEnd_5760954 := by exact prefixLift 5760954
  have htrace : WordTrace (prefixWord ++ tailWord_5760954) baseStart_5760954 baseEnd_5760954 := by
    simpa [prefixWord, tailWord_5760954, baseEnd_5760954] using wordTrace_append hprefix tailTrace_5760954
  have hstable : (prefixWord ++ tailWord_5760954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760954).length < 2 ^ (prefixWord ++ tailWord_5760954).sum := by decide
  have hdescent : baseEnd_5760954 < baseStart_5760954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760960 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 7]
def baseStart_5760960 : Nat := 118140960795 + 5760960 * 2 ^ 59
def prefixEnd_5760960 : Nat := 4983230072969 + 3 ^ 40 * 5760960 * 2
def baseEnd_5760960 : Nat := 328682390147320605689537

theorem tailTrace_5760960 : CollatzResearch.WordTrace tailWord_5760960 prefixEnd_5760960 328682390147320605689537 := by
  unfold tailWord_5760960
  simp only [CollatzResearch.WordTrace]
  refine ⟨105059736604516644240668167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140079648806022192320890889 105059736604516644240668167)
  ·
    refine ⟨157589604906774966361002251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105059736604516644240668167 157589604906774966361002251)
    ·
      refine ⟨236384407360162449541503377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157589604906774966361002251 236384407360162449541503377)
      ·
        refine ⟨177288305520121837156127533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236384407360162449541503377 177288305520121837156127533)
        ·
          refine ⟨66483114570045688933547825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177288305520121837156127533 66483114570045688933547825)
          ·
            refine ⟨49862335927534266700160869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66483114570045688933547825 49862335927534266700160869)
            ·
              refine ⟨9349187986412675006280163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49862335927534266700160869 9349187986412675006280163)
              ·
                refine ⟨14023781979619012509420245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9349187986412675006280163 14023781979619012509420245)
                ·
                  refine ⟨328682390147320605689537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14023781979619012509420245 328682390147320605689537)
                  ·
                    rfl

theorem cell23_5760960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_5760960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760960 prefixEnd_5760960 := by exact prefixLift 5760960
  have htrace : WordTrace (prefixWord ++ tailWord_5760960) baseStart_5760960 baseEnd_5760960 := by
    simpa [prefixWord, tailWord_5760960, baseEnd_5760960] using wordTrace_append hprefix tailTrace_5760960
  have hstable : (prefixWord ++ tailWord_5760960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760960).length < 2 ^ (prefixWord ++ tailWord_5760960).sum := by decide
  have hdescent : baseEnd_5760960 < baseStart_5760960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760963 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_5760963 : Nat := 118140960795 + 5760963 * 2 ^ 59
def prefixEnd_5760963 : Nat := 4983230072969 + 3 ^ 40 * 5760963 * 2
def baseEnd_5760963 : Nat := 2958143051767848939468319

theorem tailTrace_5760963 : CollatzResearch.WordTrace tailWord_5760963 prefixEnd_5760963 2958143051767848939468319 := by
  unfold tailWord_5760963
  simp only [CollatzResearch.WordTrace]
  refine ⟨210119582628022419993695543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140079721752014946662463695 210119582628022419993695543)
  ·
    refine ⟨315179373942033629990543315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210119582628022419993695543 315179373942033629990543315)
    ·
      refine ⟨472769060913050444985814973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315179373942033629990543315 472769060913050444985814973)
      ·
        refine ⟨177288397842393916869680615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472769060913050444985814973 177288397842393916869680615)
        ·
          refine ⟨265932596763590875304520923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177288397842393916869680615 265932596763590875304520923)
          ·
            refine ⟨398898895145386312956781385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265932596763590875304520923 398898895145386312956781385)
            ·
              refine ⟨299174171359039734717586039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398898895145386312956781385 299174171359039734717586039)
              ·
                refine ⟨448761257038559602076379059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299174171359039734717586039 448761257038559602076379059)
                ·
                  refine ⟨673141885557839403114568589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448761257038559602076379059 673141885557839403114568589)
                  ·
                    refine ⟨252428207084189776167963221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673141885557839403114568589 252428207084189776167963221)
                    ·
                      refine ⟨2958143051767848939468319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 252428207084189776167963221 2958143051767848939468319)
                      ·
                        rfl

theorem cell23_5760963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_5760963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760963 prefixEnd_5760963 := by exact prefixLift 5760963
  have htrace : WordTrace (prefixWord ++ tailWord_5760963) baseStart_5760963 baseEnd_5760963 := by
    simpa [prefixWord, tailWord_5760963, baseEnd_5760963] using wordTrace_append hprefix tailTrace_5760963
  have hstable : (prefixWord ++ tailWord_5760963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760963).length < 2 ^ (prefixWord ++ tailWord_5760963).sum := by decide
  have hdescent : baseEnd_5760963 < baseStart_5760963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5760971 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 2, 2, 2]
def baseStart_5760971 : Nat := 118140960795 + 5760971 * 2 ^ 59
def prefixEnd_5760971 : Nat := 4983230072969 + 3 ^ 40 * 5760971 * 2
def baseEnd_5760971 : Nat := 2958147159613084908168283

theorem tailTrace_5760971 : CollatzResearch.WordTrace tailWord_5760971 prefixEnd_5760971 2958147159613084908168283 := by
  unfold tailWord_5760971
  simp only [CollatzResearch.WordTrace]
  refine ⟨210119874411993437359986767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140079916274662291573324511 210119874411993437359986767)
  ·
    refine ⟨315179811617990156039980151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210119874411993437359986767 315179811617990156039980151)
    ·
      refine ⟨472769717426985234059970227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315179811617990156039980151 472769717426985234059970227)
      ·
        refine ⟨709154576140477851089955341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472769717426985234059970227 709154576140477851089955341)
        ·
          refine ⟨265932966052679194158733253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709154576140477851089955341 265932966052679194158733253)
          ·
            refine ⟨49862431134877348904762485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265932966052679194158733253 49862431134877348904762485)
            ·
              refine ⟨4674602918894751459821483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49862431134877348904762485 4674602918894751459821483)
              ·
                refine ⟨7011904378342127189732225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674602918894751459821483 7011904378342127189732225)
                ·
                  refine ⟨5258928283756595392299169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7011904378342127189732225 5258928283756595392299169)
                  ·
                    refine ⟨3944196212817446544224377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5258928283756595392299169 3944196212817446544224377)
                    ·
                      refine ⟨2958147159613084908168283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944196212817446544224377 2958147159613084908168283)
                      ·
                        rfl

theorem cell23_5760971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 2, 2].length) (baseStart_5760971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5760971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5760971 prefixEnd_5760971 := by exact prefixLift 5760971
  have htrace : WordTrace (prefixWord ++ tailWord_5760971) baseStart_5760971 baseEnd_5760971 := by
    simpa [prefixWord, tailWord_5760971, baseEnd_5760971] using wordTrace_append hprefix tailTrace_5760971
  have hstable : (prefixWord ++ tailWord_5760971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5760971).length < 2 ^ (prefixWord ++ tailWord_5760971).sum := by decide
  have hdescent : baseEnd_5760971 < baseStart_5760971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5760971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761000 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5761000 : Nat := 118140960795 + 5761000 * 2 ^ 59
def prefixEnd_5761000 : Nat := 4983230072969 + 3 ^ 40 * 5761000 * 2
def baseEnd_5761000 : Nat := 2958162050552065294705649

theorem tailTrace_5761000 : CollatzResearch.WordTrace tailWord_5761000 prefixEnd_5761000 2958162050552065294705649 := by
  unfold tailWord_5761000
  simp only [CollatzResearch.WordTrace]
  refine ⟨105060466064444187656396227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140080621419258916875194969 105060466064444187656396227)
  ·
    refine ⟨157590699096666281484594341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105060466064444187656396227 157590699096666281484594341)
    ·
      refine ⟨29548256080624927778361439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157590699096666281484594341 29548256080624927778361439)
      ·
        refine ⟨44322384120937391667542159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29548256080624927778361439 44322384120937391667542159)
        ·
          refine ⟨66483576181406087501313239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44322384120937391667542159 66483576181406087501313239)
          ·
            refine ⟨99725364272109131251969859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66483576181406087501313239 99725364272109131251969859)
            ·
              refine ⟨149588046408163696877954789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99725364272109131251969859 149588046408163696877954789)
              ·
                refine ⟨28047758701530693164616523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149588046408163696877954789 28047758701530693164616523)
                ·
                  refine ⟨42071638052296039746924785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28047758701530693164616523 42071638052296039746924785)
                  ·
                    refine ⟨31553728539222029810193589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42071638052296039746924785 31553728539222029810193589)
                    ·
                      refine ⟨2958162050552065294705649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31553728539222029810193589 2958162050552065294705649)
                      ·
                        rfl

theorem cell23_5761000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5761000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761000 prefixEnd_5761000 := by exact prefixLift 5761000
  have htrace : WordTrace (prefixWord ++ tailWord_5761000) baseStart_5761000 baseEnd_5761000 := by
    simpa [prefixWord, tailWord_5761000, baseEnd_5761000] using wordTrace_append hprefix tailTrace_5761000
  have hstable : (prefixWord ++ tailWord_5761000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761000).length < 2 ^ (prefixWord ++ tailWord_5761000).sum := by decide
  have hdescent : baseEnd_5761000 < baseStart_5761000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761027 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 4, 2]
def baseStart_5761027 : Nat := 118140960795 + 5761027 * 2 ^ 59
def prefixEnd_5761027 : Nat := 4983230072969 + 3 ^ 40 * 5761027 * 2
def baseEnd_5761027 : Nat := 2958175914529736689068025

theorem tailTrace_5761027 : CollatzResearch.WordTrace tailWord_5761027 prefixEnd_5761027 2958175914529736689068025 := by
  unfold tailWord_5761027
  simp only [CollatzResearch.WordTrace]
  refine ⟨210121916899790558924025335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140081277933193705949350223 210121916899790558924025335)
  ·
    refine ⟨315182875349685838386038003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210121916899790558924025335 315182875349685838386038003)
    ·
      refine ⟨472774313024528757579057005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315182875349685838386038003 472774313024528757579057005)
      ·
        refine ⟨177290367384198284092146377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472774313024528757579057005 177290367384198284092146377)
        ·
          refine ⟨132967775538148713069109783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177290367384198284092146377 132967775538148713069109783)
          ·
            refine ⟨199451663307223069603664675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132967775538148713069109783 199451663307223069603664675)
            ·
              refine ⟨299177494960834604405497013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199451663307223069603664675 299177494960834604405497013)
              ·
                refine ⟨28047890152578244163015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299177494960834604405497013 28047890152578244163015345)
                ·
                  refine ⟨21035917614433683122261509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28047890152578244163015345 21035917614433683122261509)
                  ·
                    refine ⟨3944234552706315585424033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21035917614433683122261509 3944234552706315585424033)
                    ·
                      refine ⟨2958175914529736689068025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944234552706315585424033 2958175914529736689068025)
                      ·
                        rfl

theorem cell23_5761027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_5761027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761027 prefixEnd_5761027 := by exact prefixLift 5761027
  have htrace : WordTrace (prefixWord ++ tailWord_5761027) baseStart_5761027 baseEnd_5761027 := by
    simpa [prefixWord, tailWord_5761027, baseEnd_5761027] using wordTrace_append hprefix tailTrace_5761027
  have hstable : (prefixWord ++ tailWord_5761027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761027).length < 2 ^ (prefixWord ++ tailWord_5761027).sum := by decide
  have hdescent : baseEnd_5761027 < baseStart_5761027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761097 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 1, 5]
def baseStart_5761097 : Nat := 118140960795 + 5761097 * 2 ^ 59
def prefixEnd_5761097 : Nat := 4983230072969 + 3 ^ 40 * 5761097 * 2
def baseEnd_5761097 : Nat := 986070619391850471730901

theorem tailTrace_5761097 : CollatzResearch.WordTrace tailWord_5761097 prefixEnd_5761097 986070619391850471730901 := by
  unfold tailWord_5761097
  simp only [CollatzResearch.WordTrace]
  refine ⟨210124470009536960879073545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140082980006357973919382363 210124470009536960879073545)
  ·
    refine ⟨157593352507152720659305159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210124470009536960879073545 157593352507152720659305159)
    ·
      refine ⟨236390028760729080988957739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157593352507152720659305159 236390028760729080988957739)
      ·
        refine ⟨354585043141093621483436609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236390028760729080988957739 354585043141093621483436609)
        ·
          refine ⟨265938782355820216112577457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354585043141093621483436609 265938782355820216112577457)
          ·
            refine ⟨199454086766865162084433093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265938782355820216112577457 199454086766865162084433093)
            ·
              refine ⟨37397641268787217890831205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199454086766865162084433093 37397641268787217890831205)
              ·
                refine ⟨7012057737897603354530851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37397641268787217890831205 7012057737897603354530851)
                ·
                  refine ⟨10518086606846405031796277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012057737897603354530851 10518086606846405031796277)
                  ·
                    refine ⟨986070619391850471730901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10518086606846405031796277 986070619391850471730901)
                    ·
                      rfl

theorem cell23_5761097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_5761097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761097 prefixEnd_5761097 := by exact prefixLift 5761097
  have htrace : WordTrace (prefixWord ++ tailWord_5761097) baseStart_5761097 baseEnd_5761097 := by
    simpa [prefixWord, tailWord_5761097, baseEnd_5761097] using wordTrace_append hprefix tailTrace_5761097
  have hstable : (prefixWord ++ tailWord_5761097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761097).length < 2 ^ (prefixWord ++ tailWord_5761097).sum := by decide
  have hdescent : baseEnd_5761097 < baseStart_5761097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761111 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_5761111 : Nat := 118140960795 + 5761111 * 2 ^ 59
def prefixEnd_5761111 : Nat := 4983230072969 + 3 ^ 40 * 5761111 * 2
def baseEnd_5761111 : Nat := 2958219046904714360417639

theorem tailTrace_5761111 : CollatzResearch.WordTrace tailWord_5761111 prefixEnd_5761111 2958219046904714360417639 := by
  unfold tailWord_5761111
  simp only [CollatzResearch.WordTrace]
  refine ⟨210124980631486241270083187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140083320420990827513388791 210124980631486241270083187)
  ·
    refine ⟨315187470947229361905124781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210124980631486241270083187 315187470947229361905124781)
    ·
      refine ⟨118195301605211010714421793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315187470947229361905124781 118195301605211010714421793)
      ·
        refine ⟨88646476203908258035816345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118195301605211010714421793 88646476203908258035816345)
        ·
          refine ⟨66484857152931193526862259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88646476203908258035816345 66484857152931193526862259)
          ·
            refine ⟨99727285729396790290293389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66484857152931193526862259 99727285729396790290293389)
            ·
              refine ⟨37397732148523796358860021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99727285729396790290293389 37397732148523796358860021)
              ·
                refine ⟨3506037388924105908643127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37397732148523796358860021 3506037388924105908643127)
                ·
                  refine ⟨5259056083386158862964691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506037388924105908643127 5259056083386158862964691)
                  ·
                    refine ⟨7888584125079238294447037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5259056083386158862964691 7888584125079238294447037)
                    ·
                      refine ⟨2958219046904714360417639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888584125079238294447037 2958219046904714360417639)
                      ·
                        rfl

theorem cell23_5761111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_5761111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761111 prefixEnd_5761111 := by exact prefixLift 5761111
  have htrace : WordTrace (prefixWord ++ tailWord_5761111) baseStart_5761111 baseEnd_5761111 := by
    simpa [prefixWord, tailWord_5761111, baseEnd_5761111] using wordTrace_append hprefix tailTrace_5761111
  have hstable : (prefixWord ++ tailWord_5761111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761111).length < 2 ^ (prefixWord ++ tailWord_5761111).sum := by decide
  have hdescent : baseEnd_5761111 < baseStart_5761111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761137 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_5761137 : Nat := 118140960795 + 5761137 * 2 ^ 59
def prefixEnd_5761137 : Nat := 4983230072969 + 3 ^ 40 * 5761137 * 2
def baseEnd_5761137 : Nat := 2958232397401731258692519

theorem tailTrace_5761137 : CollatzResearch.WordTrace tailWord_5761137 prefixEnd_5761137 2958232397401731258692519 := by
  unfold tailWord_5761137
  simp only [CollatzResearch.WordTrace]
  refine ⟨210125928929392047710529665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140083952619594698473686443 210125928929392047710529665)
  ·
    refine ⟨157594446697044035782897249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210125928929392047710529665 157594446697044035782897249)
    ·
      refine ⟨118195835022783026837172937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157594446697044035782897249 118195835022783026837172937)
      ·
        refine ⟨88646876267087270127879703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118195835022783026837172937 88646876267087270127879703)
        ·
          refine ⟨132970314400630905191819555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88646876267087270127879703 132970314400630905191819555)
          ·
            refine ⟨199455471600946357787729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132970314400630905191819555 199455471600946357787729333)
            ·
              refine ⟨18698950462588721042599625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199455471600946357787729333 18698950462588721042599625)
              ·
                refine ⟨14024212846941540781949719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18698950462588721042599625 14024212846941540781949719)
                ·
                  refine ⟨21036319270412311172924579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14024212846941540781949719 21036319270412311172924579)
                  ·
                    refine ⟨31554478905618466759386869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21036319270412311172924579 31554478905618466759386869)
                    ·
                      refine ⟨2958232397401731258692519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31554478905618466759386869 2958232397401731258692519)
                      ·
                        rfl

theorem cell23_5761137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_5761137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761137 prefixEnd_5761137 := by exact prefixLift 5761137
  have htrace : WordTrace (prefixWord ++ tailWord_5761137) baseStart_5761137 baseEnd_5761137 := by
    simpa [prefixWord, tailWord_5761137, baseEnd_5761137] using wordTrace_append hprefix tailTrace_5761137
  have hstable : (prefixWord ++ tailWord_5761137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761137).length < 2 ^ (prefixWord ++ tailWord_5761137).sum := by decide
  have hdescent : baseEnd_5761137 < baseStart_5761137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761157 : List Nat := [1, 3, 1, 1, 5, 2, 1, 9]
def baseStart_5761157 : Nat := 118140960795 + 5761157 * 2 ^ 59
def prefixEnd_5761157 : Nat := 4983230072969 + 3 ^ 40 * 5761157 * 2
def baseEnd_5761157 : Nat := 109564543222771154831201

theorem tailTrace_5761157 : CollatzResearch.WordTrace tailWord_5761157 prefixEnd_5761157 109564543222771154831201 := by
  unfold tailWord_5761157
  simp only [CollatzResearch.WordTrace]
  refine ⟨210126658389319591126257725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140084438926213060750838483 210126658389319591126257725)
  ·
    refine ⟨78797496895994846672346647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210126658389319591126257725 78797496895994846672346647)
    ·
      refine ⟨118196245343992270008519971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78797496895994846672346647 118196245343992270008519971)
      ·
        refine ⟨177294368015988405012779957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118196245343992270008519971 177294368015988405012779957)
        ·
          refine ⟨16621347001498912969948121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177294368015988405012779957 16621347001498912969948121)
          ·
            refine ⟨12466010251124184727461091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16621347001498912969948121 12466010251124184727461091)
            ·
              refine ⟨18699015376686277091191637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466010251124184727461091 18699015376686277091191637)
              ·
                refine ⟨109564543222771154831201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18699015376686277091191637 109564543222771154831201)
                ·
                  rfl

theorem cell23_5761157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 9].length) (baseStart_5761157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761157 prefixEnd_5761157 := by exact prefixLift 5761157
  have htrace : WordTrace (prefixWord ++ tailWord_5761157) baseStart_5761157 baseEnd_5761157 := by
    simpa [prefixWord, tailWord_5761157, baseEnd_5761157] using wordTrace_append hprefix tailTrace_5761157
  have hstable : (prefixWord ++ tailWord_5761157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761157).length < 2 ^ (prefixWord ++ tailWord_5761157).sum := by decide
  have hdescent : baseEnd_5761157 < baseStart_5761157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761205 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5761205 : Nat := 118140960795 + 5761205 * 2 ^ 59
def prefixEnd_5761205 : Nat := 4983230072969 + 3 ^ 40 * 5761205 * 2
def baseEnd_5761205 : Nat := 2958267314086236992642207

theorem tailTrace_5761205 : CollatzResearch.WordTrace tailWord_5761205 prefixEnd_5761205 2958267314086236992642207 := by
  unfold tailWord_5761205
  simp only [CollatzResearch.WordTrace]
  refine ⟨210128409093145695324005069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140085606062097130216003379 210128409093145695324005069)
  ·
    refine ⟨78798153409929635746501901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210128409093145695324005069 78798153409929635746501901)
    ·
      refine ⟨29549307528723613404938213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78798153409929635746501901 29549307528723613404938213)
      ·
        refine ⟨5540495161635677513425915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29549307528723613404938213 5540495161635677513425915)
        ·
          refine ⟨8310742742453516270138873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540495161635677513425915 8310742742453516270138873)
          ·
            refine ⟨6233057056840137202604155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8310742742453516270138873 6233057056840137202604155)
            ·
              refine ⟨9349585585260205803906233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233057056840137202604155 9349585585260205803906233)
              ·
                refine ⟨7012189188945154352929675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9349585585260205803906233 7012189188945154352929675)
                ·
                  refine ⟨10518283783417731529394513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012189188945154352929675 10518283783417731529394513)
                  ·
                    refine ⟨7888712837563298647045885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10518283783417731529394513 7888712837563298647045885)
                    ·
                      refine ⟨2958267314086236992642207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888712837563298647045885 2958267314086236992642207)
                      ·
                        rfl

theorem cell23_5761205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5761205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761205 prefixEnd_5761205 := by exact prefixLift 5761205
  have htrace : WordTrace (prefixWord ++ tailWord_5761205) baseStart_5761205 baseEnd_5761205 := by
    simpa [prefixWord, tailWord_5761205, baseEnd_5761205] using wordTrace_append hprefix tailTrace_5761205
  have hstable : (prefixWord ++ tailWord_5761205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761205).length < 2 ^ (prefixWord ++ tailWord_5761205).sum := by decide
  have hdescent : baseEnd_5761205 < baseStart_5761205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761218 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5761218 : Nat := 118140960795 + 5761218 * 2 ^ 59
def prefixEnd_5761218 : Nat := 4983230072969 + 3 ^ 40 * 5761218 * 2
def baseEnd_5761218 : Nat := 2958273989334745441779647

theorem tailTrace_5761218 : CollatzResearch.WordTrace tailWord_5761218 prefixEnd_5761218 2958273989334745441779647 := by
  unfold tailWord_5761218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532220810524649636057077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140085922161399065696152205 52532220810524649636057077)
  ·
    refine ⟨4924895700986685903380351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52532220810524649636057077 4924895700986685903380351)
    ·
      refine ⟨7387343551480028855070527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924895700986685903380351 7387343551480028855070527)
      ·
        refine ⟨11081015327220043282605791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387343551480028855070527 11081015327220043282605791)
        ·
          refine ⟨16621522990830064923908687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081015327220043282605791 16621522990830064923908687)
          ·
            refine ⟨24932284486245097385863031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16621522990830064923908687 24932284486245097385863031)
            ·
              refine ⟨37398426729367646078794547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24932284486245097385863031 37398426729367646078794547)
              ·
                refine ⟨56097640094051469118191821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37398426729367646078794547 56097640094051469118191821)
                ·
                  refine ⟨21036615035269300919321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56097640094051469118191821 21036615035269300919321933)
                  ·
                    refine ⟨7888730638225987844745725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21036615035269300919321933 7888730638225987844745725)
                    ·
                      refine ⟨2958273989334745441779647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888730638225987844745725 2958273989334745441779647)
                      ·
                        rfl

theorem cell23_5761218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5761218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761218 prefixEnd_5761218 := by exact prefixLift 5761218
  have htrace : WordTrace (prefixWord ++ tailWord_5761218) baseStart_5761218 baseEnd_5761218 := by
    simpa [prefixWord, tailWord_5761218, baseEnd_5761218] using wordTrace_append hprefix tailTrace_5761218
  have hstable : (prefixWord ++ tailWord_5761218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761218).length < 2 ^ (prefixWord ++ tailWord_5761218).sum := by decide
  have hdescent : baseEnd_5761218 < baseStart_5761218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761227 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_5761227 : Nat := 118140960795 + 5761227 * 2 ^ 59
def prefixEnd_5761227 : Nat := 4983230072969 + 3 ^ 40 * 5761227 * 2
def baseEnd_5761227 : Nat := 2958278610660635906567105

theorem tailTrace_5761227 : CollatzResearch.WordTrace tailWord_5761227 prefixEnd_5761227 2958278610660635906567105 := by
  unfold tailWord_5761227
  simp only [CollatzResearch.WordTrace]
  refine ⟨210129211499065993081305935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140086140999377328720870623 210129211499065993081305935)
  ·
    refine ⟨315193817248598989621958903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210129211499065993081305935 315193817248598989621958903)
    ·
      refine ⟨472790725872898484432938355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315193817248598989621958903 472790725872898484432938355)
      ·
        refine ⟨709186088809347726649407533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472790725872898484432938355 709186088809347726649407533)
        ·
          refine ⟨265944783303505397493527825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709186088809347726649407533 265944783303505397493527825)
          ·
            refine ⟨199458587477629048120145869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265944783303505397493527825 199458587477629048120145869)
            ·
              refine ⟨74796970304110893045054701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199458587477629048120145869 74796970304110893045054701)
              ·
                refine ⟨28048863864041584891895513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74796970304110893045054701 28048863864041584891895513)
                ·
                  refine ⟨21036647898031188668921635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28048863864041584891895513 21036647898031188668921635)
                  ·
                    refine ⟨31554971847046783003382453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21036647898031188668921635 31554971847046783003382453)
                    ·
                      refine ⟨2958278610660635906567105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31554971847046783003382453 2958278610660635906567105)
                      ·
                        rfl

theorem cell23_5761227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_5761227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761227 prefixEnd_5761227 := by exact prefixLift 5761227
  have htrace : WordTrace (prefixWord ++ tailWord_5761227) baseStart_5761227 baseEnd_5761227 := by
    simpa [prefixWord, tailWord_5761227, baseEnd_5761227] using wordTrace_append hprefix tailTrace_5761227
  have hstable : (prefixWord ++ tailWord_5761227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761227).length < 2 ^ (prefixWord ++ tailWord_5761227).sum := by decide
  have hdescent : baseEnd_5761227 < baseStart_5761227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761241 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 4, 2, 2]
def baseStart_5761241 : Nat := 118140960795 + 5761241 * 2 ^ 59
def prefixEnd_5761241 : Nat := 4983230072969 + 3 ^ 40 * 5761241 * 2
def baseEnd_5761241 : Nat := 2958285799389798851792041

theorem tailTrace_5761241 : CollatzResearch.WordTrace tailWord_5761241 prefixEnd_5761241 2958285799389798851792041 := by
  unfold tailWord_5761241
  simp only [CollatzResearch.WordTrace]
  refine ⟨210129722121015273472315577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140086481414010182314877051 210129722121015273472315577)
  ·
    refine ⟨157597291590761455104236683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210129722121015273472315577 157597291590761455104236683)
    ·
      refine ⟨236395937386142182656355025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157597291590761455104236683 236395937386142182656355025)
      ·
        refine ⟨177296953039606636992266269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236395937386142182656355025 177296953039606636992266269)
        ·
          refine ⟨66486357389852488872099851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177296953039606636992266269 66486357389852488872099851)
          ·
            refine ⟨99729536084778733308149777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66486357389852488872099851 99729536084778733308149777)
            ·
              refine ⟨74797152063584049981112333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99729536084778733308149777 74797152063584049981112333)
              ·
                refine ⟨28048932023844018742917125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74797152063584049981112333 28048932023844018742917125)
                ·
                  refine ⟨5259174754470753514296961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28048932023844018742917125 5259174754470753514296961)
                  ·
                    refine ⟨3944381065853065135722721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259174754470753514296961 3944381065853065135722721)
                    ·
                      refine ⟨2958285799389798851792041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944381065853065135722721 2958285799389798851792041)
                      ·
                        rfl

theorem cell23_5761241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_5761241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761241 prefixEnd_5761241 := by exact prefixLift 5761241
  have htrace : WordTrace (prefixWord ++ tailWord_5761241) baseStart_5761241 baseEnd_5761241 := by
    simpa [prefixWord, tailWord_5761241, baseEnd_5761241] using wordTrace_append hprefix tailTrace_5761241
  have hstable : (prefixWord ++ tailWord_5761241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761241).length < 2 ^ (prefixWord ++ tailWord_5761241).sum := by decide
  have hdescent : baseEnd_5761241 < baseStart_5761241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761247 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 7]
def baseStart_5761247 : Nat := 118140960795 + 5761247 * 2 ^ 59
def prefixEnd_5761247 : Nat := 4983230072969 + 3 ^ 40 * 5761247 * 2
def baseEnd_5761247 : Nat := 328698764474858425368557

theorem tailTrace_5761247 : CollatzResearch.WordTrace tailWord_5761247 prefixEnd_5761247 328698764474858425368557 := by
  unfold tailWord_5761247
  simp only [CollatzResearch.WordTrace]
  refine ⟨210129940958993536497033995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140086627305995690998022663 210129940958993536497033995)
  ·
    refine ⟨315194911438490304745550993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210129940958993536497033995 315194911438490304745550993)
    ·
      refine ⟨236396183578867728559163245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315194911438490304745550993 236396183578867728559163245)
      ·
        refine ⟨88648568842075398209686217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236396183578867728559163245 88648568842075398209686217)
        ·
          refine ⟨66486426631556548657264663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88648568842075398209686217 66486426631556548657264663)
          ·
            refine ⟨99729639947334822985896995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66486426631556548657264663 99729639947334822985896995)
            ·
              refine ⟨149594459921002234478845493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99729639947334822985896995 149594459921002234478845493)
              ·
                refine ⟨14024480617593959482391765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149594459921002234478845493 14024480617593959482391765)
                ·
                  refine ⟨328698764474858425368557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14024480617593959482391765 328698764474858425368557)
                  ·
                    rfl

theorem cell23_5761247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 7].length) (baseStart_5761247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761247 prefixEnd_5761247 := by exact prefixLift 5761247
  have htrace : WordTrace (prefixWord ++ tailWord_5761247) baseStart_5761247 baseEnd_5761247 := by
    simpa [prefixWord, tailWord_5761247, baseEnd_5761247] using wordTrace_append hprefix tailTrace_5761247
  have hstable : (prefixWord ++ tailWord_5761247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761247).length < 2 ^ (prefixWord ++ tailWord_5761247).sum := by decide
  have hdescent : baseEnd_5761247 < baseStart_5761247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761251 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 6]
def baseStart_5761251 : Nat := 118140960795 + 5761251 * 2 ^ 59
def prefixEnd_5761251 : Nat := 4983230072969 + 3 ^ 40 * 5761251 * 2
def baseEnd_5761251 : Nat := 986096978065447937555665

theorem tailTrace_5761251 : CollatzResearch.WordTrace tailWord_5761251 prefixEnd_5761251 986096978065447937555665 := by
  unfold tailWord_5761251
  simp only [CollatzResearch.WordTrace]
  refine ⟨210130086850979045180179607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140086724567319363453453071 210130086850979045180179607)
  ·
    refine ⟨315195130276468567770269411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210130086850979045180179607 315195130276468567770269411)
    ·
      refine ⟨472792695414702851655404117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315195130276468567770269411 472792695414702851655404117)
      ·
        refine ⟨5540539399391049042836767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 472792695414702851655404117 5540539399391049042836767)
        ·
          refine ⟨8310809099086573564255151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540539399391049042836767 8310809099086573564255151)
          ·
            refine ⟨12466213648629860346382727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310809099086573564255151 12466213648629860346382727)
            ·
              refine ⟨18699320472944790519574091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466213648629860346382727 18699320472944790519574091)
              ·
                refine ⟨28048980709417185779361137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18699320472944790519574091 28048980709417185779361137)
                ·
                  refine ⟨21036735532062889334520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28048980709417185779361137 21036735532062889334520853)
                  ·
                    refine ⟨986096978065447937555665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21036735532062889334520853 986096978065447937555665)
                    ·
                      rfl

theorem cell23_5761251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 6].length) (baseStart_5761251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761251 prefixEnd_5761251 := by exact prefixLift 5761251
  have htrace : WordTrace (prefixWord ++ tailWord_5761251) baseStart_5761251 baseEnd_5761251 := by
    simpa [prefixWord, tailWord_5761251, baseEnd_5761251] using wordTrace_append hprefix tailTrace_5761251
  have hstable : (prefixWord ++ tailWord_5761251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761251).length < 2 ^ (prefixWord ++ tailWord_5761251).sum := by decide
  have hdescent : baseEnd_5761251 < baseStart_5761251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761258 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_5761258 : Nat := 118140960795 + 5761258 * 2 ^ 59
def prefixEnd_5761258 : Nat := 4983230072969 + 3 ^ 40 * 5761258 * 2
def baseEnd_5761258 : Nat := 2958294528560925285279463

theorem tailTrace_5761258 : CollatzResearch.WordTrace tailWord_5761258 prefixEnd_5761258 2958294528560925285279463 := by
  unfold tailWord_5761258
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532585540488421343921107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140086894774635790250456285 52532585540488421343921107)
  ·
    refine ⟨78798878310732632015881661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52532585540488421343921107 78798878310732632015881661)
    ·
      refine ⟨29549579366524737005955623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78798878310732632015881661 29549579366524737005955623)
      ·
        refine ⟨44324369049787105508933435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29549579366524737005955623 44324369049787105508933435)
        ·
          refine ⟨66486553574680658263400153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44324369049787105508933435 66486553574680658263400153)
          ·
            refine ⟨49864915181010493697550115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66486553574680658263400153 49864915181010493697550115)
            ·
              refine ⟨74797372771515740546325173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49864915181010493697550115 74797372771515740546325173)
              ·
                refine ⟨7012253697329600676217985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74797372771515740546325173 7012253697329600676217985)
                ·
                  refine ⟨5259190272997200507163489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012253697329600676217985 5259190272997200507163489)
                  ·
                    refine ⟨3944392704747900380372617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259190272997200507163489 3944392704747900380372617)
                    ·
                      refine ⟨2958294528560925285279463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944392704747900380372617 2958294528560925285279463)
                      ·
                        rfl

theorem cell23_5761258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_5761258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761258 prefixEnd_5761258 := by exact prefixLift 5761258
  have htrace : WordTrace (prefixWord ++ tailWord_5761258) baseStart_5761258 baseEnd_5761258 := by
    simpa [prefixWord, tailWord_5761258, baseEnd_5761258] using wordTrace_append hprefix tailTrace_5761258
  have hstable : (prefixWord ++ tailWord_5761258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761258).length < 2 ^ (prefixWord ++ tailWord_5761258).sum := by decide
  have hdescent : baseEnd_5761258 < baseStart_5761258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761281 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 5]
def baseStart_5761281 : Nat := 118140960795 + 5761281 * 2 ^ 59
def prefixEnd_5761281 : Nat := 4983230072969 + 3 ^ 40 * 5761281 * 2
def baseEnd_5761281 : Nat := 328700704290664299476873

theorem tailTrace_5761281 : CollatzResearch.WordTrace tailWord_5761281 prefixEnd_5761281 328700704290664299476873 := by
  unfold tailWord_5761281
  simp only [CollatzResearch.WordTrace]
  refine ⟨210131181040870360303771697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140087454027246906869181131 210131181040870360303771697)
  ·
    refine ⟨157598385780652770227828773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210131181040870360303771697 157598385780652770227828773)
    ·
      refine ⟨29549697333872394417717895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157598385780652770227828773 29549697333872394417717895)
      ·
        refine ⟨44324546000808591626576843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29549697333872394417717895 44324546000808591626576843)
        ·
          refine ⟨66486819001212887439865265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44324546000808591626576843 66486819001212887439865265)
          ·
            refine ⟨49865114250909665579898949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66486819001212887439865265 49865114250909665579898949)
            ·
              refine ⟨9349708922045562296231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49865114250909665579898949 9349708922045562296231053)
              ·
                refine ⟨3506140845767085861086645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9349708922045562296231053 3506140845767085861086645)
                ·
                  refine ⟨328700704290664299476873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506140845767085861086645 328700704290664299476873)
                  ·
                    rfl

theorem cell23_5761281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 5].length) (baseStart_5761281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761281 prefixEnd_5761281 := by exact prefixLift 5761281
  have htrace : WordTrace (prefixWord ++ tailWord_5761281) baseStart_5761281 baseEnd_5761281 := by
    simpa [prefixWord, tailWord_5761281, baseEnd_5761281] using wordTrace_append hprefix tailTrace_5761281
  have hstable : (prefixWord ++ tailWord_5761281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761281).length < 2 ^ (prefixWord ++ tailWord_5761281).sum := by decide
  have hdescent : baseEnd_5761281 < baseStart_5761281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761294 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_5761294 : Nat := 118140960795 + 5761294 * 2 ^ 59
def prefixEnd_5761294 : Nat := 4983230072969 + 3 ^ 40 * 5761294 * 2
def baseEnd_5761294 : Nat := 986104337954829048143099

theorem tailTrace_5761294 : CollatzResearch.WordTrace tailWord_5761294 prefixEnd_5761294 986104337954829048143099 := by
  unfold tailWord_5761294
  simp only [CollatzResearch.WordTrace]
  refine ⟨26266456898727907940499367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140087770126548842349329957 26266456898727907940499367)
  ·
    refine ⟨39399685348091861910749051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26266456898727907940499367 39399685348091861910749051)
    ·
      refine ⟨59099528022137792866123577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39399685348091861910749051 59099528022137792866123577)
      ·
        refine ⟨44324646016603344649592683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59099528022137792866123577 44324646016603344649592683)
        ·
          refine ⟨66486969024905016974389025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44324646016603344649592683 66486969024905016974389025)
          ·
            refine ⟨49865226768678762730791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66486969024905016974389025 49865226768678762730791769)
            ·
              refine ⟨37398920076509072048093827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49865226768678762730791769 37398920076509072048093827)
              ·
                refine ⟨56098380114763608072140741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37398920076509072048093827 56098380114763608072140741)
                ·
                  refine ⟨10518446271518176513526389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56098380114763608072140741 10518446271518176513526389)
                  ·
                    refine ⟨986104337954829048143099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10518446271518176513526389 986104337954829048143099)
                    ·
                      rfl

theorem cell23_5761294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_5761294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761294 prefixEnd_5761294 := by exact prefixLift 5761294
  have htrace : WordTrace (prefixWord ++ tailWord_5761294) baseStart_5761294 baseEnd_5761294 := by
    simpa [prefixWord, tailWord_5761294, baseEnd_5761294] using wordTrace_append hprefix tailTrace_5761294
  have hstable : (prefixWord ++ tailWord_5761294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761294).length < 2 ^ (prefixWord ++ tailWord_5761294).sum := by decide
  have hdescent : baseEnd_5761294 < baseStart_5761294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761351 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_5761351 : Nat := 118140960795 + 5761351 * 2 ^ 59
def prefixEnd_5761351 : Nat := 4983230072969 + 3 ^ 40 * 5761351 * 2
def baseEnd_5761351 : Nat := 2958342282261793421416535

theorem tailTrace_5761351 : CollatzResearch.WordTrace tailWord_5761351 prefixEnd_5761351 2958342282261793421416535 := by
  unfold tailWord_5761351
  simp only [CollatzResearch.WordTrace]
  refine ⟨210133734150616762258819907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140089156100411174839213271 210133734150616762258819907)
  ·
    refine ⟨315200601225925143388229861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210133734150616762258819907 315200601225925143388229861)
    ·
      refine ⟨59100112729860964385293099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315200601225925143388229861 59100112729860964385293099)
      ·
        refine ⟨88650169094791446577939649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59100112729860964385293099 88650169094791446577939649)
        ·
          refine ⟨66487626821093584933454737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88650169094791446577939649 66487626821093584933454737)
          ·
            refine ⟨49865720115820188700091053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66487626821093584933454737 49865720115820188700091053)
            ·
              refine ⟨18699645043432570762534145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49865720115820188700091053 18699645043432570762534145)
              ·
                refine ⟨14024733782574428071900609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18699645043432570762534145 14024733782574428071900609)
                ·
                  refine ⟨10518550336930821053925457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14024733782574428071900609 10518550336930821053925457)
                  ·
                    refine ⟨7888912752698115790444093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10518550336930821053925457 7888912752698115790444093)
                    ·
                      refine ⟨2958342282261793421416535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7888912752698115790444093 2958342282261793421416535)
                      ·
                        rfl

theorem cell23_5761351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_5761351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761351 prefixEnd_5761351 := by exact prefixLift 5761351
  have htrace : WordTrace (prefixWord ++ tailWord_5761351) baseStart_5761351 baseEnd_5761351 := by
    simpa [prefixWord, tailWord_5761351, baseEnd_5761351] using wordTrace_append hprefix tailTrace_5761351
  have hstable : (prefixWord ++ tailWord_5761351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761351).length < 2 ^ (prefixWord ++ tailWord_5761351).sum := by decide
  have hdescent : baseEnd_5761351 < baseStart_5761351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761415 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_5761415 : Nat := 118140960795 + 5761415 * 2 ^ 59
def prefixEnd_5761415 : Nat := 4983230072969 + 3 ^ 40 * 5761415 * 2
def baseEnd_5761415 : Nat := 2958375145023681171016241

theorem tailTrace_5761415 : CollatzResearch.WordTrace tailWord_5761415 prefixEnd_5761415 2958375145023681171016241 := by
  unfold tailWord_5761415
  simp only [CollatzResearch.WordTrace]
  refine ⟨210136068422384901189149699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140090712281589934126099799 210136068422384901189149699)
  ·
    refine ⟨315204102633577351783724549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210136068422384901189149699 315204102633577351783724549)
    ·
      refine ⟨59100769243795753459448353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315204102633577351783724549 59100769243795753459448353)
      ·
        refine ⟨44325576932846815094586265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59100769243795753459448353 44325576932846815094586265)
        ·
          refine ⟨33244182699635111320939699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44325576932846815094586265 33244182699635111320939699)
          ·
            refine ⟨49866274049452666981409549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33244182699635111320939699 49866274049452666981409549)
            ·
              refine ⟨18699852768544750118028581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49866274049452666981409549 18699852768544750118028581)
              ·
                refine ⟨3506222394102140647130359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18699852768544750118028581 3506222394102140647130359)
                ·
                  refine ⟨5259333591153210970695539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506222394102140647130359 5259333591153210970695539)
                  ·
                    refine ⟨7889000386729816456043309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5259333591153210970695539 7889000386729816456043309)
                    ·
                      refine ⟨2958375145023681171016241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889000386729816456043309 2958375145023681171016241)
                      ·
                        rfl

theorem cell23_5761415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_5761415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761415 prefixEnd_5761415 := by exact prefixLift 5761415
  have htrace : WordTrace (prefixWord ++ tailWord_5761415) baseStart_5761415 baseEnd_5761415 := by
    simpa [prefixWord, tailWord_5761415, baseEnd_5761415] using wordTrace_append hprefix tailTrace_5761415
  have hstable : (prefixWord ++ tailWord_5761415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761415).length < 2 ^ (prefixWord ++ tailWord_5761415).sum := by decide
  have hdescent : baseEnd_5761415 < baseStart_5761415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761444 : List Nat := [2, 3, 1, 2, 1, 1, 2, 11]
def baseStart_5761444 : Nat := 118140960795 + 5761444 * 2 ^ 59
def prefixEnd_5761444 : Nat := 4983230072969 + 3 ^ 40 * 5761444 * 2
def baseEnd_5761444 : Nat := 109570001331950428057541

theorem tailTrace_5761444 : CollatzResearch.WordTrace tailWord_5761444 prefixEnd_5761444 109570001331950428057541 := by
  unfold tailWord_5761444
  simp only [CollatzResearch.WordTrace]
  refine ⟨105068563069639919570977693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140091417426186559427970257 105068563069639919570977693)
  ·
    refine ⟨39400711151114969839116635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105068563069639919570977693 39400711151114969839116635)
    ·
      refine ⟨59101066726672454758674953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39400711151114969839116635 59101066726672454758674953)
      ·
        refine ⟨44325800045004341069006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59101066726672454758674953 44325800045004341069006215)
        ·
          refine ⟨66488700067506511603509323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44325800045004341069006215 66488700067506511603509323)
          ·
            refine ⟨99733050101259767405263985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66488700067506511603509323 99733050101259767405263985)
            ·
              refine ⟨74799787575944825553947989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99733050101259767405263985 74799787575944825553947989)
              ·
                refine ⟨109570001331950428057541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74799787575944825553947989 109570001331950428057541)
                ·
                  rfl

theorem cell23_5761444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 11].length) (baseStart_5761444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761444 prefixEnd_5761444 := by exact prefixLift 5761444
  have htrace : WordTrace (prefixWord ++ tailWord_5761444) baseStart_5761444 baseEnd_5761444 := by
    simpa [prefixWord, tailWord_5761444, baseEnd_5761444] using wordTrace_append hprefix tailTrace_5761444
  have hstable : (prefixWord ++ tailWord_5761444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761444).length < 2 ^ (prefixWord ++ tailWord_5761444).sum := by decide
  have hdescent : baseEnd_5761444 < baseStart_5761444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761448 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5761448 : Nat := 118140960795 + 5761448 * 2 ^ 59
def prefixEnd_5761448 : Nat := 4983230072969 + 3 ^ 40 * 5761448 * 2
def baseEnd_5761448 : Nat := 986130696628426513967863

theorem tailTrace_5761448 : CollatzResearch.WordTrace tailWord_5761448 prefixEnd_5761448 986130696628426513967863 := by
  unfold tailWord_5761448
  simp only [CollatzResearch.WordTrace]
  refine ⟨105068636015632673912550499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140091514687510231883400665 105068636015632673912550499)
  ·
    refine ⟨157602954023449010868825749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105068636015632673912550499 157602954023449010868825749)
    ·
      refine ⟨7387638469849172384476207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157602954023449010868825749 7387638469849172384476207)
      ·
        refine ⟨11081457704773758576714311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387638469849172384476207 11081457704773758576714311)
        ·
          refine ⟨16622186557160637865071467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081457704773758576714311 16622186557160637865071467)
          ·
            refine ⟨24933279835740956797607201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16622186557160637865071467 24933279835740956797607201)
            ·
              refine ⟨18699959876805717598205401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24933279835740956797607201 18699959876805717598205401)
              ·
                refine ⟨14024969907604288198654051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18699959876805717598205401 14024969907604288198654051)
                ·
                  refine ⟨21037454861406432297981077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14024969907604288198654051 21037454861406432297981077)
                  ·
                    refine ⟨986130696628426513967863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21037454861406432297981077 986130696628426513967863)
                    ·
                      rfl

theorem cell23_5761448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5761448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761448 prefixEnd_5761448 := by exact prefixLift 5761448
  have htrace : WordTrace (prefixWord ++ tailWord_5761448) baseStart_5761448 baseEnd_5761448 := by
    simpa [prefixWord, tailWord_5761448, baseEnd_5761448] using wordTrace_append hprefix tailTrace_5761448
  have hstable : (prefixWord ++ tailWord_5761448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761448).length < 2 ^ (prefixWord ++ tailWord_5761448).sum := by decide
  have hdescent : baseEnd_5761448 < baseStart_5761448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761458 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_5761458 : Nat := 118140960795 + 5761458 * 2 ^ 59
def prefixEnd_5761458 : Nat := 4983230072969 + 3 ^ 40 * 5761458 * 2
def baseEnd_5761458 : Nat := 2958397224691824502778543

theorem tailTrace_5761458 : CollatzResearch.WordTrace tailWord_5761458 prefixEnd_5761458 2958397224691824502778543 := by
  unfold tailWord_5761458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52534409190307279883241257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140091757840819413021976685 52534409190307279883241257)
  ·
    refine ⟨39400806892730459912430943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52534409190307279883241257 39400806892730459912430943)
    ·
      refine ⟨59101210339095689868646415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39400806892730459912430943 59101210339095689868646415)
      ·
        refine ⟨88651815508643534802969623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59101210339095689868646415 88651815508643534802969623)
        ·
          refine ⟨132977723262965302204454435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88651815508643534802969623 132977723262965302204454435)
          ·
            refine ⟨199466584894447953306681653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132977723262965302204454435 199466584894447953306681653)
            ·
              refine ⟨18699992333854495622501405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199466584894447953306681653 18699992333854495622501405)
              ·
                refine ⟨7012497125195435858438027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18699992333854495622501405 7012497125195435858438027)
                ·
                  refine ⟨10518745687793153787657041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012497125195435858438027 10518745687793153787657041)
                  ·
                    refine ⟨7889059265844865340742781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10518745687793153787657041 7889059265844865340742781)
                    ·
                      refine ⟨2958397224691824502778543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889059265844865340742781 2958397224691824502778543)
                      ·
                        rfl

theorem cell23_5761458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_5761458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761458 prefixEnd_5761458 := by exact prefixLift 5761458
  have htrace : WordTrace (prefixWord ++ tailWord_5761458) baseStart_5761458 baseEnd_5761458 := by
    simpa [prefixWord, tailWord_5761458, baseEnd_5761458] using wordTrace_append hprefix tailTrace_5761458
  have hstable : (prefixWord ++ tailWord_5761458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761458).length < 2 ^ (prefixWord ++ tailWord_5761458).sum := by decide
  have hdescent : baseEnd_5761458 < baseStart_5761458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761461 : List Nat := [1, 3, 3, 2, 3, 1, 10]
def baseStart_5761461 : Nat := 118140960795 + 5761461 * 2 ^ 59
def prefixEnd_5761461 : Nat := 4983230072969 + 3 ^ 40 * 5761461 * 2
def baseEnd_5761461 : Nat := 36523441544861580136309

theorem tailTrace_5761461 : CollatzResearch.WordTrace tailWord_5761461 prefixEnd_5761461 36523441544861580136309 := by
  unfold tailWord_5761461
  simp only [CollatzResearch.WordTrace]
  refine ⟨210137746180218251045324237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140091830786812167363549491 210137746180218251045324237)
  ·
    refine ⟨78801654817581844141996589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210137746180218251045324237 78801654817581844141996589)
    ·
      refine ⟨29550620556593191553248721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78801654817581844141996589 29550620556593191553248721)
      ·
        refine ⟨22162965417444893664936541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29550620556593191553248721 22162965417444893664936541)
        ·
          refine ⟨8311112031541835124351203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22162965417444893664936541 8311112031541835124351203)
          ·
            refine ⟨12466668047312752686526805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8311112031541835124351203 12466668047312752686526805)
            ·
              refine ⟨36523441544861580136309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12466668047312752686526805 36523441544861580136309)
              ·
                rfl

theorem cell23_5761461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 10].length) (baseStart_5761461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761461 prefixEnd_5761461 := by exact prefixLift 5761461
  have htrace : WordTrace (prefixWord ++ tailWord_5761461) baseStart_5761461 baseEnd_5761461 := by
    simpa [prefixWord, tailWord_5761461, baseEnd_5761461] using wordTrace_append hprefix tailTrace_5761461
  have hstable : (prefixWord ++ tailWord_5761461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761461).length < 2 ^ (prefixWord ++ tailWord_5761461).sum := by decide
  have hdescent : baseEnd_5761461 < baseStart_5761461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761464 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_5761464 : Nat := 118140960795 + 5761464 * 2 ^ 59
def prefixEnd_5761464 : Nat := 4983230072969 + 3 ^ 40 * 5761464 * 2
def baseEnd_5761464 : Nat := 2958400305575751479303515

theorem tailTrace_5761464 : CollatzResearch.WordTrace tailWord_5761464 prefixEnd_5761464 2958400305575751479303515 := by
  unfold tailWord_5761464
  simp only [CollatzResearch.WordTrace]
  refine ⟨105068927799603691278841723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140091903732804921705122297 105068927799603691278841723)
  ·
    refine ⟨157603391699405536918262585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105068927799603691278841723 157603391699405536918262585)
    ·
      refine ⟨118202543774554152688696939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157603391699405536918262585 118202543774554152688696939)
      ·
        refine ⟨177303815661831229033045409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118202543774554152688696939 177303815661831229033045409)
        ·
          refine ⟨132977861746373421774784057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177303815661831229033045409 132977861746373421774784057)
          ·
            refine ⟨99733396309780066331088043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132977861746373421774784057 99733396309780066331088043)
            ·
              refine ⟨149600094464670099496632065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99733396309780066331088043 149600094464670099496632065)
              ·
                refine ⟨112200070848502574622474049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149600094464670099496632065 112200070848502574622474049)
                ·
                  refine ⟨84150053136376930966855537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112200070848502574622474049 84150053136376930966855537)
                  ·
                    refine ⟨63112539852282698225141653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84150053136376930966855537 63112539852282698225141653)
                    ·
                      refine ⟨2958400305575751479303515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63112539852282698225141653 2958400305575751479303515)
                      ·
                        rfl

theorem cell23_5761464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_5761464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761464 prefixEnd_5761464 := by exact prefixLift 5761464
  have htrace : WordTrace (prefixWord ++ tailWord_5761464) baseStart_5761464 baseEnd_5761464 := by
    simpa [prefixWord, tailWord_5761464, baseEnd_5761464] using wordTrace_append hprefix tailTrace_5761464
  have hstable : (prefixWord ++ tailWord_5761464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761464).length < 2 ^ (prefixWord ++ tailWord_5761464).sum := by decide
  have hdescent : baseEnd_5761464 < baseStart_5761464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761465 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 2, 4]
def baseStart_5761465 : Nat := 118140960795 + 5761465 * 2 ^ 59
def prefixEnd_5761465 : Nat := 4983230072969 + 3 ^ 40 * 5761465 * 2
def baseEnd_5761465 : Nat := 986133606352135325130337

theorem tailTrace_5761465 : CollatzResearch.WordTrace tailWord_5761465 prefixEnd_5761465 986133606352135325130337 := by
  unfold tailWord_5761465
  simp only [CollatzResearch.WordTrace]
  refine ⟨210137892072203759728469849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140091928048135839818979899 210137892072203759728469849)
  ·
    refine ⟨157603419054152819796352387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210137892072203759728469849 157603419054152819796352387)
    ·
      refine ⟨236405128581229229694528581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157603419054152819796352387 236405128581229229694528581)
      ·
        refine ⟨44325961608980480567724109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236405128581229229694528581 44325961608980480567724109)
        ·
          refine ⟨16622235603367680212896541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44325961608980480567724109 16622235603367680212896541)
          ·
            refine ⟨6233338351262880079836203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16622235603367680212896541 6233338351262880079836203)
            ·
              refine ⟨9350007526894320119754305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233338351262880079836203 9350007526894320119754305)
              ·
                refine ⟨7012505645170740089815729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350007526894320119754305 7012505645170740089815729)
                ·
                  refine ⟨5259379233878055067361797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012505645170740089815729 5259379233878055067361797)
                  ·
                    refine ⟨986133606352135325130337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259379233878055067361797 986133606352135325130337)
                    ·
                      rfl

theorem cell23_5761465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_5761465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761465 prefixEnd_5761465 := by exact prefixLift 5761465
  have htrace : WordTrace (prefixWord ++ tailWord_5761465) baseStart_5761465 baseEnd_5761465 := by
    simpa [prefixWord, tailWord_5761465, baseEnd_5761465] using wordTrace_append hprefix tailTrace_5761465
  have hstable : (prefixWord ++ tailWord_5761465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761465).length < 2 ^ (prefixWord ++ tailWord_5761465).sum := by decide
  have hdescent : baseEnd_5761465 < baseStart_5761465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761501 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5761501 : Nat := 118140960795 + 5761501 * 2 ^ 59
def prefixEnd_5761501 : Nat := 4983230072969 + 3 ^ 40 * 5761501 * 2
def baseEnd_5761501 : Nat := 2958419304359967834540845

theorem tailTrace_5761501 : CollatzResearch.WordTrace tailWord_5761501 prefixEnd_5761501 2958419304359967834540845 := by
  unfold tailWord_5761501
  simp only [CollatzResearch.WordTrace]
  refine ⟨210139205100073337876780357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140092803400048891917853571 210139205100073337876780357)
  ·
    refine ⟨39401100956263750851896317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210139205100073337876780357 39401100956263750851896317)
    ·
      refine ⟨14775412858598906569461119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39401100956263750851896317 14775412858598906569461119)
      ·
        refine ⟨22163119287898359854191679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14775412858598906569461119 22163119287898359854191679)
        ·
          refine ⟨33244678931847539781287519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22163119287898359854191679 33244678931847539781287519)
          ·
            refine ⟨49867018397771309671931279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33244678931847539781287519 49867018397771309671931279)
            ·
              refine ⟨74800527596656964507896919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49867018397771309671931279 74800527596656964507896919)
              ·
                refine ⟨112200791394985446761845379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74800527596656964507896919 112200791394985446761845379)
                ·
                  refine ⟨168301187092478170142768069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112200791394985446761845379 168301187092478170142768069)
                  ·
                    refine ⟨31556472579839656901769013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168301187092478170142768069 31556472579839656901769013)
                    ·
                      refine ⟨2958419304359967834540845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31556472579839656901769013 2958419304359967834540845)
                      ·
                        rfl

theorem cell23_5761501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5761501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761501 prefixEnd_5761501 := by exact prefixLift 5761501
  have htrace : WordTrace (prefixWord ++ tailWord_5761501) baseStart_5761501 baseEnd_5761501 := by
    simpa [prefixWord, tailWord_5761501, baseEnd_5761501] using wordTrace_append hprefix tailTrace_5761501
  have hstable : (prefixWord ++ tailWord_5761501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761501).length < 2 ^ (prefixWord ++ tailWord_5761501).sum := by decide
  have hdescent : baseEnd_5761501 < baseStart_5761501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761541 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_5761541 : Nat := 118140960795 + 5761541 * 2 ^ 59
def prefixEnd_5761541 : Nat := 4983230072969 + 3 ^ 40 * 5761541 * 2
def baseEnd_5761541 : Nat := 2958439843586147678040661

theorem tailTrace_5761541 : CollatzResearch.WordTrace tailWord_5761541 prefixEnd_5761541 2958439843586147678040661 := by
  unfold tailWord_5761541
  simp only [CollatzResearch.WordTrace]
  refine ⟨210140664019928424708236477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140093776013285616472157651 210140664019928424708236477)
  ·
    refine ⟨78802749007473159265588679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210140664019928424708236477 78802749007473159265588679)
    ·
      refine ⟨118204123511209738898383019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78802749007473159265588679 118204123511209738898383019)
      ·
        refine ⟨177306185266814608347574529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118204123511209738898383019 177306185266814608347574529)
        ·
          refine ⟨132979638950110956260680897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177306185266814608347574529 132979638950110956260680897)
          ·
            refine ⟨99734729212583217195510673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132979638950110956260680897 99734729212583217195510673)
            ·
              refine ⟨74801046909437412896633005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99734729212583217195510673 74801046909437412896633005)
              ·
                refine ⟨28050392591039029836237377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74801046909437412896633005 28050392591039029836237377)
                ·
                  refine ⟨21037794443279272377178033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28050392591039029836237377 21037794443279272377178033)
                  ·
                    refine ⟨15778345832459454282883525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21037794443279272377178033 15778345832459454282883525)
                    ·
                      refine ⟨2958439843586147678040661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15778345832459454282883525 2958439843586147678040661)
                      ·
                        rfl

theorem cell23_5761541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_5761541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761541 prefixEnd_5761541 := by exact prefixLift 5761541
  have htrace : WordTrace (prefixWord ++ tailWord_5761541) baseStart_5761541 baseEnd_5761541 := by
    simpa [prefixWord, tailWord_5761541, baseEnd_5761541] using wordTrace_append hprefix tailTrace_5761541
  have hstable : (prefixWord ++ tailWord_5761541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761541).length < 2 ^ (prefixWord ++ tailWord_5761541).sum := by decide
  have hdescent : baseEnd_5761541 < baseStart_5761541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761549 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5761549 : Nat := 118140960795 + 5761549 * 2 ^ 59
def prefixEnd_5761549 : Nat := 4983230072969 + 3 ^ 40 * 5761549 * 2
def baseEnd_5761549 : Nat := 2958443951431383646740625

theorem tailTrace_5761549 : CollatzResearch.WordTrace tailWord_5761549 prefixEnd_5761549 2958443951431383646740625 := by
  unfold tailWord_5761549
  simp only [CollatzResearch.WordTrace]
  refine ⟨210140955803899442074527701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140093970535932961383018467 210140955803899442074527701)
  ·
    refine ⟨4925178651653893173621743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 210140955803899442074527701 4925178651653893173621743)
    ·
      refine ⟨7387767977480839760432615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925178651653893173621743 7387767977480839760432615)
      ·
        refine ⟨11081651966221259640648923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387767977480839760432615 11081651966221259640648923)
        ·
          refine ⟨16622477949331889460973385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081651966221259640648923 16622477949331889460973385)
          ·
            refine ⟨12466858461998917095730039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16622477949331889460973385 12466858461998917095730039)
            ·
              refine ⟨18700287692998375643595059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466858461998917095730039 18700287692998375643595059)
              ·
                refine ⟨28050431539497563465392589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18700287692998375643595059 28050431539497563465392589)
                ·
                  refine ⟨10518911827311586299522221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28050431539497563465392589 10518911827311586299522221)
                  ·
                    refine ⟨3944591935241844862320833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10518911827311586299522221 3944591935241844862320833)
                    ·
                      refine ⟨2958443951431383646740625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944591935241844862320833 2958443951431383646740625)
                      ·
                        rfl

theorem cell23_5761549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5761549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761549 prefixEnd_5761549 := by exact prefixLift 5761549
  have htrace : WordTrace (prefixWord ++ tailWord_5761549) baseStart_5761549 baseEnd_5761549 := by
    simpa [prefixWord, tailWord_5761549, baseEnd_5761549] using wordTrace_append hprefix tailTrace_5761549
  have hstable : (prefixWord ++ tailWord_5761549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761549).length < 2 ^ (prefixWord ++ tailWord_5761549).sum := by decide
  have hdescent : baseEnd_5761549 < baseStart_5761549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761561 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_5761561 : Nat := 118140960795 + 5761561 * 2 ^ 59
def prefixEnd_5761561 : Nat := 4983230072969 + 3 ^ 40 * 5761561 * 2
def baseEnd_5761561 : Nat := 2958450113199237599790569

theorem tailTrace_5761561 : CollatzResearch.WordTrace tailWord_5761561 prefixEnd_5761561 2958450113199237599790569 := by
  unfold tailWord_5761561
  simp only [CollatzResearch.WordTrace]
  refine ⟨210141393479855968123964537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140094262319903978749309691 210141393479855968123964537)
  ·
    refine ⟨157606045109891976092973403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210141393479855968123964537 157606045109891976092973403)
    ·
      refine ⟨236409067664837964139460105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157606045109891976092973403 236409067664837964139460105)
      ·
        refine ⟨177306800748628473104595079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236409067664837964139460105 177306800748628473104595079)
        ·
          refine ⟨265960201122942709656892619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177306800748628473104595079 265960201122942709656892619)
          ·
            refine ⟨398940301684414064485338929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265960201122942709656892619 398940301684414064485338929)
            ·
              refine ⟨299205226263310548364004197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398940301684414064485338929 299205226263310548364004197)
              ·
                refine ⟨56100979924370727818250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299205226263310548364004197 56100979924370727818250787)
                ·
                  refine ⟨84151469886556091727376181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56100979924370727818250787 84151469886556091727376181)
                  ·
                    refine ⟨7889200301864633599441517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84151469886556091727376181 7889200301864633599441517)
                    ·
                      refine ⟨2958450113199237599790569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889200301864633599441517 2958450113199237599790569)
                      ·
                        rfl

theorem cell23_5761561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_5761561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761561 prefixEnd_5761561 := by exact prefixLift 5761561
  have htrace : WordTrace (prefixWord ++ tailWord_5761561) baseStart_5761561 baseEnd_5761561 := by
    simpa [prefixWord, tailWord_5761561, baseEnd_5761561] using wordTrace_append hprefix tailTrace_5761561
  have hstable : (prefixWord ++ tailWord_5761561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761561).length < 2 ^ (prefixWord ++ tailWord_5761561).sum := by decide
  have hdescent : baseEnd_5761561 < baseStart_5761561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761585 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 5]
def baseStart_5761585 : Nat := 118140960795 + 5761585 * 2 ^ 59
def prefixEnd_5761585 : Nat := 4983230072969 + 3 ^ 40 * 5761585 * 2
def baseEnd_5761585 : Nat := 328718048526105056210051

theorem tailTrace_5761585 : CollatzResearch.WordTrace tailWord_5761585 prefixEnd_5761585 328718048526105056210051 := by
  unfold tailWord_5761585
  simp only [CollatzResearch.WordTrace]
  refine ⟨210142268831769020222838209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140094845887846013481892139 210142268831769020222838209)
  ·
    refine ⟨157606701623826765167128657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210142268831769020222838209 157606701623826765167128657)
    ·
      refine ⟨118205026217870073875346493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157606701623826765167128657 118205026217870073875346493)
      ·
        refine ⟨44326884831701277703254935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118205026217870073875346493 44326884831701277703254935)
        ·
          refine ⟨66490327247551916554882403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44326884831701277703254935 66490327247551916554882403)
          ·
            refine ⟨99735490871327874832323605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66490327247551916554882403 99735490871327874832323605)
            ·
              refine ⟨4675101134593494132765169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99735490871327874832323605 4675101134593494132765169)
              ·
                refine ⟨3506325850945120599573877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4675101134593494132765169 3506325850945120599573877)
                ·
                  refine ⟨328718048526105056210051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506325850945120599573877 328718048526105056210051)
                  ·
                    rfl

theorem cell23_5761585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 5].length) (baseStart_5761585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761585 prefixEnd_5761585 := by exact prefixLift 5761585
  have htrace : WordTrace (prefixWord ++ tailWord_5761585) baseStart_5761585 baseEnd_5761585 := by
    simpa [prefixWord, tailWord_5761585, baseEnd_5761585] using wordTrace_append hprefix tailTrace_5761585
  have hstable : (prefixWord ++ tailWord_5761585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761585).length < 2 ^ (prefixWord ++ tailWord_5761585).sum := by decide
  have hdescent : baseEnd_5761585 < baseStart_5761585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761591 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_5761591 : Nat := 118140960795 + 5761591 * 2 ^ 59
def prefixEnd_5761591 : Nat := 4983230072969 + 3 ^ 40 * 5761591 * 2
def baseEnd_5761591 : Nat := 2958465517618872482415431

theorem tailTrace_5761591 : CollatzResearch.WordTrace tailWord_5761591 prefixEnd_5761591 2958465517618872482415431 := by
  unfold tailWord_5761591
  simp only [CollatzResearch.WordTrace]
  refine ⟨210142487669747283247556627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140094991779831522165037751 210142487669747283247556627)
  ·
    refine ⟨315213731504620924871334941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210142487669747283247556627 315213731504620924871334941)
    ·
      refine ⟨118205149314232846826750603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315213731504620924871334941 118205149314232846826750603)
      ·
        refine ⟨177307723971349270240125905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118205149314232846826750603 177307723971349270240125905)
        ·
          refine ⟨132980792978511952680094429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177307723971349270240125905 132980792978511952680094429)
          ·
            refine ⟨49867797366941982255035411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132980792978511952680094429 49867797366941982255035411)
            ·
              refine ⟨74801696050412973382553117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49867797366941982255035411 74801696050412973382553117)
              ·
                refine ⟨28050636018904865018457419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74801696050412973382553117 28050636018904865018457419)
                ·
                  refine ⟨42075954028357297527686129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28050636018904865018457419 42075954028357297527686129)
                  ·
                    refine ⟨31556965521267973145764597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42075954028357297527686129 31556965521267973145764597)
                    ·
                      refine ⟨2958465517618872482415431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31556965521267973145764597 2958465517618872482415431)
                      ·
                        rfl

theorem cell23_5761591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_5761591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761591 prefixEnd_5761591 := by exact prefixLift 5761591
  have htrace : WordTrace (prefixWord ++ tailWord_5761591) baseStart_5761591 baseEnd_5761591 := by
    simpa [prefixWord, tailWord_5761591, baseEnd_5761591] using wordTrace_append hprefix tailTrace_5761591
  have hstable : (prefixWord ++ tailWord_5761591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761591).length < 2 ^ (prefixWord ++ tailWord_5761591).sum := by decide
  have hdescent : baseEnd_5761591 < baseStart_5761591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761618 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_5761618 : Nat := 118140960795 + 5761618 * 2 ^ 59
def prefixEnd_5761618 : Nat := 4983230072969 + 3 ^ 40 * 5761618 * 2
def baseEnd_5761618 : Nat := 2958479381596543876777807

theorem tailTrace_5761618 : CollatzResearch.WordTrace tailWord_5761618 prefixEnd_5761618 2958479381596543876777807 := by
  unfold tailWord_5761618
  simp only [CollatzResearch.WordTrace]
  refine ⟨52535868110162366714697377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140095648293766311239193005 52535868110162366714697377)
  ·
    refine ⟨39401901082621775036023033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52535868110162366714697377 39401901082621775036023033)
    ·
      refine ⟨29551425811966331277017275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39401901082621775036023033 29551425811966331277017275)
      ·
        refine ⟨44327138717949496915525913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29551425811966331277017275 44327138717949496915525913)
        ·
          refine ⟨33245354038462122686644435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44327138717949496915525913 33245354038462122686644435)
          ·
            refine ⟨49868031057693184029966653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33245354038462122686644435 49868031057693184029966653)
            ·
              refine ⟨18700511646634944011237495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49868031057693184029966653 18700511646634944011237495)
              ·
                refine ⟨28050767469952416016856243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18700511646634944011237495 28050767469952416016856243)
                ·
                  refine ⟨42076151204928624025284365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28050767469952416016856243 42076151204928624025284365)
                  ·
                    refine ⟨15778556701848234009481637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42076151204928624025284365 15778556701848234009481637)
                    ·
                      refine ⟨2958479381596543876777807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15778556701848234009481637 2958479381596543876777807)
                      ·
                        rfl

theorem cell23_5761618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_5761618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761618 prefixEnd_5761618 := by exact prefixLift 5761618
  have htrace : WordTrace (prefixWord ++ tailWord_5761618) baseStart_5761618 baseEnd_5761618 := by
    simpa [prefixWord, tailWord_5761618, baseEnd_5761618] using wordTrace_append hprefix tailTrace_5761618
  have hstable : (prefixWord ++ tailWord_5761618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761618).length < 2 ^ (prefixWord ++ tailWord_5761618).sum := by decide
  have hdescent : baseEnd_5761618 < baseStart_5761618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761630 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5761630 : Nat := 118140960795 + 5761630 * 2 ^ 59
def prefixEnd_5761630 : Nat := 4983230072969 + 3 ^ 40 * 5761630 * 2
def baseEnd_5761630 : Nat := 2958485543364397829827753

theorem tailTrace_5761630 : CollatzResearch.WordTrace tailWord_5761630 prefixEnd_5761630 2958485543364397829827753 := by
  unfold tailWord_5761630
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267988764575749113528293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140095940077737328605484229 26267988764575749113528293)
  ·
    refine ⟨4925247893357952958786555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26267988764575749113528293 4925247893357952958786555)
    ·
      refine ⟨7387871840036929438179833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925247893357952958786555 7387871840036929438179833)
      ·
        refine ⟨5540903880027697078634875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7387871840036929438179833 5540903880027697078634875)
        ·
          refine ⟨8311355820041545617952313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540903880027697078634875 8311355820041545617952313)
          ·
            refine ⟨6233516865031159213464235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8311355820041545617952313 6233516865031159213464235)
            ·
              refine ⟨9350275297546738820196353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233516865031159213464235 9350275297546738820196353)
              ·
                refine ⟨7012706473160054115147265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350275297546738820196353 7012706473160054115147265)
                ·
                  refine ⟨5259529854870040586360449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012706473160054115147265 5259529854870040586360449)
                  ·
                    refine ⟨3944647391152530439770337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259529854870040586360449 3944647391152530439770337)
                    ·
                      refine ⟨2958485543364397829827753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944647391152530439770337 2958485543364397829827753)
                      ·
                        rfl

theorem cell23_5761630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5761630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761630 prefixEnd_5761630 := by exact prefixLift 5761630
  have htrace : WordTrace (prefixWord ++ tailWord_5761630) baseStart_5761630 baseEnd_5761630 := by
    simpa [prefixWord, tailWord_5761630, baseEnd_5761630] using wordTrace_append hprefix tailTrace_5761630
  have hstable : (prefixWord ++ tailWord_5761630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761630).length < 2 ^ (prefixWord ++ tailWord_5761630).sum := by decide
  have hdescent : baseEnd_5761630 < baseStart_5761630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761631 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_5761631 : Nat := 118140960795 + 5761631 * 2 ^ 59
def prefixEnd_5761631 : Nat := 4983230072969 + 3 ^ 40 * 5761631 * 2
def baseEnd_5761631 : Nat := 2958486056845052325915247

theorem tailTrace_5761631 : CollatzResearch.WordTrace tailWord_5761631 prefixEnd_5761631 2958486056845052325915247 := by
  unfold tailWord_5761631
  simp only [CollatzResearch.WordTrace]
  refine ⟨210143946589602370079012747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140095964393068246719341831 210143946589602370079012747)
  ·
    refine ⟨315215919884403555118519121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210143946589602370079012747 315215919884403555118519121)
    ·
      refine ⟨236411939913302666338889341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315215919884403555118519121 236411939913302666338889341)
      ·
        refine ⟨88654477467488499877083503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236411939913302666338889341 88654477467488499877083503)
        ·
          refine ⟨132981716201232749815625255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88654477467488499877083503 132981716201232749815625255)
          ·
            refine ⟨199472574301849124723437883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132981716201232749815625255 199472574301849124723437883)
            ·
              refine ⟨299208861452773687085156825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199472574301849124723437883 299208861452773687085156825)
              ·
                refine ⟨224406646089580265313867619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299208861452773687085156825 224406646089580265313867619)
                ·
                  refine ⟨336609969134370397970801429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224406646089580265313867619 336609969134370397970801429)
                  ·
                    refine ⟨15778592303173612404881317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 336609969134370397970801429 15778592303173612404881317)
                    ·
                      refine ⟨2958486056845052325915247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15778592303173612404881317 2958486056845052325915247)
                      ·
                        rfl

theorem cell23_5761631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_5761631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761631 prefixEnd_5761631 := by exact prefixLift 5761631
  have htrace : WordTrace (prefixWord ++ tailWord_5761631) baseStart_5761631 baseEnd_5761631 := by
    simpa [prefixWord, tailWord_5761631, baseEnd_5761631] using wordTrace_append hprefix tailTrace_5761631
  have hstable : (prefixWord ++ tailWord_5761631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761631).length < 2 ^ (prefixWord ++ tailWord_5761631).sum := by decide
  have hdescent : baseEnd_5761631 < baseStart_5761631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761645 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_5761645 : Nat := 118140960795 + 5761645 * 2 ^ 59
def prefixEnd_5761645 : Nat := 4983230072969 + 3 ^ 40 * 5761645 * 2
def baseEnd_5761645 : Nat := 986164415191405090380061

theorem tailTrace_5761645 : CollatzResearch.WordTrace tailWord_5761645 prefixEnd_5761645 986164415191405090380061 := by
  unfold tailWord_5761645
  simp only [CollatzResearch.WordTrace]
  refine ⟨210144457211551650470022389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140096304807701100313348259 210144457211551650470022389)
  ·
    refine ⟨19701042863582967231564599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210144457211551650470022389 19701042863582967231564599)
    ·
      refine ⟨29551564295374450847346899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701042863582967231564599 29551564295374450847346899)
      ·
        refine ⟨44327346443061676271020349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29551564295374450847346899 44327346443061676271020349)
        ·
          refine ⟨16622754916148128601632631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44327346443061676271020349 16622754916148128601632631)
          ·
            refine ⟨24934132374222192902448947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16622754916148128601632631 24934132374222192902448947)
            ·
              refine ⟨37401198561333289353673421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24934132374222192902448947 37401198561333289353673421)
              ·
                refine ⟨14025449460499983507627533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37401198561333289353673421 14025449460499983507627533)
                ·
                  refine ⟨5259543547687493815360325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14025449460499983507627533 5259543547687493815360325)
                  ·
                    refine ⟨986164415191405090380061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259543547687493815360325 986164415191405090380061)
                    ·
                      rfl

theorem cell23_5761645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_5761645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761645 prefixEnd_5761645 := by exact prefixLift 5761645
  have htrace : WordTrace (prefixWord ++ tailWord_5761645) baseStart_5761645 baseEnd_5761645 := by
    simpa [prefixWord, tailWord_5761645, baseEnd_5761645] using wordTrace_append hprefix tailTrace_5761645
  have hstable : (prefixWord ++ tailWord_5761645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761645).length < 2 ^ (prefixWord ++ tailWord_5761645).sum := by decide
  have hdescent : baseEnd_5761645 < baseStart_5761645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761681 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_5761681 : Nat := 118140960795 + 5761681 * 2 ^ 59
def prefixEnd_5761681 : Nat := 4983230072969 + 3 ^ 40 * 5761681 * 2
def baseEnd_5761681 : Nat := 2958511730877777130290017

theorem tailTrace_5761681 : CollatzResearch.WordTrace tailWord_5761681 prefixEnd_5761681 2958511730877777130290017 := by
  unfold tailWord_5761681
  simp only [CollatzResearch.WordTrace]
  refine ⟨210145770239421228618332897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140097180159614152412221931 210145770239421228618332897)
  ·
    refine ⟨157609327679565921463749673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210145770239421228618332897 157609327679565921463749673)
    ·
      refine ⟨118206995759674441097812255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157609327679565921463749673 118206995759674441097812255)
      ·
        refine ⟨177310493639511661646718383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118206995759674441097812255 177310493639511661646718383)
        ·
          refine ⟨265965740459267492470077575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177310493639511661646718383 265965740459267492470077575)
          ·
            refine ⟨398948610688901238705116363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265965740459267492470077575 398948610688901238705116363)
            ·
              refine ⟨598422916033351858057674545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398948610688901238705116363 598422916033351858057674545)
              ·
                refine ⟨448817187025013893543255909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598422916033351858057674545 448817187025013893543255909)
                ·
                  refine ⟨84153222567190105039360483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 448817187025013893543255909 84153222567190105039360483)
                  ·
                    refine ⟨126229833850785157559040725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84153222567190105039360483 126229833850785157559040725)
                    ·
                      refine ⟨2958511730877777130290017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126229833850785157559040725 2958511730877777130290017)
                      ·
                        rfl

theorem cell23_5761681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_5761681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761681 prefixEnd_5761681 := by exact prefixLift 5761681
  have htrace : WordTrace (prefixWord ++ tailWord_5761681) baseStart_5761681 baseEnd_5761681 := by
    simpa [prefixWord, tailWord_5761681, baseEnd_5761681] using wordTrace_append hprefix tailTrace_5761681
  have hstable : (prefixWord ++ tailWord_5761681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761681).length < 2 ^ (prefixWord ++ tailWord_5761681).sum := by decide
  have hdescent : baseEnd_5761681 < baseStart_5761681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761725 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5761725 : Nat := 118140960795 + 5761725 * 2 ^ 59
def prefixEnd_5761725 : Nat := 4983230072969 + 3 ^ 40 * 5761725 * 2
def baseEnd_5761725 : Nat := 2958534324026574958139815

theorem tailTrace_5761725 : CollatzResearch.WordTrace tailWord_5761725 prefixEnd_5761725 2958534324026574958139815 := by
  unfold tailWord_5761725
  simp only [CollatzResearch.WordTrace]
  refine ⟨210147375051261824132934629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140098250034174549421956419 210147375051261824132934629)
  ·
    refine ⟨39402632822111592024925243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210147375051261824132934629 39402632822111592024925243)
    ·
      refine ⟨59103949233167388037387865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39402632822111592024925243 59103949233167388037387865)
      ·
        refine ⟨44327961924875541028040899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59103949233167388037387865 44327961924875541028040899)
        ·
          refine ⟨66491942887313311542061349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44327961924875541028040899 66491942887313311542061349)
          ·
            refine ⟨12467239291371245914136503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66491942887313311542061349 12467239291371245914136503)
            ·
              refine ⟨18700858937056868871204755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12467239291371245914136503 18700858937056868871204755)
              ·
                refine ⟨28051288405585303306807133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18700858937056868871204755 28051288405585303306807133)
                ·
                  refine ⟨10519233152094488740052675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28051288405585303306807133 10519233152094488740052675)
                  ·
                    refine ⟨15778849728141733110079013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10519233152094488740052675 15778849728141733110079013)
                    ·
                      refine ⟨2958534324026574958139815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15778849728141733110079013 2958534324026574958139815)
                      ·
                        rfl

theorem cell23_5761725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5761725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761725 prefixEnd_5761725 := by exact prefixLift 5761725
  have htrace : WordTrace (prefixWord ++ tailWord_5761725) baseStart_5761725 baseEnd_5761725 := by
    simpa [prefixWord, tailWord_5761725, baseEnd_5761725] using wordTrace_append hprefix tailTrace_5761725
  have hstable : (prefixWord ++ tailWord_5761725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761725).length < 2 ^ (prefixWord ++ tailWord_5761725).sum := by decide
  have hdescent : baseEnd_5761725 < baseStart_5761725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761748 : List Nat := [2, 4, 1, 3, 13]
def baseStart_5761748 : Nat := 118140960795 + 5761748 * 2 ^ 59
def prefixEnd_5761748 : Nat := 4983230072969 + 3 ^ 40 * 5761748 * 2
def baseEnd_5761748 : Nat := 4058362323843111616121

theorem tailTrace_5761748 : CollatzResearch.WordTrace tailWord_5761748 prefixEnd_5761748 4058362323843111616121 := by
  unfold tailWord_5761748
  simp only [CollatzResearch.WordTrace]
  refine ⟨105074106965089249530510949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140098809286785666040681265 105074106965089249530510949)
  ·
    refine ⟨19701395055954234286970803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105074106965089249530510949 19701395055954234286970803)
    ·
      refine ⟨29552092583931351430456205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701395055954234286970803 29552092583931351430456205)
      ·
        refine ⟨11082034718974256786421077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29552092583931351430456205 11082034718974256786421077)
        ·
          refine ⟨4058362323843111616121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11082034718974256786421077 4058362323843111616121)
          ·
            rfl

theorem cell23_5761748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 13].length) (baseStart_5761748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761748 prefixEnd_5761748 := by exact prefixLift 5761748
  have htrace : WordTrace (prefixWord ++ tailWord_5761748) baseStart_5761748 baseEnd_5761748 := by
    simpa [prefixWord, tailWord_5761748, baseEnd_5761748] using wordTrace_append hprefix tailTrace_5761748
  have hstable : (prefixWord ++ tailWord_5761748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761748).length < 2 ^ (prefixWord ++ tailWord_5761748).sum := by decide
  have hdescent : baseEnd_5761748 < baseStart_5761748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761752 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_5761752 : Nat := 118140960795 + 5761752 * 2 ^ 59
def prefixEnd_5761752 : Nat := 4983230072969 + 3 ^ 40 * 5761752 * 2
def baseEnd_5761752 : Nat := 986182729334748784167397

theorem tailTrace_5761752 : CollatzResearch.WordTrace tailWord_5761752 prefixEnd_5761752 986182729334748784167397 := by
  unfold tailWord_5761752
  simp only [CollatzResearch.WordTrace]
  refine ⟨105074179911082003872083755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140098906548109338496111673 105074179911082003872083755)
  ·
    refine ⟨157611269866623005808125633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105074179911082003872083755 157611269866623005808125633)
    ·
      refine ⟨118208452399967254356094225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157611269866623005808125633 118208452399967254356094225)
      ·
        refine ⟨88656339299975440767070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118208452399967254356094225 88656339299975440767070669)
        ·
          refine ⟨33246127237490790287651501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88656339299975440767070669 33246127237490790287651501)
          ·
            refine ⟨12467297714059046357869313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33246127237490790287651501 12467297714059046357869313)
            ·
              refine ⟨9350473285544284768401985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12467297714059046357869313 9350473285544284768401985)
              ·
                refine ⟨7012854964158213576301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350473285544284768401985 7012854964158213576301489)
                ·
                  refine ⟨5259641223118660182226117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012854964158213576301489 5259641223118660182226117)
                  ·
                    refine ⟨986182729334748784167397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259641223118660182226117 986182729334748784167397)
                    ·
                      rfl

theorem cell23_5761752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_5761752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761752 prefixEnd_5761752 := by exact prefixLift 5761752
  have htrace : WordTrace (prefixWord ++ tailWord_5761752) baseStart_5761752 baseEnd_5761752 := by
    simpa [prefixWord, tailWord_5761752, baseEnd_5761752] using wordTrace_append hprefix tailTrace_5761752
  have hstable : (prefixWord ++ tailWord_5761752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761752).length < 2 ^ (prefixWord ++ tailWord_5761752).sum := by decide
  have hdescent : baseEnd_5761752 < baseStart_5761752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761765 : List Nat := [1, 3, 1, 4, 1, 4, 1, 8]
def baseStart_5761765 : Nat := 118140960795 + 5761765 * 2 ^ 59
def prefixEnd_5761765 : Nat := 4983230072969 + 3 ^ 40 * 5761765 * 2
def baseEnd_5761765 : Nat := 109576106046398325986653

theorem tailTrace_5761765 : CollatzResearch.WordTrace tailWord_5761765 prefixEnd_5761765 109576106046398325986653 := by
  unfold tailWord_5761765
  simp only [CollatzResearch.WordTrace]
  refine ⟨210148833971116910964390749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140099222647411273976260499 210148833971116910964390749)
  ·
    refine ⟨78805812739168841611646531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210148833971116910964390749 78805812739168841611646531)
    ·
      refine ⟨118208719108753262417469797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78805812739168841611646531 118208719108753262417469797)
      ·
        refine ⟨22164134832891236703275587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118208719108753262417469797 22164134832891236703275587)
        ·
          refine ⟨33246202249336855054913381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22164134832891236703275587 33246202249336855054913381)
          ·
            refine ⟨6233662921750660322796259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33246202249336855054913381 6233662921750660322796259)
            ·
              refine ⟨9350494382625990484194389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233662921750660322796259 9350494382625990484194389)
              ·
                refine ⟨109576106046398325986653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9350494382625990484194389 109576106046398325986653)
                ·
                  rfl

theorem cell23_5761765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 8].length) (baseStart_5761765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761765 prefixEnd_5761765 := by exact prefixLift 5761765
  have htrace : WordTrace (prefixWord ++ tailWord_5761765) baseStart_5761765 baseEnd_5761765 := by
    simpa [prefixWord, tailWord_5761765, baseEnd_5761765] using wordTrace_append hprefix tailTrace_5761765
  have hstable : (prefixWord ++ tailWord_5761765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761765).length < 2 ^ (prefixWord ++ tailWord_5761765).sum := by decide
  have hdescent : baseEnd_5761765 < baseStart_5761765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761775 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_5761775 : Nat := 118140960795 + 5761775 * 2 ^ 59
def prefixEnd_5761775 : Nat := 4983230072969 + 3 ^ 40 * 5761775 * 2
def baseEnd_5761775 : Nat := 2958559998059299762514585

theorem tailTrace_5761775 : CollatzResearch.WordTrace tailWord_5761775 prefixEnd_5761775 2958559998059299762514585 := by
  unfold tailWord_5761775
  simp only [CollatzResearch.WordTrace]
  refine ⟨210149198701080682672254779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140099465800720455114836519 210149198701080682672254779)
  ·
    refine ⟨315223798051621024008382169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210149198701080682672254779 315223798051621024008382169)
    ·
      refine ⟨236417848538715768006286627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315223798051621024008382169 236417848538715768006286627)
      ·
        refine ⟨354626772808073652009429941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236417848538715768006286627 354626772808073652009429941)
        ·
          refine ⟨33246259950756904875884057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354626772808073652009429941 33246259950756904875884057)
          ·
            refine ⟨24934694963067678656913043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33246259950756904875884057 24934694963067678656913043)
            ·
              refine ⟨37402042444601517985369565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24934694963067678656913043 37402042444601517985369565)
              ·
                refine ⟨14025765916725569244513587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37402042444601517985369565 14025765916725569244513587)
                ·
                  refine ⟨21038648875088353866770381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14025765916725569244513587 21038648875088353866770381)
                  ·
                    refine ⟨7889493328158132700038893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21038648875088353866770381 7889493328158132700038893)
                    ·
                      refine ⟨2958559998059299762514585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889493328158132700038893 2958559998059299762514585)
                      ·
                        rfl

theorem cell23_5761775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_5761775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761775 prefixEnd_5761775 := by exact prefixLift 5761775
  have htrace : WordTrace (prefixWord ++ tailWord_5761775) baseStart_5761775 baseEnd_5761775 := by
    simpa [prefixWord, tailWord_5761775, baseEnd_5761775] using wordTrace_append hprefix tailTrace_5761775
  have hstable : (prefixWord ++ tailWord_5761775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761775).length < 2 ^ (prefixWord ++ tailWord_5761775).sum := by decide
  have hdescent : baseEnd_5761775 < baseStart_5761775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761780 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5761780 : Nat := 118140960795 + 5761780 * 2 ^ 59
def prefixEnd_5761780 : Nat := 4983230072969 + 3 ^ 40 * 5761780 * 2
def baseEnd_5761780 : Nat := 2958562565462572242952063

theorem tailTrace_5761780 : CollatzResearch.WordTrace tailWord_5761780 prefixEnd_5761780 2958562565462572242952063 := by
  unfold tailWord_5761780
  simp only [CollatzResearch.WordTrace]
  refine ⟨105074690533031284263093397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140099587377375045684124529 105074690533031284263093397)
  ·
    refine ⟨4925376118735841449832503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105074690533031284263093397 4925376118735841449832503)
    ·
      refine ⟨7388064178103762174748755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925376118735841449832503 7388064178103762174748755)
      ·
        refine ⟨11082096267155643262123133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388064178103762174748755 11082096267155643262123133)
        ·
          refine ⟨4155786100183366223296175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11082096267155643262123133 4155786100183366223296175)
          ·
            refine ⟨6233679150275049334944263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155786100183366223296175 6233679150275049334944263)
            ·
              refine ⟨9350518725412574002416395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233679150275049334944263 9350518725412574002416395)
              ·
                refine ⟨14025778088118861003624593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350518725412574002416395 14025778088118861003624593)
                ·
                  refine ⟨10519333566089145752718445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14025778088118861003624593 10519333566089145752718445)
                  ·
                    refine ⟨3944750087283429657269417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10519333566089145752718445 3944750087283429657269417)
                    ·
                      refine ⟨2958562565462572242952063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944750087283429657269417 2958562565462572242952063)
                      ·
                        rfl

theorem cell23_5761780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5761780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761780 prefixEnd_5761780 := by exact prefixLift 5761780
  have htrace : WordTrace (prefixWord ++ tailWord_5761780) baseStart_5761780 baseEnd_5761780 := by
    simpa [prefixWord, tailWord_5761780, baseEnd_5761780] using wordTrace_append hprefix tailTrace_5761780
  have hstable : (prefixWord ++ tailWord_5761780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761780).length < 2 ^ (prefixWord ++ tailWord_5761780).sum := by decide
  have hdescent : baseEnd_5761780 < baseStart_5761780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761826 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_5761826 : Nat := 118140960795 + 5761826 * 2 ^ 59
def prefixEnd_5761826 : Nat := 4983230072969 + 3 ^ 40 * 5761826 * 2
def baseEnd_5761826 : Nat := 2958586185572679062976851

theorem tailTrace_5761826 : CollatzResearch.WordTrace tailWord_5761826 prefixEnd_5761826 2958586185572679062976851 := by
  unfold tailWord_5761826
  simp only [CollatzResearch.WordTrace]
  refine ⟨52537764705973979595590333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140100705882597278921574221 52537764705973979595590333)
  ·
    refine ⟨19701661764740242348346375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52537764705973979595590333 19701661764740242348346375)
    ·
      refine ⟨29552492647110363522519563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19701661764740242348346375 29552492647110363522519563)
      ·
        refine ⟨44328738970665545283779345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29552492647110363522519563 44328738970665545283779345)
        ·
          refine ⟨33246554227999158962834509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44328738970665545283779345 33246554227999158962834509)
          ·
            refine ⟨12467457835499684611062941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33246554227999158962834509 12467457835499684611062941)
            ·
              refine ⟨4675296688312381729148603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12467457835499684611062941 4675296688312381729148603)
              ·
                refine ⟨7012945032468572593722905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675296688312381729148603 7012945032468572593722905)
                ·
                  refine ⟨5259708774351429445292179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012945032468572593722905 5259708774351429445292179)
                  ·
                    refine ⟨7889563161527144167938269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5259708774351429445292179 7889563161527144167938269)
                    ·
                      refine ⟨2958586185572679062976851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889563161527144167938269 2958586185572679062976851)
                      ·
                        rfl

theorem cell23_5761826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_5761826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761826 prefixEnd_5761826 := by exact prefixLift 5761826
  have htrace : WordTrace (prefixWord ++ tailWord_5761826) baseStart_5761826 baseEnd_5761826 := by
    simpa [prefixWord, tailWord_5761826, baseEnd_5761826] using wordTrace_append hprefix tailTrace_5761826
  have hstable : (prefixWord ++ tailWord_5761826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761826).length < 2 ^ (prefixWord ++ tailWord_5761826).sum := by decide
  have hdescent : baseEnd_5761826 < baseStart_5761826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5761959 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5761959 : Nat := 118140960795 + 5761959 * 2 ^ 59
def prefixEnd_5761959 : Nat := 4983230072969 + 3 ^ 40 * 5761959 * 2
def baseEnd_5761959 : Nat := 2958654478499727042613739

theorem tailTrace_5761959 : CollatzResearch.WordTrace tailWord_5761959 prefixEnd_5761959 2958654478499727042613739 := by
  unfold tailWord_5761959
  simp only [CollatzResearch.WordTrace]
  refine ⟨210155909732414082096952931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140103939821609388064635287 210155909732414082096952931)
  ·
    refine ⟨315233864598621123145429397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210155909732414082096952931 315233864598621123145429397)
    ·
      refine ⟨14776587403060365147442003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 315233864598621123145429397 14776587403060365147442003)
      ·
        refine ⟨22164881104590547721163005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14776587403060365147442003 22164881104590547721163005)
        ·
          refine ⟨8311830414221455395436127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22164881104590547721163005 8311830414221455395436127)
          ·
            refine ⟨12467745621332183093154191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8311830414221455395436127 12467745621332183093154191)
            ·
              refine ⟨18701618431998274639731287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12467745621332183093154191 18701618431998274639731287)
              ·
                refine ⟨28052427647997411959596931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18701618431998274639731287 28052427647997411959596931)
                ·
                  refine ⟨42078641471996117939395397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28052427647997411959596931 42078641471996117939395397)
                  ·
                    refine ⟨7889745275999272113636637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42078641471996117939395397 7889745275999272113636637)
                    ·
                      refine ⟨2958654478499727042613739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889745275999272113636637 2958654478499727042613739)
                      ·
                        rfl

theorem cell23_5761959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5761959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5761959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5761959 prefixEnd_5761959 := by exact prefixLift 5761959
  have htrace : WordTrace (prefixWord ++ tailWord_5761959) baseStart_5761959 baseEnd_5761959 := by
    simpa [prefixWord, tailWord_5761959, baseEnd_5761959] using wordTrace_append hprefix tailTrace_5761959
  have hstable : (prefixWord ++ tailWord_5761959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5761959).length < 2 ^ (prefixWord ++ tailWord_5761959).sum := by decide
  have hdescent : baseEnd_5761959 < baseStart_5761959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5761959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762009 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_5762009 : Nat := 118140960795 + 5762009 * 2 ^ 59
def prefixEnd_5762009 : Nat := 4983230072969 + 3 ^ 40 * 5762009 * 2
def baseEnd_5762009 : Nat := 986226717510817282329503

theorem tailTrace_5762009 : CollatzResearch.WordTrace tailWord_5762009 prefixEnd_5762009 986226717510817282329503 := by
  unfold tailWord_5762009
  simp only [CollatzResearch.WordTrace]
  refine ⟨210157733382232940636273081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140105155588155293757515387 210157733382232940636273081)
  ·
    refine ⟨157618300036674705477204811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210157733382232940636273081 157618300036674705477204811)
    ·
      refine ⟨236427450055012058215807217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157618300036674705477204811 236427450055012058215807217)
      ·
        refine ⟨177320587541259043661855413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236427450055012058215807217 177320587541259043661855413)
        ·
          refine ⟨16623805081993035343298945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177320587541259043661855413 16623805081993035343298945)
          ·
            refine ⟨12467853811494776507474209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16623805081993035343298945 12467853811494776507474209)
            ·
              refine ⟨9350890358621082380605657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12467853811494776507474209 9350890358621082380605657)
              ·
                refine ⟨7013167768965811785454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350890358621082380605657 7013167768965811785454243)
                ·
                  refine ⟨10519751653448717678181365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013167768965811785454243 10519751653448717678181365)
                  ·
                    refine ⟨986226717510817282329503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10519751653448717678181365 986226717510817282329503)
                    ·
                      rfl

theorem cell23_5762009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_5762009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762009 prefixEnd_5762009 := by exact prefixLift 5762009
  have htrace : WordTrace (prefixWord ++ tailWord_5762009) baseStart_5762009 baseEnd_5762009 := by
    simpa [prefixWord, tailWord_5762009, baseEnd_5762009] using wordTrace_append hprefix tailTrace_5762009
  have hstable : (prefixWord ++ tailWord_5762009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762009).length < 2 ^ (prefixWord ++ tailWord_5762009).sum := by decide
  have hdescent : baseEnd_5762009 < baseStart_5762009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762023 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5762023 : Nat := 118140960795 + 5762023 * 2 ^ 59
def prefixEnd_5762023 : Nat := 4983230072969 + 3 ^ 40 * 5762023 * 2
def baseEnd_5762023 : Nat := 2958687341261614792213445

theorem tailTrace_5762023 : CollatzResearch.WordTrace tailWord_5762023 prefixEnd_5762023 2958687341261614792213445 := by
  unfold tailWord_5762023
  simp only [CollatzResearch.WordTrace]
  refine ⟨210158244004182221027282723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140105496002788147351521815 210158244004182221027282723)
  ·
    refine ⟨315237366006273331540924085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210158244004182221027282723 315237366006273331540924085)
    ·
      refine ⟨29553503063088124831961633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315237366006273331540924085 29553503063088124831961633)
      ·
        refine ⟨22165127297316093623971225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29553503063088124831961633 22165127297316093623971225)
        ·
          refine ⟨16623845472987070217978419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22165127297316093623971225 16623845472987070217978419)
          ·
            refine ⟨24935768209480605326967629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16623845472987070217978419 24935768209480605326967629)
            ·
              refine ⟨9350913078555226997612861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24935768209480605326967629 9350913078555226997612861)
              ·
                refine ⟨3506592404458210124104823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9350913078555226997612861 3506592404458210124104823)
                ·
                  refine ⟨5259888606687315186157235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506592404458210124104823 5259888606687315186157235)
                  ·
                    refine ⟨7889832910030972779235853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5259888606687315186157235 7889832910030972779235853)
                    ·
                      refine ⟨2958687341261614792213445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889832910030972779235853 2958687341261614792213445)
                      ·
                        rfl

theorem cell23_5762023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5762023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762023 prefixEnd_5762023 := by exact prefixLift 5762023
  have htrace : WordTrace (prefixWord ++ tailWord_5762023) baseStart_5762023 baseEnd_5762023 := by
    simpa [prefixWord, tailWord_5762023, baseEnd_5762023] using wordTrace_append hprefix tailTrace_5762023
  have hstable : (prefixWord ++ tailWord_5762023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762023).length < 2 ^ (prefixWord ++ tailWord_5762023).sum := by decide
  have hdescent : baseEnd_5762023 < baseStart_5762023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762032 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_5762032 : Nat := 118140960795 + 5762032 * 2 ^ 59
def prefixEnd_5762032 : Nat := 4983230072969 + 3 ^ 40 * 5762032 * 2
def baseEnd_5762032 : Nat := 2958691962587505257000903

theorem tailTrace_5762032 : CollatzResearch.WordTrace tailWord_5762032 prefixEnd_5762032 2958691962587505257000903 := by
  unfold tailWord_5762032
  simp only [CollatzResearch.WordTrace]
  refine ⟨105079286130574807782180175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140105714840766410376240233 105079286130574807782180175)
  ·
    refine ⟨157618929195862211673270263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105079286130574807782180175 157618929195862211673270263)
    ·
      refine ⟨236428393793793317509905395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157618929195862211673270263 236428393793793317509905395)
      ·
        refine ⟨354642590690689976264858093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236428393793793317509905395 354642590690689976264858093)
        ·
          refine ⟨132990971509008741099321785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354642590690689976264858093 132990971509008741099321785)
          ·
            refine ⟨99743228631756555824491339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132990971509008741099321785 99743228631756555824491339)
            ·
              refine ⟨149614842947634833736737009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99743228631756555824491339 149614842947634833736737009)
              ·
                refine ⟨112211132210726125302552757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149614842947634833736737009 112211132210726125302552757)
                ·
                  refine ⟨10519793644755574247114321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112211132210726125302552757 10519793644755574247114321)
                  ·
                    refine ⟨7889845233566680685335741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10519793644755574247114321 7889845233566680685335741)
                    ·
                      refine ⟨2958691962587505257000903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889845233566680685335741 2958691962587505257000903)
                      ·
                        rfl

theorem cell23_5762032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_5762032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762032 prefixEnd_5762032 := by exact prefixLift 5762032
  have htrace : WordTrace (prefixWord ++ tailWord_5762032) baseStart_5762032 baseEnd_5762032 := by
    simpa [prefixWord, tailWord_5762032, baseEnd_5762032] using wordTrace_append hprefix tailTrace_5762032
  have hstable : (prefixWord ++ tailWord_5762032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762032).length < 2 ^ (prefixWord ++ tailWord_5762032).sum := by decide
  have hdescent : baseEnd_5762032 < baseStart_5762032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762056 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_5762056 : Nat := 118140960795 + 5762056 * 2 ^ 59
def prefixEnd_5762056 : Nat := 4983230072969 + 3 ^ 40 * 5762056 * 2
def baseEnd_5762056 : Nat := 986234762041071054366931

theorem tailTrace_5762056 : CollatzResearch.WordTrace tailWord_5762056 prefixEnd_5762056 986234762041071054366931 := by
  unfold tailWord_5762056
  simp only [CollatzResearch.WordTrace]
  refine ⟨105079723806531333831617011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140106298408708445108822681 105079723806531333831617011)
  ·
    refine ⟨157619585709797000747425517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105079723806531333831617011 157619585709797000747425517)
    ·
      refine ⟨59107344641173875280284569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157619585709797000747425517 59107344641173875280284569)
      ·
        refine ⟨44330508480880406460213427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59107344641173875280284569 44330508480880406460213427)
        ·
          refine ⟨66495762721320609690320141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44330508480880406460213427 66495762721320609690320141)
          ·
            refine ⟨24935911020495228633870053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66495762721320609690320141 24935911020495228633870053)
            ·
              refine ⟨4675483316342855368850635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24935911020495228633870053 4675483316342855368850635)
              ·
                refine ⟨7013224974514283053275953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675483316342855368850635 7013224974514283053275953)
                ·
                  refine ⟨5259918730885712289956965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013224974514283053275953 5259918730885712289956965)
                  ·
                    refine ⟨986234762041071054366931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259918730885712289956965 986234762041071054366931)
                    ·
                      rfl

theorem cell23_5762056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_5762056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762056 prefixEnd_5762056 := by exact prefixLift 5762056
  have htrace : WordTrace (prefixWord ++ tailWord_5762056) baseStart_5762056 baseEnd_5762056 := by
    simpa [prefixWord, tailWord_5762056, baseEnd_5762056] using wordTrace_append hprefix tailTrace_5762056
  have hstable : (prefixWord ++ tailWord_5762056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762056).length < 2 ^ (prefixWord ++ tailWord_5762056).sum := by decide
  have hdescent : baseEnd_5762056 < baseStart_5762056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762075 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_5762075 : Nat := 118140960795 + 5762075 * 2 ^ 59
def prefixEnd_5762075 : Nat := 4983230072969 + 3 ^ 40 * 5762075 * 2
def baseEnd_5762075 : Nat := 2958714042255648588763205

theorem tailTrace_5762075 : CollatzResearch.WordTrace tailWord_5762075 prefixEnd_5762075 2958714042255648588763205 := by
  unfold tailWord_5762075
  simp only [CollatzResearch.WordTrace]
  refine ⟨210160140599993833908175679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140106760399995889272117119 210160140599993833908175679)
  ·
    refine ⟨315240210899990750862263519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210160140599993833908175679 315240210899990750862263519)
    ·
      refine ⟨472860316349986126293395279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315240210899990750862263519 472860316349986126293395279)
      ·
        refine ⟨709290474524979189440092919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472860316349986126293395279 709290474524979189440092919)
        ·
          refine ⟨1063935711787468784160139379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709290474524979189440092919 1063935711787468784160139379)
          ·
            refine ⟨1595903567681203176240209069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063935711787468784160139379 1595903567681203176240209069)
            ·
              refine ⟨598463837880451191090078401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1595903567681203176240209069 598463837880451191090078401)
              ·
                refine ⟨448847878410338393317558801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598463837880451191090078401 448847878410338393317558801)
                ·
                  refine ⟨336635908807753794988169101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448847878410338393317558801 336635908807753794988169101)
                  ·
                    refine ⟨126238465802907673120563413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336635908807753794988169101 126238465802907673120563413)
                    ·
                      refine ⟨2958714042255648588763205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126238465802907673120563413 2958714042255648588763205)
                      ·
                        rfl

theorem cell23_5762075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_5762075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762075 prefixEnd_5762075 := by exact prefixLift 5762075
  have htrace : WordTrace (prefixWord ++ tailWord_5762075) baseStart_5762075 baseEnd_5762075 := by
    simpa [prefixWord, tailWord_5762075, baseEnd_5762075] using wordTrace_append hprefix tailTrace_5762075
  have hstable : (prefixWord ++ tailWord_5762075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762075).length < 2 ^ (prefixWord ++ tailWord_5762075).sum := by decide
  have hdescent : baseEnd_5762075 < baseStart_5762075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762079 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_5762079 : Nat := 118140960795 + 5762079 * 2 ^ 59
def prefixEnd_5762079 : Nat := 4983230072969 + 3 ^ 40 * 5762079 * 2
def baseEnd_5762079 : Nat := 2958716096178266573113187

theorem tailTrace_5762079 : CollatzResearch.WordTrace tailWord_5762079 prefixEnd_5762079 2958716096178266573113187 := by
  unfold tailWord_5762079
  simp only [CollatzResearch.WordTrace]
  refine ⟨210160286491979342591321291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140106857661319561727547527 210160286491979342591321291)
  ·
    refine ⟨315240429737969013886981937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210160286491979342591321291 315240429737969013886981937)
    ·
      refine ⟨236430322303476760415236453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315240429737969013886981937 236430322303476760415236453)
      ·
        refine ⟨44330685431901892577856835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236430322303476760415236453 44330685431901892577856835)
        ·
          refine ⟨66496028147852838866785253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44330685431901892577856835 66496028147852838866785253)
          ·
            refine ⟨12468005277722407287522235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66496028147852838866785253 12468005277722407287522235)
            ·
              refine ⟨18702007916583610931283353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12468005277722407287522235 18702007916583610931283353)
              ·
                refine ⟨14026505937437708198462515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18702007916583610931283353 14026505937437708198462515)
                ·
                  refine ⟨21039758906156562297693773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14026505937437708198462515 21039758906156562297693773)
                  ·
                    refine ⟨7889909589808710861635165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21039758906156562297693773 7889909589808710861635165)
                    ·
                      refine ⟨2958716096178266573113187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889909589808710861635165 2958716096178266573113187)
                      ·
                        rfl

theorem cell23_5762079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_5762079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762079 prefixEnd_5762079 := by exact prefixLift 5762079
  have htrace : WordTrace (prefixWord ++ tailWord_5762079) baseStart_5762079 baseEnd_5762079 := by
    simpa [prefixWord, tailWord_5762079, baseEnd_5762079] using wordTrace_append hprefix tailTrace_5762079
  have hstable : (prefixWord ++ tailWord_5762079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762079).length < 2 ^ (prefixWord ++ tailWord_5762079).sum := by decide
  have hdescent : baseEnd_5762079 < baseStart_5762079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762096 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_5762096 : Nat := 118140960795 + 5762096 * 2 ^ 59
def prefixEnd_5762096 : Nat := 4983230072969 + 3 ^ 40 * 5762096 * 2
def baseEnd_5762096 : Nat := 2958724825349393006600609

theorem tailTrace_5762096 : CollatzResearch.WordTrace tailWord_5762096 prefixEnd_5762096 2958724825349393006600609 := by
  unfold tailWord_5762096
  simp only [CollatzResearch.WordTrace]
  refine ⟨105080453266458877247345071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140107271021945169663126761 105080453266458877247345071)
  ·
    refine ⟨157620679899688315871017607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105080453266458877247345071 157620679899688315871017607)
    ·
      refine ⟨236431019849532473806526411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157620679899688315871017607 236431019849532473806526411)
      ·
        refine ⟨354646529774298710709789617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236431019849532473806526411 354646529774298710709789617)
        ·
          refine ⟨265984897330724033032342213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354646529774298710709789617 265984897330724033032342213)
          ·
            refine ⟨49872168249510756193564165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 265984897330724033032342213 49872168249510756193564165)
            ·
              refine ⟨9351031546783266786293281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49872168249510756193564165 9351031546783266786293281)
              ·
                refine ⟨7013273660087450089719961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351031546783266786293281 7013273660087450089719961)
                ·
                  refine ⟨5259955245065587567289971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013273660087450089719961 5259955245065587567289971)
                  ·
                    refine ⟨7889932867598381350934957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5259955245065587567289971 7889932867598381350934957)
                    ·
                      refine ⟨2958724825349393006600609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889932867598381350934957 2958724825349393006600609)
                      ·
                        rfl

theorem cell23_5762096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_5762096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762096 prefixEnd_5762096 := by exact prefixLift 5762096
  have htrace : WordTrace (prefixWord ++ tailWord_5762096) baseStart_5762096 baseEnd_5762096 := by
    simpa [prefixWord, tailWord_5762096, baseEnd_5762096] using wordTrace_append hprefix tailTrace_5762096
  have hstable : (prefixWord ++ tailWord_5762096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762096).length < 2 ^ (prefixWord ++ tailWord_5762096).sum := by decide
  have hdescent : baseEnd_5762096 < baseStart_5762096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762112 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_5762112 : Nat := 118140960795 + 5762112 * 2 ^ 59
def prefixEnd_5762112 : Nat := 4983230072969 + 3 ^ 40 * 5762112 * 2
def baseEnd_5762112 : Nat := 986244347013288314666845

theorem tailTrace_5762112 : CollatzResearch.WordTrace tailWord_5762112 prefixEnd_5762112 986244347013288314666845 := by
  unfold tailWord_5762112
  simp only [CollatzResearch.WordTrace]
  refine ⟨105080745050429894613636295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140107660067239859484848393 105080745050429894613636295)
  ·
    refine ⟨157621117575644841920454443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105080745050429894613636295 157621117575644841920454443)
    ·
      refine ⟨236431676363467262880681665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157621117575644841920454443 236431676363467262880681665)
      ·
        refine ⟨177323757272600447160511249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236431676363467262880681665 177323757272600447160511249)
        ·
          refine ⟨132992817954450335370383437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177323757272600447160511249 132992817954450335370383437)
          ·
            refine ⟨49872306732918875763893789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132992817954450335370383437 49872306732918875763893789)
            ·
              refine ⟨18702115024844578411460171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49872306732918875763893789 18702115024844578411460171)
              ·
                refine ⟨28053172537266867617190257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18702115024844578411460171 28053172537266867617190257)
                ·
                  refine ⟨21039879402950150712892693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28053172537266867617190257 21039879402950150712892693)
                  ·
                    refine ⟨986244347013288314666845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21039879402950150712892693 986244347013288314666845)
                    ·
                      rfl

theorem cell23_5762112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_5762112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762112 prefixEnd_5762112 := by exact prefixLift 5762112
  have htrace : WordTrace (prefixWord ++ tailWord_5762112) baseStart_5762112 baseEnd_5762112 := by
    simpa [prefixWord, tailWord_5762112, baseEnd_5762112] using wordTrace_append hprefix tailTrace_5762112
  have hstable : (prefixWord ++ tailWord_5762112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762112).length < 2 ^ (prefixWord ++ tailWord_5762112).sum := by decide
  have hdescent : baseEnd_5762112 < baseStart_5762112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762122 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_5762122 : Nat := 118140960795 + 5762122 * 2 ^ 59
def prefixEnd_5762122 : Nat := 4983230072969 + 3 ^ 40 * 5762122 * 2
def baseEnd_5762122 : Nat := 2958738175846409904875489

theorem tailTrace_5762122 : CollatzResearch.WordTrace tailWord_5762122 prefixEnd_5762122 2958738175846409904875489 := by
  unfold tailWord_5762122
  simp only [CollatzResearch.WordTrace]
  refine ⟨52540463707705890233784155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140107903220549040623424413 52540463707705890233784155)
  ·
    refine ⟨78810695561558835350676233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52540463707705890233784155 78810695561558835350676233)
    ·
      refine ⟨59108021671169126513007175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78810695561558835350676233 59108021671169126513007175)
      ·
        refine ⟨88662032506753689769510763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59108021671169126513007175 88662032506753689769510763)
        ·
          refine ⟨132993048760130534654266145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88662032506753689769510763 132993048760130534654266145)
          ·
            refine ⟨99744786570097900990699609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132993048760130534654266145 99744786570097900990699609)
            ·
              refine ⟨74808589927573425743024707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99744786570097900990699609 74808589927573425743024707)
              ·
                refine ⟨112212884891360138614537061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74808589927573425743024707 112212884891360138614537061)
                ·
                  refine ⟨21039915917130025990225699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112212884891360138614537061 21039915917130025990225699)
                  ·
                    refine ⟨31559873875695038985338549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21039915917130025990225699 31559873875695038985338549)
                    ·
                      refine ⟨2958738175846409904875489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31559873875695038985338549 2958738175846409904875489)
                      ·
                        rfl

theorem cell23_5762122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_5762122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762122 prefixEnd_5762122 := by exact prefixLift 5762122
  have htrace : WordTrace (prefixWord ++ tailWord_5762122) baseStart_5762122 baseEnd_5762122 := by
    simpa [prefixWord, tailWord_5762122, baseEnd_5762122] using wordTrace_append hprefix tailTrace_5762122
  have hstable : (prefixWord ++ tailWord_5762122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762122).length < 2 ^ (prefixWord ++ tailWord_5762122).sum := by decide
  have hdescent : baseEnd_5762122 < baseStart_5762122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762134 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_5762134 : Nat := 118140960795 + 5762134 * 2 ^ 59
def prefixEnd_5762134 : Nat := 4983230072969 + 3 ^ 40 * 5762134 * 2
def baseEnd_5762134 : Nat := 2958744337614263857925435

theorem tailTrace_5762134 : CollatzResearch.WordTrace tailWord_5762134 prefixEnd_5762134 2958744337614263857925435 := by
  unfold tailWord_5762134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13135143281673755436535841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140108195004520057989715637 13135143281673755436535841)
  ·
    refine ⟨9851357461255316577401881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13135143281673755436535841 9851357461255316577401881)
    ·
      refine ⟨7388518095941487433051411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9851357461255316577401881 7388518095941487433051411)
      ·
        refine ⟨11082777143912231149577117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388518095941487433051411 11082777143912231149577117)
        ·
          refine ⟨4156041428967086681091419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11082777143912231149577117 4156041428967086681091419)
          ·
            refine ⟨6234062143450630021637129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156041428967086681091419 6234062143450630021637129)
            ·
              refine ⟨4675546607587972516227847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6234062143450630021637129 4675546607587972516227847)
              ·
                refine ⟨7013319911381958774341771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675546607587972516227847 7013319911381958774341771)
                ·
                  refine ⟨10519979867072938161512657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013319911381958774341771 10519979867072938161512657)
                  ·
                    refine ⟨7889984900304703621134493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10519979867072938161512657 7889984900304703621134493)
                    ·
                      refine ⟨2958744337614263857925435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7889984900304703621134493 2958744337614263857925435)
                      ·
                        rfl

theorem cell23_5762134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_5762134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762134 prefixEnd_5762134 := by exact prefixLift 5762134
  have htrace : WordTrace (prefixWord ++ tailWord_5762134) baseStart_5762134 baseEnd_5762134 := by
    simpa [prefixWord, tailWord_5762134, baseEnd_5762134] using wordTrace_append hprefix tailTrace_5762134
  have hstable : (prefixWord ++ tailWord_5762134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762134).length < 2 ^ (prefixWord ++ tailWord_5762134).sum := by decide
  have hdescent : baseEnd_5762134 < baseStart_5762134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762136 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_5762136 : Nat := 118140960795 + 5762136 * 2 ^ 59
def prefixEnd_5762136 : Nat := 4983230072969 + 3 ^ 40 * 5762136 * 2
def baseEnd_5762136 : Nat := 2958745364575572850100425

theorem tailTrace_5762136 : CollatzResearch.WordTrace tailWord_5762136 prefixEnd_5762136 2958745364575572850100425 := by
  unfold tailWord_5762136
  simp only [CollatzResearch.WordTrace]
  refine ⟨105081182726386420663073131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140108243635181894217430841 105081182726386420663073131)
  ·
    refine ⟨157621774089579630994609697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105081182726386420663073131 157621774089579630994609697)
    ·
      refine ⟨118216330567184723245957273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157621774089579630994609697 118216330567184723245957273)
      ·
        refine ⟨88662247925388542434467955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118216330567184723245957273 88662247925388542434467955)
        ·
          refine ⟨132993371888082813651701933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88662247925388542434467955 132993371888082813651701933)
          ·
            refine ⟨49872514458031055119388225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132993371888082813651701933 49872514458031055119388225)
            ·
              refine ⟨37404385843523291339541169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49872514458031055119388225 37404385843523291339541169)
              ·
                refine ⟨28053289382642468504655877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37404385843523291339541169 28053289382642468504655877)
                ·
                  refine ⟨5259991759245462844622977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28053289382642468504655877 5259991759245462844622977)
                  ·
                    refine ⟨3944993819434097133467233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5259991759245462844622977 3944993819434097133467233)
                    ·
                      refine ⟨2958745364575572850100425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3944993819434097133467233 2958745364575572850100425)
                      ·
                        rfl

theorem cell23_5762136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_5762136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762136 prefixEnd_5762136 := by exact prefixLift 5762136
  have htrace : WordTrace (prefixWord ++ tailWord_5762136) baseStart_5762136 baseEnd_5762136 := by
    simpa [prefixWord, tailWord_5762136, baseEnd_5762136] using wordTrace_append hprefix tailTrace_5762136
  have hstable : (prefixWord ++ tailWord_5762136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762136).length < 2 ^ (prefixWord ++ tailWord_5762136).sum := by decide
  have hdescent : baseEnd_5762136 < baseStart_5762136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762153 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 2, 2, 2]
def baseStart_5762153 : Nat := 118140960795 + 5762153 * 2 ^ 59
def prefixEnd_5762153 : Nat := 4983230072969 + 3 ^ 40 * 5762153 * 2
def baseEnd_5762153 : Nat := 2958754093746699283587847

theorem tailTrace_5762153 : CollatzResearch.WordTrace tailWord_5762153 prefixEnd_5762153 2958754093746699283587847 := by
  unfold tailWord_5762153
  simp only [CollatzResearch.WordTrace]
  refine ⟨210162985493711253229515113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140108656995807502153010075 210162985493711253229515113)
  ·
    refine ⟨157622239120283439922136335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210162985493711253229515113 157622239120283439922136335)
    ·
      refine ⟨236433358680425159883204503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157622239120283439922136335 236433358680425159883204503)
      ·
        refine ⟨354650038020637739824806755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236433358680425159883204503 354650038020637739824806755)
        ·
          refine ⟨531975057030956609737210133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354650038020637739824806755 531975057030956609737210133)
          ·
            refine ⟨24936330798326091081431725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 531975057030956609737210133 24936330798326091081431725)
            ·
              refine ⟨9351124049372284155536897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24936330798326091081431725 9351124049372284155536897)
              ·
                refine ⟨7013343037029213116652673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351124049372284155536897 7013343037029213116652673)
                ·
                  refine ⟨5260007277771909837489505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013343037029213116652673 5260007277771909837489505)
                  ·
                    refine ⟨3945005458328932378117129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260007277771909837489505 3945005458328932378117129)
                    ·
                      refine ⟨2958754093746699283587847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945005458328932378117129 2958754093746699283587847)
                      ·
                        rfl

theorem cell23_5762153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2, 2].length) (baseStart_5762153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762153 prefixEnd_5762153 := by exact prefixLift 5762153
  have htrace : WordTrace (prefixWord ++ tailWord_5762153) baseStart_5762153 baseEnd_5762153 := by
    simpa [prefixWord, tailWord_5762153, baseEnd_5762153] using wordTrace_append hprefix tailTrace_5762153
  have hstable : (prefixWord ++ tailWord_5762153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762153).length < 2 ^ (prefixWord ++ tailWord_5762153).sum := by decide
  have hdescent : baseEnd_5762153 < baseStart_5762153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762159 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 5]
def baseStart_5762159 : Nat := 118140960795 + 5762159 * 2 ^ 59
def prefixEnd_5762159 : Nat := 4983230072969 + 3 ^ 40 * 5762159 * 2
def baseEnd_5762159 : Nat := 328750797181180695568091

theorem tailTrace_5762159 : CollatzResearch.WordTrace tailWord_5762159 prefixEnd_5762159 328750797181180695568091 := by
  unfold tailWord_5762159
  simp only [CollatzResearch.WordTrace]
  refine ⟨210163204331689516254233531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140108802887793010836155687 210163204331689516254233531)
  ·
    refine ⟨315244806497534274381350297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210163204331689516254233531 315244806497534274381350297)
    ·
      refine ⟨236433604873150705786012723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315244806497534274381350297 236433604873150705786012723)
      ·
        refine ⟨354650407309726058679019085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236433604873150705786012723 354650407309726058679019085)
        ·
          refine ⟨132993902741147272004632157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354650407309726058679019085 132993902741147272004632157)
          ·
            refine ⟨49872713527930227001737059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132993902741147272004632157 49872713527930227001737059)
            ·
              refine ⟨74809070291895340502605589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49872713527930227001737059 74809070291895340502605589)
              ·
                refine ⟨3506675169932594086059637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74809070291895340502605589 3506675169932594086059637)
                ·
                  refine ⟨328750797181180695568091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506675169932594086059637 328750797181180695568091)
                  ·
                    rfl

theorem cell23_5762159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 5].length) (baseStart_5762159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762159 prefixEnd_5762159 := by exact prefixLift 5762159
  have htrace : WordTrace (prefixWord ++ tailWord_5762159) baseStart_5762159 baseEnd_5762159 := by
    simpa [prefixWord, tailWord_5762159, baseEnd_5762159] using wordTrace_append hprefix tailTrace_5762159
  have hstable : (prefixWord ++ tailWord_5762159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762159).length < 2 ^ (prefixWord ++ tailWord_5762159).sum := by decide
  have hdescent : baseEnd_5762159 < baseStart_5762159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762172 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_5762172 : Nat := 118140960795 + 5762172 * 2 ^ 59
def prefixEnd_5762172 : Nat := 4983230072969 + 3 ^ 40 * 5762172 * 2
def baseEnd_5762172 : Nat := 986254616626378236416753

theorem tailTrace_5762172 : CollatzResearch.WordTrace tailWord_5762172 prefixEnd_5762172 986254616626378236416753 := by
  unfold tailWord_5762172
  simp only [CollatzResearch.WordTrace]
  refine ⟨105081839240321209737228385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140109118987094946316304513 105081839240321209737228385)
  ·
    refine ⟨78811379430240907302921289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105081839240321209737228385 78811379430240907302921289)
    ·
      refine ⟨59108534572680680477190967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78811379430240907302921289 59108534572680680477190967)
      ·
        refine ⟨88662801859021020715786451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59108534572680680477190967 88662801859021020715786451)
        ·
          refine ⟨132994202788531531073679677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88662801859021020715786451 132994202788531531073679677)
          ·
            refine ⟨49872826045699324152629879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132994202788531531073679677 49872826045699324152629879)
            ·
              refine ⟨74809239068548986228944819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49872826045699324152629879 74809239068548986228944819)
              ·
                refine ⟨112213858602823479343417229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74809239068548986228944819 112213858602823479343417229)
                ·
                  refine ⟨42080196976058804753781461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112213858602823479343417229 42080196976058804753781461)
                  ·
                    refine ⟨986254616626378236416753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42080196976058804753781461 986254616626378236416753)
                    ·
                      rfl

theorem cell23_5762172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_5762172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762172 prefixEnd_5762172 := by exact prefixLift 5762172
  have htrace : WordTrace (prefixWord ++ tailWord_5762172) baseStart_5762172 baseEnd_5762172 := by
    simpa [prefixWord, tailWord_5762172, baseEnd_5762172] using wordTrace_append hprefix tailTrace_5762172
  have hstable : (prefixWord ++ tailWord_5762172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762172).length < 2 ^ (prefixWord ++ tailWord_5762172).sum := by decide
  have hdescent : baseEnd_5762172 < baseStart_5762172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762174 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5762174 : Nat := 118140960795 + 5762174 * 2 ^ 59
def prefixEnd_5762174 : Nat := 4983230072969 + 3 ^ 40 * 5762174 * 2
def baseEnd_5762174 : Nat := 2958764876840443701425251

theorem tailTrace_5762174 : CollatzResearch.WordTrace tailWord_5762174 prefixEnd_5762174 2958764876840443701425251 := by
  unfold tailWord_5762174
  simp only [CollatzResearch.WordTrace]
  refine ⟨26270468928329396727003697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140109167617756782544019717 26270468928329396727003697)
  ·
    refine ⟨19702851696247047545252773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26270468928329396727003697 19702851696247047545252773)
    ·
      refine ⟨3694284693046321414734895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19702851696247047545252773 3694284693046321414734895)
      ·
        refine ⟨5541427039569482122102343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694284693046321414734895 5541427039569482122102343)
        ·
          refine ⟨8312140559354223183153515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541427039569482122102343 8312140559354223183153515)
          ·
            refine ⟨12468210839031334774730273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312140559354223183153515 12468210839031334774730273)
            ·
              refine ⟨9351158129273501081047705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12468210839031334774730273 9351158129273501081047705)
              ·
                refine ⟨7013368596955125810785779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351158129273501081047705 7013368596955125810785779)
                ·
                  refine ⟨10520052895432688716178669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013368596955125810785779 10520052895432688716178669)
                  ·
                    refine ⟨3945019835787258268567001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10520052895432688716178669 3945019835787258268567001)
                    ·
                      refine ⟨2958764876840443701425251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945019835787258268567001 2958764876840443701425251)
                      ·
                        rfl

theorem cell23_5762174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5762174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762174 prefixEnd_5762174 := by exact prefixLift 5762174
  have htrace : WordTrace (prefixWord ++ tailWord_5762174) baseStart_5762174 baseEnd_5762174 := by
    simpa [prefixWord, tailWord_5762174, baseEnd_5762174] using wordTrace_append hprefix tailTrace_5762174
  have hstable : (prefixWord ++ tailWord_5762174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762174).length < 2 ^ (prefixWord ++ tailWord_5762174).sum := by decide
  have hdescent : baseEnd_5762174 < baseStart_5762174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762206 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5762206 : Nat := 118140960795 + 5762206 * 2 ^ 59
def prefixEnd_5762206 : Nat := 4983230072969 + 3 ^ 40 * 5762206 * 2
def baseEnd_5762206 : Nat := 986260436073795858741701

theorem tailTrace_5762206 : CollatzResearch.WordTrace tailWord_5762206 prefixEnd_5762206 986260436073795858741701 := by
  unfold tailWord_5762206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26270614820314905410149309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140109945708346162187462981 26270614820314905410149309)
  ·
    refine ⟨9851480557618089528805991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26270614820314905410149309 9851480557618089528805991)
    ·
      refine ⟨14777220836427134293208987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9851480557618089528805991 14777220836427134293208987)
      ·
        refine ⟨22165831254640701439813481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14777220836427134293208987 22165831254640701439813481)
        ·
          refine ⟨16624373440980526079860111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22165831254640701439813481 16624373440980526079860111)
          ·
            refine ⟨24936560161470789119790167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16624373440980526079860111 24936560161470789119790167)
            ·
              refine ⟨37404840242206183679685251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24936560161470789119790167 37404840242206183679685251)
              ·
                refine ⟨56107260363309275519527877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37404840242206183679685251 56107260363309275519527877)
                ·
                  refine ⟨10520111318120489159911477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56107260363309275519527877 10520111318120489159911477)
                  ·
                    refine ⟨986260436073795858741701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10520111318120489159911477 986260436073795858741701)
                    ·
                      rfl

theorem cell23_5762206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5762206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762206 prefixEnd_5762206 := by exact prefixLift 5762206
  have htrace : WordTrace (prefixWord ++ tailWord_5762206) baseStart_5762206 baseEnd_5762206 := by
    simpa [prefixWord, tailWord_5762206, baseEnd_5762206] using wordTrace_append hprefix tailTrace_5762206
  have hstable : (prefixWord ++ tailWord_5762206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762206).length < 2 ^ (prefixWord ++ tailWord_5762206).sum := by decide
  have hdescent : baseEnd_5762206 < baseStart_5762206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762210 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_5762210 : Nat := 118140960795 + 5762210 * 2 ^ 59
def prefixEnd_5762210 : Nat := 4983230072969 + 3 ^ 40 * 5762210 * 2
def baseEnd_5762210 : Nat := 328753706904889506730565

theorem tailTrace_5762210 : CollatzResearch.WordTrace tailWord_5762210 prefixEnd_5762210 328753706904889506730565 := by
  unfold tailWord_5762210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52541266113626187991085021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140110042969669834642893389 52541266113626187991085021)
  ·
    refine ⟨19702974792609820496656883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52541266113626187991085021 19702974792609820496656883)
    ·
      refine ⟨29554462188914730744985325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19702974792609820496656883 29554462188914730744985325)
      ·
        refine ⟨11082923320843024029369497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29554462188914730744985325 11082923320843024029369497)
        ·
          refine ⟨8312192490632268022027123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11082923320843024029369497 8312192490632268022027123)
          ·
            refine ⟨12468288735948402033040685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312192490632268022027123 12468288735948402033040685)
            ·
              refine ⟨4675608275980650762390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12468288735948402033040685 4675608275980650762390257)
              ·
                refine ⟨3506706206985488071792693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4675608275980650762390257 3506706206985488071792693)
                ·
                  refine ⟨328753706904889506730565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506706206985488071792693 328753706904889506730565)
                  ·
                    rfl

theorem cell23_5762210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_5762210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762210 prefixEnd_5762210 := by exact prefixLift 5762210
  have htrace : WordTrace (prefixWord ++ tailWord_5762210) baseStart_5762210 baseEnd_5762210 := by
    simpa [prefixWord, tailWord_5762210, baseEnd_5762210] using wordTrace_append hprefix tailTrace_5762210
  have hstable : (prefixWord ++ tailWord_5762210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762210).length < 2 ^ (prefixWord ++ tailWord_5762210).sum := by decide
  have hdescent : baseEnd_5762210 < baseStart_5762210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762232 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 10]
def baseStart_5762232 : Nat := 118140960795 + 5762232 * 2 ^ 59
def prefixEnd_5762232 : Nat := 4983230072969 + 3 ^ 40 * 5762232 * 2
def baseEnd_5762232 : Nat := 328754962079822719388887

theorem tailTrace_5762232 : CollatzResearch.WordTrace tailWord_5762232 prefixEnd_5762232 328754962079822719388887 := by
  unfold tailWord_5762232
  simp only [CollatzResearch.WordTrace]
  refine ⟨105082933430212524860820475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140110577906950033147760633 105082933430212524860820475)
  ·
    refine ⟨157624400145318787291230713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105082933430212524860820475 157624400145318787291230713)
    ·
      refine ⟨118218300108989090468423035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157624400145318787291230713 118218300108989090468423035)
      ·
        refine ⟨177327450163483635702634553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118218300108989090468423035 177327450163483635702634553)
        ·
          refine ⟨132995587622612726776975915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177327450163483635702634553 132995587622612726776975915)
          ·
            refine ⟨199493381433919090165463873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132995587622612726776975915 199493381433919090165463873)
            ·
              refine ⟨149620036075439317624097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199493381433919090165463873 149620036075439317624097905)
              ·
                refine ⟨112215027056579488218073429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149620036075439317624097905 112215027056579488218073429)
                ·
                  refine ⟨328754962079822719388887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112215027056579488218073429 328754962079822719388887)
                  ·
                    rfl

theorem cell23_5762232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_5762232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762232 prefixEnd_5762232 := by exact prefixLift 5762232
  have htrace : WordTrace (prefixWord ++ tailWord_5762232) baseStart_5762232 baseEnd_5762232 := by
    simpa [prefixWord, tailWord_5762232, baseEnd_5762232] using wordTrace_append hprefix tailTrace_5762232
  have hstable : (prefixWord ++ tailWord_5762232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762232).length < 2 ^ (prefixWord ++ tailWord_5762232).sum := by decide
  have hdescent : baseEnd_5762232 < baseStart_5762232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762303 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 2, 3, 2]
def baseStart_5762303 : Nat := 118140960795 + 5762303 * 2 ^ 59
def prefixEnd_5762303 : Nat := 4983230072969 + 3 ^ 40 * 5762303 * 2
def baseEnd_5762303 : Nat := 2958831115844873696712157

theorem tailTrace_5762303 : CollatzResearch.WordTrace tailWord_5762303 prefixEnd_5762303 2958831115844873696712157 := by
  unfold tailWord_5762303
  simp only [CollatzResearch.WordTrace]
  refine ⟨210168456443167828847475563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140112304295445219231650375 210168456443167828847475563)
  ·
    refine ⟨315252684664751743271213345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210168456443167828847475563 315252684664751743271213345)
    ·
      refine ⟨236439513498563807453410009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315252684664751743271213345 236439513498563807453410009)
      ·
        refine ⟨177329635123922855590057507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236439513498563807453410009 177329635123922855590057507)
        ·
          refine ⟨265994452685884283385086261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177329635123922855590057507 265994452685884283385086261)
          ·
            refine ⟨24936979939301651567351837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265994452685884283385086261 24936979939301651567351837)
            ·
              refine ⟨9351367477238119337756939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24936979939301651567351837 9351367477238119337756939)
              ·
                refine ⟨14027051215857179006635409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9351367477238119337756939 14027051215857179006635409)
                ·
                  refine ⟨10520288411892884254976557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14027051215857179006635409 10520288411892884254976557)
                  ·
                    refine ⟨3945108154459831595616209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10520288411892884254976557 3945108154459831595616209)
                    ·
                      refine ⟨2958831115844873696712157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945108154459831595616209 2958831115844873696712157)
                      ·
                        rfl

theorem cell23_5762303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_5762303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762303 prefixEnd_5762303 := by exact prefixLift 5762303
  have htrace : WordTrace (prefixWord ++ tailWord_5762303) baseStart_5762303 baseEnd_5762303 := by
    simpa [prefixWord, tailWord_5762303, baseEnd_5762303] using wordTrace_append hprefix tailTrace_5762303
  have hstable : (prefixWord ++ tailWord_5762303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762303).length < 2 ^ (prefixWord ++ tailWord_5762303).sum := by decide
  have hdescent : baseEnd_5762303 < baseStart_5762303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762309 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_5762309 : Nat := 118140960795 + 5762309 * 2 ^ 59
def prefixEnd_5762309 : Nat := 4983230072969 + 3 ^ 40 * 5762309 * 2
def baseEnd_5762309 : Nat := 986278065576266891079043

theorem tailTrace_5762309 : CollatzResearch.WordTrace tailWord_5762309 prefixEnd_5762309 986278065576266891079043 := by
  unfold tailWord_5762309
  simp only [CollatzResearch.WordTrace]
  refine ⟨210168675281146091872193981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140112450187430727914795987 210168675281146091872193981)
  ·
    refine ⟨78813253230429784452072743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210168675281146091872193981 78813253230429784452072743)
    ·
      refine ⟨118219879845644676678109115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78813253230429784452072743 118219879845644676678109115)
      ·
        refine ⟨177329819768467015017163673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118219879845644676678109115 177329819768467015017163673)
        ·
          refine ⟨132997364826350261262872755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177329819768467015017163673 132997364826350261262872755)
          ·
            refine ⟨199496047239525391894309133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132997364826350261262872755 199496047239525391894309133)
            ·
              refine ⟨74811017714822021960365925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199496047239525391894309133 74811017714822021960365925)
              ·
                refine ⟨14027065821529129117568611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74811017714822021960365925 14027065821529129117568611)
                ·
                  refine ⟨21040598732293693676352917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14027065821529129117568611 21040598732293693676352917)
                  ·
                    refine ⟨986278065576266891079043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21040598732293693676352917 986278065576266891079043)
                    ·
                      rfl

theorem cell23_5762309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_5762309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762309 prefixEnd_5762309 := by exact prefixLift 5762309
  have htrace : WordTrace (prefixWord ++ tailWord_5762309) baseStart_5762309 baseEnd_5762309 := by
    simpa [prefixWord, tailWord_5762309, baseEnd_5762309] using wordTrace_append hprefix tailTrace_5762309
  have hstable : (prefixWord ++ tailWord_5762309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762309).length < 2 ^ (prefixWord ++ tailWord_5762309).sum := by decide
  have hdescent : baseEnd_5762309 < baseStart_5762309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762353 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_5762353 : Nat := 118140960795 + 5762353 * 2 ^ 59
def prefixEnd_5762353 : Nat := 4983230072969 + 3 ^ 40 * 5762353 * 2
def baseEnd_5762353 : Nat := 2958856789877598501086927

theorem tailTrace_5762353 : CollatzResearch.WordTrace tailWord_5762353 prefixEnd_5762353 2958856789877598501086927 := by
  unfold tailWord_5762353
  simp only [CollatzResearch.WordTrace]
  refine ⟨210170280092986687386795713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140113520061991124924530475 210170280092986687386795713)
  ·
    refine ⟨157627710069740015540096785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210170280092986687386795713 157627710069740015540096785)
    ·
      refine ⟨118220782552305011655072589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157627710069740015540096785 118220782552305011655072589)
      ·
        refine ⟨44332793457114379370652221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118220782552305011655072589 44332793457114379370652221)
        ·
          refine ⟨16624797546417892263994583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44332793457114379370652221 16624797546417892263994583)
          ·
            refine ⟨24937196319626838395991875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16624797546417892263994583 24937196319626838395991875)
            ·
              refine ⟨37405794479440257593987813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24937196319626838395991875 37405794479440257593987813)
              ·
                refine ⟨7013586464895048298872715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37405794479440257593987813 7013586464895048298872715)
                ·
                  refine ⟨10520379697342572448309073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013586464895048298872715 10520379697342572448309073)
                  ·
                    refine ⟨7890284773006929336231805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10520379697342572448309073 7890284773006929336231805)
                    ·
                      refine ⟨2958856789877598501086927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890284773006929336231805 2958856789877598501086927)
                      ·
                        rfl

theorem cell23_5762353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_5762353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762353 prefixEnd_5762353 := by exact prefixLift 5762353
  have htrace : WordTrace (prefixWord ++ tailWord_5762353) baseStart_5762353 baseEnd_5762353 := by
    simpa [prefixWord, tailWord_5762353, baseEnd_5762353] using wordTrace_append hprefix tailTrace_5762353
  have hstable : (prefixWord ++ tailWord_5762353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762353).length < 2 ^ (prefixWord ++ tailWord_5762353).sum := by decide
  have hdescent : baseEnd_5762353 < baseStart_5762353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762356 : List Nat := [2, 5, 1, 1, 1, 1, 3, 9]
def baseStart_5762356 : Nat := 118140960795 + 5762356 * 2 ^ 59
def prefixEnd_5762356 : Nat := 4983230072969 + 3 ^ 40 * 5762356 * 2
def baseEnd_5762356 : Nat := 109587345567391184790719

theorem tailTrace_5762356 : CollatzResearch.WordTrace tailWord_5762356 prefixEnd_5762356 109587345567391184790719 := by
  unfold tailWord_5762356
  simp only [CollatzResearch.WordTrace]
  refine ⟨105085194755987909449577461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140113593007983879266103281 105085194755987909449577461)
  ·
    refine ⟨9851737008373866510897887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105085194755987909449577461 9851737008373866510897887)
    ·
      refine ⟨14777605512560799766346831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9851737008373866510897887 14777605512560799766346831)
      ·
        refine ⟨22166408268841199649520247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14777605512560799766346831 22166408268841199649520247)
        ·
          refine ⟨33249612403261799474280371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22166408268841199649520247 33249612403261799474280371)
          ·
            refine ⟨49874418604892699211420557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33249612403261799474280371 49874418604892699211420557)
            ·
              refine ⟨18702906976834762204282709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49874418604892699211420557 18702906976834762204282709)
              ·
                refine ⟨109587345567391184790719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18702906976834762204282709 109587345567391184790719)
                ·
                  rfl

theorem cell23_5762356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 9].length) (baseStart_5762356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762356 prefixEnd_5762356 := by exact prefixLift 5762356
  have htrace : WordTrace (prefixWord ++ tailWord_5762356) baseStart_5762356 baseEnd_5762356 := by
    simpa [prefixWord, tailWord_5762356, baseEnd_5762356] using wordTrace_append hprefix tailTrace_5762356
  have hstable : (prefixWord ++ tailWord_5762356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762356).length < 2 ^ (prefixWord ++ tailWord_5762356).sum := by decide
  have hdescent : baseEnd_5762356 < baseStart_5762356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762367 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 1, 2, 2]
def baseStart_5762367 : Nat := 118140960795 + 5762367 * 2 ^ 59
def prefixEnd_5762367 : Nat := 4983230072969 + 3 ^ 40 * 5762367 * 2
def baseEnd_5762367 : Nat := 2958863978606761446311863

theorem tailTrace_5762367 : CollatzResearch.WordTrace tailWord_5762367 prefixEnd_5762367 2958863978606761446311863 := by
  unfold tailWord_5762367
  simp only [CollatzResearch.WordTrace]
  refine ⟨210170790714935967777805355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140113860476623978518536903 210170790714935967777805355)
  ·
    refine ⟨315256186072403951666708033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210170790714935967777805355 315256186072403951666708033)
    ·
      refine ⟨236442139554302963750031025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315256186072403951666708033 236442139554302963750031025)
      ·
        refine ⟨177331604665727222812523269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236442139554302963750031025 177331604665727222812523269)
        ·
          refine ⟨33249675874823854277348113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177331604665727222812523269 33249675874823854277348113)
          ·
            refine ⟨24937256906117890708011085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33249675874823854277348113 24937256906117890708011085)
            ·
              refine ⟨9351471339794209015504157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24937256906117890708011085 9351471339794209015504157)
              ·
                refine ⟨3506801752422828380814059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9351471339794209015504157 3506801752422828380814059)
                ·
                  refine ⟨5260202628634242571221089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506801752422828380814059 5260202628634242571221089)
                  ·
                    refine ⟨3945151971475681928415817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260202628634242571221089 3945151971475681928415817)
                    ·
                      refine ⟨2958863978606761446311863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945151971475681928415817 2958863978606761446311863)
                      ·
                        rfl

theorem cell23_5762367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_5762367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762367 prefixEnd_5762367 := by exact prefixLift 5762367
  have htrace : WordTrace (prefixWord ++ tailWord_5762367) baseStart_5762367 baseEnd_5762367 := by
    simpa [prefixWord, tailWord_5762367, baseEnd_5762367] using wordTrace_append hprefix tailTrace_5762367
  have hstable : (prefixWord ++ tailWord_5762367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762367).length < 2 ^ (prefixWord ++ tailWord_5762367).sum := by decide
  have hdescent : baseEnd_5762367 < baseStart_5762367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762399 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 8]
def baseStart_5762399 : Nat := 118140960795 + 5762399 * 2 ^ 59
def prefixEnd_5762399 : Nat := 4983230072969 + 3 ^ 40 * 5762399 * 2
def baseEnd_5762399 : Nat := 986293469995901773703905

theorem tailTrace_5762399 : CollatzResearch.WordTrace tailWord_5762399 prefixEnd_5762399 986293469995901773703905 := by
  unfold tailWord_5762399
  simp only [CollatzResearch.WordTrace]
  refine ⟨210171957850820037242970251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140114638567213358161980167 210171957850820037242970251)
  ·
    refine ⟨315257936776230055864455377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210171957850820037242970251 315257936776230055864455377)
    ·
      refine ⟨236443452582172541898341533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315257936776230055864455377 236443452582172541898341533)
      ·
        refine ⟨88666294718314703211878075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236443452582172541898341533 88666294718314703211878075)
        ·
          refine ⟨132999442077472054817817113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88666294718314703211878075 132999442077472054817817113)
          ·
            refine ⟨99749581558104041113362835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132999442077472054817817113 99749581558104041113362835)
            ·
              refine ⟨149624372337156061670044253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99749581558104041113362835 149624372337156061670044253)
              ·
                refine ⟨56109139626433523126266595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149624372337156061670044253 56109139626433523126266595)
                ·
                  refine ⟨84163709439650284689399893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56109139626433523126266595 84163709439650284689399893)
                  ·
                    refine ⟨986293469995901773703905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84163709439650284689399893 986293469995901773703905)
                    ·
                      rfl

theorem cell23_5762399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_5762399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762399 prefixEnd_5762399 := by exact prefixLift 5762399
  have htrace : WordTrace (prefixWord ++ tailWord_5762399) baseStart_5762399 baseEnd_5762399 := by
    simpa [prefixWord, tailWord_5762399, baseEnd_5762399] using wordTrace_append hprefix tailTrace_5762399
  have hstable : (prefixWord ++ tailWord_5762399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762399).length < 2 ^ (prefixWord ++ tailWord_5762399).sum := by decide
  have hdescent : baseEnd_5762399 < baseStart_5762399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762400 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_5762400 : Nat := 118140960795 + 5762400 * 2 ^ 59
def prefixEnd_5762400 : Nat := 4983230072969 + 3 ^ 40 * 5762400 * 2
def baseEnd_5762400 : Nat := 2958880923468359817199211

theorem tailTrace_5762400 : CollatzResearch.WordTrace tailWord_5762400 prefixEnd_5762400 2958880923468359817199211 := by
  unfold tailWord_5762400
  simp only [CollatzResearch.WordTrace]
  refine ⟨105085997161908207206878327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140114662882544276275837769 105085997161908207206878327)
  ·
    refine ⟨157628995742862310810317491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105085997161908207206878327 157628995742862310810317491)
    ·
      refine ⟨236443493614293466215476237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157628995742862310810317491 236443493614293466215476237)
      ·
        refine ⟨88666310105360049830803589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236443493614293466215476237 88666310105360049830803589)
        ·
          refine ⟨16624933144755009343275673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88666310105360049830803589 16624933144755009343275673)
          ·
            refine ⟨12468699858566257007456755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16624933144755009343275673 12468699858566257007456755)
            ·
              refine ⟨18703049787849385511185133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12468699858566257007456755 18703049787849385511185133)
              ·
                refine ⟨7013643670443519566694425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18703049787849385511185133 7013643670443519566694425)
                ·
                  refine ⟨5260232752832639675020819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013643670443519566694425 5260232752832639675020819)
                  ·
                    refine ⟨7890349129248959512531229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260232752832639675020819 7890349129248959512531229)
                    ·
                      refine ⟨2958880923468359817199211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890349129248959512531229 2958880923468359817199211)
                      ·
                        rfl

theorem cell23_5762400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_5762400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762400 prefixEnd_5762400 := by exact prefixLift 5762400
  have htrace : WordTrace (prefixWord ++ tailWord_5762400) baseStart_5762400 baseEnd_5762400 := by
    simpa [prefixWord, tailWord_5762400, baseEnd_5762400] using wordTrace_append hprefix tailTrace_5762400
  have hstable : (prefixWord ++ tailWord_5762400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762400).length < 2 ^ (prefixWord ++ tailWord_5762400).sum := by decide
  have hdescent : baseEnd_5762400 < baseStart_5762400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762423 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_5762423 : Nat := 118140960795 + 5762423 * 2 ^ 59
def prefixEnd_5762423 : Nat := 4983230072969 + 3 ^ 40 * 5762423 * 2
def baseEnd_5762423 : Nat := 2958892733523413227211605

theorem tailTrace_5762423 : CollatzResearch.WordTrace tailWord_5762423 prefixEnd_5762423 2958892733523413227211605 := by
  unfold tailWord_5762423
  simp only [CollatzResearch.WordTrace]
  refine ⟨210172833202733089341843923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140115222135155392894562615 210172833202733089341843923)
  ·
    refine ⟨315259249804099634012765885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210172833202733089341843923 315259249804099634012765885)
    ·
      refine ⟨118222218676537362754787207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315259249804099634012765885 118222218676537362754787207)
      ·
        refine ⟨177333328014806044132180811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118222218676537362754787207 177333328014806044132180811)
        ·
          refine ⟨265999992022209066198271217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177333328014806044132180811 265999992022209066198271217)
          ·
            refine ⟨199499994016656799648703413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265999992022209066198271217 199499994016656799648703413)
            ·
              refine ⟨18703124439061574967065945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199499994016656799648703413 18703124439061574967065945)
              ·
                refine ⟨14027343329296181225299459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18703124439061574967065945 14027343329296181225299459)
                ·
                  refine ⟨21041014993944271837949189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14027343329296181225299459 21041014993944271837949189)
                  ·
                    refine ⟨3945190311364550969615473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21041014993944271837949189 3945190311364550969615473)
                    ·
                      refine ⟨2958892733523413227211605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945190311364550969615473 2958892733523413227211605)
                      ·
                        rfl

theorem cell23_5762423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_5762423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762423 prefixEnd_5762423 := by exact prefixLift 5762423
  have htrace : WordTrace (prefixWord ++ tailWord_5762423) baseStart_5762423 baseEnd_5762423 := by
    simpa [prefixWord, tailWord_5762423, baseEnd_5762423] using wordTrace_append hprefix tailTrace_5762423
  have hstable : (prefixWord ++ tailWord_5762423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762423).length < 2 ^ (prefixWord ++ tailWord_5762423).sum := by decide
  have hdescent : baseEnd_5762423 < baseStart_5762423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762434 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_5762434 : Nat := 118140960795 + 5762434 * 2 ^ 59
def prefixEnd_5762434 : Nat := 4983230072969 + 3 ^ 40 * 5762434 * 2
def baseEnd_5762434 : Nat := 2958898381810612684174055

theorem tailTrace_5762434 : CollatzResearch.WordTrace tailWord_5762434 prefixEnd_5762434 2958898381810612684174055 := by
  unfold tailWord_5762434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52543308601423309555123589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140115489603795492146996237 52543308601423309555123589)
  ·
    refine ⟨9851870362766870541585673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52543308601423309555123589 9851870362766870541585673)
    ·
      refine ⟨7388902772075152906189255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9851870362766870541585673 7388902772075152906189255)
      ·
        refine ⟨11083354158112729359283883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388902772075152906189255 11083354158112729359283883)
        ·
          refine ⟨16625031237169094038925825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11083354158112729359283883 16625031237169094038925825)
          ·
            refine ⟨12468773427876820529194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16625031237169094038925825 12468773427876820529194369)
            ·
              refine ⟨9351580070907615396895777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12468773427876820529194369 9351580070907615396895777)
              ·
                refine ⟨7013685053180711547671833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351580070907615396895777 7013685053180711547671833)
                ·
                  refine ⟨5260263789885533660753875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013685053180711547671833 5260263789885533660753875)
                  ·
                    refine ⟨7890395684828300491130813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260263789885533660753875 7890395684828300491130813)
                    ·
                      refine ⟨2958898381810612684174055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890395684828300491130813 2958898381810612684174055)
                      ·
                        rfl

theorem cell23_5762434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_5762434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762434 prefixEnd_5762434 := by exact prefixLift 5762434
  have htrace : WordTrace (prefixWord ++ tailWord_5762434) baseStart_5762434 baseEnd_5762434 := by
    simpa [prefixWord, tailWord_5762434, baseEnd_5762434] using wordTrace_append hprefix tailTrace_5762434
  have hstable : (prefixWord ++ tailWord_5762434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762434).length < 2 ^ (prefixWord ++ tailWord_5762434).sum := by decide
  have hdescent : baseEnd_5762434 < baseStart_5762434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762450 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_5762450 : Nat := 118140960795 + 5762450 * 2 ^ 59
def prefixEnd_5762450 : Nat := 4983230072969 + 3 ^ 40 * 5762450 * 2
def baseEnd_5762450 : Nat := 986302199167028207191327

theorem tailTrace_5762450 : CollatzResearch.WordTrace tailWord_5762450 prefixEnd_5762450 986302199167028207191327 := by
  unfold tailWord_5762450
  simp only [CollatzResearch.WordTrace]
  refine ⟨52543454493408818238269201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140115878649090181968717869 52543454493408818238269201)
  ·
    refine ⟨39407590870056613678701901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52543454493408818238269201 39407590870056613678701901)
    ·
      refine ⟨14777846576271230129513213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39407590870056613678701901 14777846576271230129513213)
      ·
        refine ⟨5541692466101711298567455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14777846576271230129513213 5541692466101711298567455)
        ·
          refine ⟨8312538699152566947851183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5541692466101711298567455 8312538699152566947851183)
          ·
            refine ⟨12468808048728850421776775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8312538699152566947851183 12468808048728850421776775)
            ·
              refine ⟨18703212073093275632665163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12468808048728850421776775 18703212073093275632665163)
              ·
                refine ⟨28054818109639913448997745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18703212073093275632665163 28054818109639913448997745)
                ·
                  refine ⟨21041113582229935086748309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28054818109639913448997745 21041113582229935086748309)
                  ·
                    refine ⟨986302199167028207191327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21041113582229935086748309 986302199167028207191327)
                    ·
                      rfl

theorem cell23_5762450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_5762450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762450 prefixEnd_5762450 := by exact prefixLift 5762450
  have htrace : WordTrace (prefixWord ++ tailWord_5762450) baseStart_5762450 baseEnd_5762450 := by
    simpa [prefixWord, tailWord_5762450, baseEnd_5762450] using wordTrace_append hprefix tailTrace_5762450
  have hstable : (prefixWord ++ tailWord_5762450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762450).length < 2 ^ (prefixWord ++ tailWord_5762450).sum := by decide
  have hdescent : baseEnd_5762450 < baseStart_5762450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762536 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 10]
def baseStart_5762536 : Nat := 118140960795 + 5762536 * 2 ^ 59
def prefixEnd_5762536 : Nat := 4983230072969 + 3 ^ 40 * 5762536 * 2
def baseEnd_5762536 : Nat := 328772306315263476122065

theorem tailTrace_5762536 : CollatzResearch.WordTrace tailWord_5762536 prefixEnd_5762536 328772306315263476122065 := by
  unfold tailWord_5762536
  simp only [CollatzResearch.WordTrace]
  refine ⟨105088477325661854820353731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140117969767549139760471641 105088477325661854820353731)
  ·
    refine ⟨157632715988492782230530597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105088477325661854820353731 157632715988492782230530597)
    ·
      refine ⟨29556134247842396668224487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157632715988492782230530597 29556134247842396668224487)
      ·
        refine ⟨44334201371763595002336731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29556134247842396668224487 44334201371763595002336731)
        ·
          refine ⟨66501302057645392503505097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44334201371763595002336731 66501302057645392503505097)
          ·
            refine ⟨49875976543234044377628823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66501302057645392503505097 49875976543234044377628823)
            ·
              refine ⟨74813964814851066566443235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49875976543234044377628823 74813964814851066566443235)
              ·
                refine ⟨112220947222276599849664853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74813964814851066566443235 112220947222276599849664853)
                ·
                  refine ⟨328772306315263476122065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112220947222276599849664853 328772306315263476122065)
                  ·
                    rfl

theorem cell23_5762536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_5762536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762536 prefixEnd_5762536 := by exact prefixLift 5762536
  have htrace : WordTrace (prefixWord ++ tailWord_5762536) baseStart_5762536 baseEnd_5762536 := by
    simpa [prefixWord, tailWord_5762536, baseEnd_5762536] using wordTrace_append hprefix tailTrace_5762536
  have hstable : (prefixWord ++ tailWord_5762536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762536).length < 2 ^ (prefixWord ++ tailWord_5762536).sum := by decide
  have hdescent : baseEnd_5762536 < baseStart_5762536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762540 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_5762540 : Nat := 118140960795 + 5762540 * 2 ^ 59
def prefixEnd_5762540 : Nat := 4983230072969 + 3 ^ 40 * 5762540 * 2
def baseEnd_5762540 : Nat := 986317603586663089816189

theorem tailTrace_5762540 : CollatzResearch.WordTrace tailWord_5762540 prefixEnd_5762540 986317603586663089816189 := by
  unfold tailWord_5762540
  simp only [CollatzResearch.WordTrace]
  refine ⟨105088550271654609161926537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140118067028872812215902049 105088550271654609161926537)
  ·
    refine ⟨78816412703740956871444903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105088550271654609161926537 78816412703740956871444903)
    ·
      refine ⟨118224619055611435307167355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78816412703740956871444903 118224619055611435307167355)
      ·
        refine ⟨177336928583417152960751033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118224619055611435307167355 177336928583417152960751033)
        ·
          refine ⟨133002696437562864720563275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177336928583417152960751033 133002696437562864720563275)
          ·
            refine ⟨199504044656344297080844913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133002696437562864720563275 199504044656344297080844913)
            ·
              refine ⟨149628033492258222810633685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199504044656344297080844913 149628033492258222810633685)
              ·
                refine ⟨3506907034974802097124227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149628033492258222810633685 3506907034974802097124227)
                ·
                  refine ⟨5260360552462203145686341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506907034974802097124227 5260360552462203145686341)
                  ·
                    refine ⟨986317603586663089816189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260360552462203145686341 986317603586663089816189)
                    ·
                      rfl

theorem cell23_5762540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_5762540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762540 prefixEnd_5762540 := by exact prefixLift 5762540
  have htrace : WordTrace (prefixWord ++ tailWord_5762540) baseStart_5762540 baseEnd_5762540 := by
    simpa [prefixWord, tailWord_5762540, baseEnd_5762540] using wordTrace_append hprefix tailTrace_5762540
  have hstable : (prefixWord ++ tailWord_5762540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762540).length < 2 ^ (prefixWord ++ tailWord_5762540).sum := by decide
  have hdescent : baseEnd_5762540 < baseStart_5762540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762550 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5762550 : Nat := 118140960795 + 5762550 * 2 ^ 59
def prefixEnd_5762550 : Nat := 4983230072969 + 3 ^ 40 * 5762550 * 2
def baseEnd_5762550 : Nat := 2958957945566534230323521

theorem tailTrace_5762550 : CollatzResearch.WordTrace tailWord_5762550 prefixEnd_5762550 2958957945566534230323521 := by
  unfold tailWord_5762550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136091579579561876982319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140118310182181993354478069 13136091579579561876982319)
  ·
    refine ⟨19704137369369342815473479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13136091579579561876982319 19704137369369342815473479)
    ·
      refine ⟨29556206054054014223210219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19704137369369342815473479 29556206054054014223210219)
      ·
        refine ⟨44334309081081021334815329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29556206054054014223210219 44334309081081021334815329)
        ·
          refine ⟨33250731810810766001111497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44334309081081021334815329 33250731810810766001111497)
          ·
            refine ⟨24938048858108074500833623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33250731810810766001111497 24938048858108074500833623)
            ·
              refine ⟨37407073287162111751250435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24938048858108074500833623 37407073287162111751250435)
              ·
                refine ⟨56110609930743167626875653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37407073287162111751250435 56110609930743167626875653)
                ·
                  refine ⟨10520739362014343930039185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56110609930743167626875653 10520739362014343930039185)
                  ·
                    refine ⟨7890554521510757947529389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10520739362014343930039185 7890554521510757947529389)
                    ·
                      refine ⟨2958957945566534230323521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890554521510757947529389 2958957945566534230323521)
                      ·
                        rfl

theorem cell23_5762550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5762550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762550 prefixEnd_5762550 := by exact prefixLift 5762550
  have htrace : WordTrace (prefixWord ++ tailWord_5762550) baseStart_5762550 baseEnd_5762550 := by
    simpa [prefixWord, tailWord_5762550, baseEnd_5762550] using wordTrace_append hprefix tailTrace_5762550
  have hstable : (prefixWord ++ tailWord_5762550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762550).length < 2 ^ (prefixWord ++ tailWord_5762550).sum := by decide
  have hdescent : baseEnd_5762550 < baseStart_5762550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762556 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_5762556 : Nat := 118140960795 + 5762556 * 2 ^ 59
def prefixEnd_5762556 : Nat := 4983230072969 + 3 ^ 40 * 5762556 * 2
def baseEnd_5762556 : Nat := 2958961026450461206848493

theorem tailTrace_5762556 : CollatzResearch.WordTrace tailWord_5762556 prefixEnd_5762556 2958961026450461206848493 := by
  unfold tailWord_5762556
  simp only [CollatzResearch.WordTrace]
  refine ⟨105088842055625626528217761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140118456074167502037623681 105088842055625626528217761)
  ·
    refine ⟨78816631541719219896163321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105088842055625626528217761 78816631541719219896163321)
    ·
      refine ⟨59112473656289414922122491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78816631541719219896163321 59112473656289414922122491)
      ·
        refine ⟨88668710484434122383183737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59112473656289414922122491 88668710484434122383183737)
        ·
          refine ⟨66501532863325591787387803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88668710484434122383183737 66501532863325591787387803)
          ·
            refine ⟨99752299294988387681081705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66501532863325591787387803 99752299294988387681081705)
            ·
              refine ⟨74814224471241290760811279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99752299294988387681081705 74814224471241290760811279)
              ·
                refine ⟨112221336706861936141216919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74814224471241290760811279 112221336706861936141216919)
                ·
                  refine ⟨168332005060292904211825379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112221336706861936141216919 168332005060292904211825379)
                  ·
                    refine ⟨252498007590439356317738069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168332005060292904211825379 252498007590439356317738069)
                    ·
                      refine ⟨2958961026450461206848493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 252498007590439356317738069 2958961026450461206848493)
                      ·
                        rfl

theorem cell23_5762556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_5762556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762556 prefixEnd_5762556 := by exact prefixLift 5762556
  have htrace : WordTrace (prefixWord ++ tailWord_5762556) baseStart_5762556 baseEnd_5762556 := by
    simpa [prefixWord, tailWord_5762556, baseEnd_5762556] using wordTrace_append hprefix tailTrace_5762556
  have hstable : (prefixWord ++ tailWord_5762556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762556).length < 2 ^ (prefixWord ++ tailWord_5762556).sum := by decide
  have hdescent : baseEnd_5762556 < baseStart_5762556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762570 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_5762570 : Nat := 118140960795 + 5762570 * 2 ^ 59
def prefixEnd_5762570 : Nat := 4983230072969 + 3 ^ 40 * 5762570 * 2
def baseEnd_5762570 : Nat := 328774246131069350230381

theorem tailTrace_5762570 : CollatzResearch.WordTrace tailWord_5762570 prefixEnd_5762570 328774246131069350230381 := by
  unfold tailWord_5762570
  simp only [CollatzResearch.WordTrace]
  refine ⟨52544548683300133361861291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140118796488800355631630109 52544548683300133361861291)
  ·
    refine ⟨78816823024950200042791937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52544548683300133361861291 78816823024950200042791937)
    ·
      refine ⟨59112617268712650032093953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78816823024950200042791937 59112617268712650032093953)
      ·
        refine ⟨44334462951534487524070465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59112617268712650032093953 44334462951534487524070465)
        ·
          refine ⟨33250847213650865643052849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44334462951534487524070465 33250847213650865643052849)
          ·
            refine ⟨24938135410238149232289637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33250847213650865643052849 24938135410238149232289637)
            ·
              refine ⟨4675900389419652981054307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24938135410238149232289637 4675900389419652981054307)
              ·
                refine ⟨7013850584129479471581461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675900389419652981054307 7013850584129479471581461)
                ·
                  refine ⟨328774246131069350230381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7013850584129479471581461 328774246131069350230381)
                  ·
                    rfl

theorem cell23_5762570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_5762570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762570 prefixEnd_5762570 := by exact prefixLift 5762570
  have htrace : WordTrace (prefixWord ++ tailWord_5762570) baseStart_5762570 baseEnd_5762570 := by
    simpa [prefixWord, tailWord_5762570, baseEnd_5762570] using wordTrace_append hprefix tailTrace_5762570
  have hstable : (prefixWord ++ tailWord_5762570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762570).length < 2 ^ (prefixWord ++ tailWord_5762570).sum := by decide
  have hdescent : baseEnd_5762570 < baseStart_5762570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_5762597 : Nat := 118140960795 + 5762597 * 2 ^ 59
def prefixEnd_5762597 : Nat := 4983230072969 + 3 ^ 40 * 5762597 * 2
def baseEnd_5762597 : Nat := 2958982079157295546435805

theorem tailTrace_5762597 : CollatzResearch.WordTrace tailWord_5762597 prefixEnd_5762597 2958982079157295546435805 := by
  unfold tailWord_5762597
  simp only [CollatzResearch.WordTrace]
  refine ⟨210179179504102717058678045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140119453002735144705785363 210179179504102717058678045)
  ·
    refine ⟨78817192314038518897004267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210179179504102717058678045 78817192314038518897004267)
    ·
      refine ⟨118225788471057778345506401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78817192314038518897004267 118225788471057778345506401)
      ·
        refine ⟨88669341353293333759129801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118225788471057778345506401 88669341353293333759129801)
        ·
          refine ⟨66502006014970000319347351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88669341353293333759129801 66502006014970000319347351)
          ·
            refine ⟨99753009022455000479021027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66502006014970000319347351 99753009022455000479021027)
            ·
              refine ⟨149629513533682500718531541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99753009022455000479021027 149629513533682500718531541)
              ·
                refine ⟨3506941723445683610590583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149629513533682500718531541 3506941723445683610590583)
                ·
                  refine ⟨5260412585168525415885875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506941723445683610590583 5260412585168525415885875)
                  ·
                    refine ⟨7890618877752788123828813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260412585168525415885875 7890618877752788123828813)
                    ·
                      refine ⟨2958982079157295546435805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890618877752788123828813 2958982079157295546435805)
                      ·
                        rfl

theorem cell23_5762597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_5762597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762597 prefixEnd_5762597 := by exact prefixLift 5762597
  have htrace : WordTrace (prefixWord ++ tailWord_5762597) baseStart_5762597 baseEnd_5762597 := by
    simpa [prefixWord, tailWord_5762597, baseEnd_5762597] using wordTrace_append hprefix tailTrace_5762597
  have hstable : (prefixWord ++ tailWord_5762597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762597).length < 2 ^ (prefixWord ++ tailWord_5762597).sum := by decide
  have hdescent : baseEnd_5762597 < baseStart_5762597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762640 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_5762640 : Nat := 118140960795 + 5762640 * 2 ^ 59
def prefixEnd_5762640 : Nat := 4983230072969 + 3 ^ 40 * 5762640 * 2
def baseEnd_5762640 : Nat := 2959004158825438878198107

theorem tailTrace_5762640 : CollatzResearch.WordTrace tailWord_5762640 prefixEnd_5762640 2959004158825438878198107 := by
  unfold tailWord_5762640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105090373921473467701246687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140120498561964623601662249 105090373921473467701246687)
  ·
    refine ⟨157635560882210201551870031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105090373921473467701246687 157635560882210201551870031)
    ·
      refine ⟨236453341323315302327805047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157635560882210201551870031 236453341323315302327805047)
      ·
        refine ⟨354680011984972953491707571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236453341323315302327805047 354680011984972953491707571)
        ·
          refine ⟨532020017977459430237561357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354680011984972953491707571 532020017977459430237561357)
          ·
            refine ⟨199507506741547286339085509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 532020017977459430237561357 199507506741547286339085509)
            ·
              refine ⟨37407657514040116188578533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199507506741547286339085509 37407657514040116188578533)
              ·
                refine ⟨7013935783882521785358475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37407657514040116188578533 7013935783882521785358475)
                ·
                  refine ⟨10520903675823782678037713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7013935783882521785358475 10520903675823782678037713)
                  ·
                    refine ⟨7890677756867837008528285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10520903675823782678037713 7890677756867837008528285)
                    ·
                      refine ⟨2959004158825438878198107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7890677756867837008528285 2959004158825438878198107)
                      ·
                        rfl

theorem cell23_5762640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_5762640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762640 prefixEnd_5762640 := by exact prefixLift 5762640
  have htrace : WordTrace (prefixWord ++ tailWord_5762640) baseStart_5762640 baseEnd_5762640 := by
    simpa [prefixWord, tailWord_5762640, baseEnd_5762640] using wordTrace_append hprefix tailTrace_5762640
  have hstable : (prefixWord ++ tailWord_5762640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762640).length < 2 ^ (prefixWord ++ tailWord_5762640).sum := by decide
  have hdescent : baseEnd_5762640 < baseStart_5762640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762664 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_5762664 : Nat := 118140960795 + 5762664 * 2 ^ 59
def prefixEnd_5762664 : Nat := 4983230072969 + 3 ^ 40 * 5762664 * 2
def baseEnd_5762664 : Nat := 986338827453715594765999

theorem tailTrace_5762664 : CollatzResearch.WordTrace tailWord_5762664 prefixEnd_5762664 986338827453715594765999 := by
  unfold tailWord_5762664
  simp only [CollatzResearch.WordTrace]
  refine ⟨105090811597429993750683523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140121082129906658334244697 105090811597429993750683523)
  ·
    refine ⟨157636217396144990626025285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105090811597429993750683523 157636217396144990626025285)
    ·
      refine ⟨29556790761777185742379741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157636217396144990626025285 29556790761777185742379741)
      ·
        refine ⟨11083796535666444653392403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29556790761777185742379741 11083796535666444653392403)
        ·
          refine ⟨16625694803499666980088605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11083796535666444653392403 16625694803499666980088605)
          ·
            refine ⟨6234635551312375117533227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16625694803499666980088605 6234635551312375117533227)
            ·
              refine ⟨9351953326968562676299841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234635551312375117533227 9351953326968562676299841)
              ·
                refine ⟨7013964995226422007224881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9351953326968562676299841 7013964995226422007224881)
                ·
                  refine ⟨5260473746419816505418661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013964995226422007224881 5260473746419816505418661)
                  ·
                    refine ⟨986338827453715594765999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260473746419816505418661 986338827453715594765999)
                    ·
                      rfl

theorem cell23_5762664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_5762664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762664 prefixEnd_5762664 := by exact prefixLift 5762664
  have htrace : WordTrace (prefixWord ++ tailWord_5762664) baseStart_5762664 baseEnd_5762664 := by
    simpa [prefixWord, tailWord_5762664, baseEnd_5762664] using wordTrace_append hprefix tailTrace_5762664
  have hstable : (prefixWord ++ tailWord_5762664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762664).length < 2 ^ (prefixWord ++ tailWord_5762664).sum := by decide
  have hdescent : baseEnd_5762664 < baseStart_5762664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762697 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 1, 3, 2]
def baseStart_5762697 : Nat := 118140960795 + 5762697 * 2 ^ 59
def prefixEnd_5762697 : Nat := 4983230072969 + 3 ^ 40 * 5762697 * 2
def baseEnd_5762697 : Nat := 2959033427222745155185345

theorem tailTrace_5762697 : CollatzResearch.WordTrace tailWord_5762697 prefixEnd_5762697 2959033427222745155185345 := by
  unfold tailWord_5762697
  simp only [CollatzResearch.WordTrace]
  refine ⟨210182826803740434137318345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140121884535826956091545563 210182826803740434137318345)
  ·
    refine ⟨157637120102805325602988759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210182826803740434137318345 157637120102805325602988759)
    ·
      refine ⟨236455680154207988404483139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157637120102805325602988759 236455680154207988404483139)
      ·
        refine ⟨354683520231311982606724709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236455680154207988404483139 354683520231311982606724709)
        ·
          refine ⟨66503160043370996738760883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354683520231311982606724709 66503160043370996738760883)
          ·
            refine ⟨99754740065056495108141325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66503160043370996738760883 99754740065056495108141325)
            ·
              refine ⟨37408027524396185665552997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99754740065056495108141325 37408027524396185665552997)
              ·
                refine ⟨7014005160824284812291187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37408027524396185665552997 7014005160824284812291187)
                ·
                  refine ⟨10521007741236427218436781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014005160824284812291187 10521007741236427218436781)
                  ·
                    refine ⟨3945377902963660206913793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10521007741236427218436781 3945377902963660206913793)
                    ·
                      refine ⟨2959033427222745155185345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945377902963660206913793 2959033427222745155185345)
                      ·
                        rfl

theorem cell23_5762697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 3, 2].length) (baseStart_5762697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762697 prefixEnd_5762697 := by exact prefixLift 5762697
  have htrace : WordTrace (prefixWord ++ tailWord_5762697) baseStart_5762697 baseEnd_5762697 := by
    simpa [prefixWord, tailWord_5762697, baseEnd_5762697] using wordTrace_append hprefix tailTrace_5762697
  have hstable : (prefixWord ++ tailWord_5762697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762697).length < 2 ^ (prefixWord ++ tailWord_5762697).sum := by decide
  have hdescent : baseEnd_5762697 < baseStart_5762697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762763 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 7]
def baseStart_5762763 : Nat := 118140960795 + 5762763 * 2 ^ 59
def prefixEnd_5762763 : Nat := 4983230072969 + 3 ^ 40 * 5762763 * 2
def baseEnd_5762763 : Nat := 986355772315313965653347

theorem tailTrace_5762763 : CollatzResearch.WordTrace tailWord_5762763 prefixEnd_5762763 986355772315313965653347 := by
  unfold tailWord_5762763
  simp only [CollatzResearch.WordTrace]
  refine ⟨210185234021501327409220943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140123489347667551606147295 210185234021501327409220943)
  ·
    refine ⟨315277851032251991113831415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210185234021501327409220943 315277851032251991113831415)
    ·
      refine ⟨472916776548377986670747123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315277851032251991113831415 472916776548377986670747123)
      ·
        refine ⟨709375164822566980006120685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472916776548377986670747123 709375164822566980006120685)
        ·
          refine ⟨266015686808462617502295257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709375164822566980006120685 266015686808462617502295257)
          ·
            refine ⟨199511765106346963126721443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266015686808462617502295257 199511765106346963126721443)
            ·
              refine ⟨299267647659520444690082165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199511765106346963126721443 299267647659520444690082165)
              ·
                refine ⟨28056341968080041689695203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299267647659520444690082165 28056341968080041689695203)
                ·
                  refine ⟨42084512952120062534542805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28056341968080041689695203 42084512952120062534542805)
                  ·
                    refine ⟨986355772315313965653347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42084512952120062534542805 986355772315313965653347)
                    ·
                      rfl

theorem cell23_5762763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_5762763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762763 prefixEnd_5762763 := by exact prefixLift 5762763
  have htrace : WordTrace (prefixWord ++ tailWord_5762763) baseStart_5762763 baseEnd_5762763 := by
    simpa [prefixWord, tailWord_5762763, baseEnd_5762763] using wordTrace_append hprefix tailTrace_5762763
  have hstable : (prefixWord ++ tailWord_5762763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762763).length < 2 ^ (prefixWord ++ tailWord_5762763).sum := by decide
  have hdescent : baseEnd_5762763 < baseStart_5762763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762793 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_5762793 : Nat := 118140960795 + 5762793 * 2 ^ 59
def prefixEnd_5762793 : Nat := 4983230072969 + 3 ^ 40 * 5762793 * 2
def baseEnd_5762793 : Nat := 986360907121858926528301

theorem tailTrace_5762793 : CollatzResearch.WordTrace tailWord_5762793 prefixEnd_5762793 986360907121858926528301 := by
  unfold tailWord_5762793
  simp only [CollatzResearch.WordTrace]
  refine ⟨210186328211392642532813033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140124218807595095021875355 210186328211392642532813033)
  ·
    refine ⟨157639746158544481899609775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210186328211392642532813033 157639746158544481899609775)
    ·
      refine ⟨236459619237816722849414663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157639746158544481899609775 236459619237816722849414663)
      ·
        refine ⟨354689428856725084274121995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236459619237816722849414663 354689428856725084274121995)
        ·
          refine ⟨532034143285087626411182993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354689428856725084274121995 532034143285087626411182993)
          ·
            refine ⟨399025607463815719808387245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532034143285087626411182993 399025607463815719808387245)
            ·
              refine ⟨149634602798930894928145217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399025607463815719808387245 149634602798930894928145217)
              ·
                refine ⟨112225952099198171196108913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149634602798930894928145217 112225952099198171196108913)
                ·
                  refine ⟨84169464074398628397081685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112225952099198171196108913 84169464074398628397081685)
                  ·
                    refine ⟨986360907121858926528301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84169464074398628397081685 986360907121858926528301)
                    ·
                      rfl

theorem cell23_5762793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_5762793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762793 prefixEnd_5762793 := by exact prefixLift 5762793
  have htrace : WordTrace (prefixWord ++ tailWord_5762793) baseStart_5762793 baseEnd_5762793 := by
    simpa [prefixWord, tailWord_5762793, baseEnd_5762793] using wordTrace_append hprefix tailTrace_5762793
  have hstable : (prefixWord ++ tailWord_5762793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762793).length < 2 ^ (prefixWord ++ tailWord_5762793).sum := by decide
  have hdescent : baseEnd_5762793 < baseStart_5762793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762817 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_5762817 : Nat := 118140960795 + 5762817 * 2 ^ 59
def prefixEnd_5762817 : Nat := 4983230072969 + 3 ^ 40 * 5762817 * 2
def baseEnd_5762817 : Nat := 2959095044901284685684793

theorem tailTrace_5762817 : CollatzResearch.WordTrace tailWord_5762817 prefixEnd_5762817 2959095044901284685684793 := by
  unfold tailWord_5762817
  simp only [CollatzResearch.WordTrace]
  refine ⟨210187203563305694631686705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140124802375537129754457803 210187203563305694631686705)
  ·
    refine ⟨157640402672479270973765029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210187203563305694631686705 157640402672479270973765029)
    ·
      refine ⟨29557575501089863307580943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157640402672479270973765029 29557575501089863307580943)
      ·
        refine ⟨44336363251634794961371415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29557575501089863307580943 44336363251634794961371415)
        ·
          refine ⟨66504544877452192442057123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44336363251634794961371415 66504544877452192442057123)
          ·
            refine ⟨99756817316178288663085685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66504544877452192442057123 99756817316178288663085685)
            ·
              refine ⟨9352201623391714562164283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99756817316178288663085685 9352201623391714562164283)
              ·
                refine ⟨14028302435087571843246425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9352201623391714562164283 14028302435087571843246425)
                ·
                  refine ⟨10521226826315678882434819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14028302435087571843246425 10521226826315678882434819)
                  ·
                    refine ⟨15781840239473518323652229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10521226826315678882434819 15781840239473518323652229)
                    ·
                      refine ⟨2959095044901284685684793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15781840239473518323652229 2959095044901284685684793)
                      ·
                        rfl

theorem cell23_5762817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_5762817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762817 prefixEnd_5762817 := by exact prefixLift 5762817
  have htrace : WordTrace (prefixWord ++ tailWord_5762817) baseStart_5762817 baseEnd_5762817 := by
    simpa [prefixWord, tailWord_5762817, baseEnd_5762817] using wordTrace_append hprefix tailTrace_5762817
  have hstable : (prefixWord ++ tailWord_5762817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762817).length < 2 ^ (prefixWord ++ tailWord_5762817).sum := by decide
  have hdescent : baseEnd_5762817 < baseStart_5762817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762829 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5762829 : Nat := 118140960795 + 5762829 * 2 ^ 59
def prefixEnd_5762829 : Nat := 4983230072969 + 3 ^ 40 * 5762829 * 2
def baseEnd_5762829 : Nat := 2959101206669138638734739

theorem tailTrace_5762829 : CollatzResearch.WordTrace tailWord_5762829 prefixEnd_5762829 2959101206669138638734739 := by
  unfold tailWord_5762829
  simp only [CollatzResearch.WordTrace]
  refine ⟨210187641239262220681123541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140125094159508147120749027 210187641239262220681123541)
  ·
    refine ⟨4926272841545208297213833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 210187641239262220681123541 4926272841545208297213833)
    ·
      refine ⟨3694704631158906222910375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4926272841545208297213833 3694704631158906222910375)
      ·
        refine ⟨5542056946738359334365563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694704631158906222910375 5542056946738359334365563)
        ·
          refine ⟨8313085420107539001548345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542056946738359334365563 8313085420107539001548345)
          ·
            refine ⟨6234814065080654251161259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8313085420107539001548345 6234814065080654251161259)
            ·
              refine ⟨9352221097620981376741889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234814065080654251161259 9352221097620981376741889)
              ·
                refine ⟨7014165823215736032556417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352221097620981376741889 7014165823215736032556417)
                ·
                  refine ⟨5260624367411802024417313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014165823215736032556417 5260624367411802024417313)
                  ·
                    refine ⟨3945468275558851518312985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260624367411802024417313 3945468275558851518312985)
                    ·
                      refine ⟨2959101206669138638734739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945468275558851518312985 2959101206669138638734739)
                      ·
                        rfl

theorem cell23_5762829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5762829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762829 prefixEnd_5762829 := by exact prefixLift 5762829
  have htrace : WordTrace (prefixWord ++ tailWord_5762829) baseStart_5762829 baseEnd_5762829 := by
    simpa [prefixWord, tailWord_5762829, baseEnd_5762829] using wordTrace_append hprefix tailTrace_5762829
  have hstable : (prefixWord ++ tailWord_5762829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762829).length < 2 ^ (prefixWord ++ tailWord_5762829).sum := by decide
  have hdescent : baseEnd_5762829 < baseStart_5762829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762830 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5762830 : Nat := 118140960795 + 5762830 * 2 ^ 59
def prefixEnd_5762830 : Nat := 4983230072969 + 3 ^ 40 * 5762830 * 2
def baseEnd_5762830 : Nat := 2959101720149793134822233

theorem tailTrace_5762830 : CollatzResearch.WordTrace tailWord_5762830 prefixEnd_5762830 2959101720149793134822233 := by
  unfold tailWord_5762830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273459714032324731488743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140125118474839065234606629 26273459714032324731488743)
  ·
    refine ⟨39410189571048487097233115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26273459714032324731488743 39410189571048487097233115)
    ·
      refine ⟨59115284356572730645849673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39410189571048487097233115 59115284356572730645849673)
      ·
        refine ⟨44336463267429547984387255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59115284356572730645849673 44336463267429547984387255)
        ·
          refine ⟨66504694901144321976580883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44336463267429547984387255 66504694901144321976580883)
          ·
            refine ⟨99757042351716482964871325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66504694901144321976580883 99757042351716482964871325)
            ·
              refine ⟨37408890881893681111826747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99757042351716482964871325 37408890881893681111826747)
              ·
                refine ⟨56113336322840521667740121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37408890881893681111826747 56113336322840521667740121)
                ·
                  refine ⟨42085002242130391250805091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56113336322840521667740121 42085002242130391250805091)
                  ·
                    refine ⟨63127503363195586876207637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42085002242130391250805091 63127503363195586876207637)
                    ·
                      refine ⟨2959101720149793134822233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63127503363195586876207637 2959101720149793134822233)
                      ·
                        rfl

theorem cell23_5762830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5762830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762830 prefixEnd_5762830 := by exact prefixLift 5762830
  have htrace : WordTrace (prefixWord ++ tailWord_5762830) baseStart_5762830 baseEnd_5762830 := by
    simpa [prefixWord, tailWord_5762830, baseEnd_5762830] using wordTrace_append hprefix tailTrace_5762830
  have hstable : (prefixWord ++ tailWord_5762830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762830).length < 2 ^ (prefixWord ++ tailWord_5762830).sum := by decide
  have hdescent : baseEnd_5762830 < baseStart_5762830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762844 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_5762844 : Nat := 118140960795 + 5762844 * 2 ^ 59
def prefixEnd_5762844 : Nat := 4983230072969 + 3 ^ 40 * 5762844 * 2
def baseEnd_5762844 : Nat := 986369636292985360015723

theorem tailTrace_5762844 : CollatzResearch.WordTrace tailWord_5762844 prefixEnd_5762844 986369636292985360015723 := by
  unfold tailWord_5762844
  simp only [CollatzResearch.WordTrace]
  refine ⟨105094094167103939121459793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140125458889471918828613057 105094094167103939121459793)
  ·
    refine ⟨78820570625327954341094845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105094094167103939121459793 78820570625327954341094845)
    ·
      refine ⟨29557713984497982877910567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78820570625327954341094845 29557713984497982877910567)
      ·
        refine ⟨44336570976746974316865851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29557713984497982877910567 44336570976746974316865851)
        ·
          refine ⟨66504856465120461475298777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44336570976746974316865851 66504856465120461475298777)
          ·
            refine ⟨49878642348840346106474083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66504856465120461475298777 49878642348840346106474083)
            ·
              refine ⟨74817963523260519159711125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49878642348840346106474083 74817963523260519159711125)
              ·
                refine ⟨3507092040152836835611459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74817963523260519159711125 3507092040152836835611459)
                ·
                  refine ⟨5260638060229255253417189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507092040152836835611459 5260638060229255253417189)
                  ·
                    refine ⟨986369636292985360015723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260638060229255253417189 986369636292985360015723)
                    ·
                      rfl

theorem cell23_5762844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_5762844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762844 prefixEnd_5762844 := by exact prefixLift 5762844
  have htrace : WordTrace (prefixWord ++ tailWord_5762844) baseStart_5762844 baseEnd_5762844 := by
    simpa [prefixWord, tailWord_5762844, baseEnd_5762844] using wordTrace_append hprefix tailTrace_5762844
  have hstable : (prefixWord ++ tailWord_5762844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762844).length < 2 ^ (prefixWord ++ tailWord_5762844).sum := by decide
  have hdescent : baseEnd_5762844 < baseStart_5762844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762878 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_5762878 : Nat := 118140960795 + 5762878 * 2 ^ 59
def prefixEnd_5762878 : Nat := 4983230072969 + 3 ^ 40 * 5762878 * 2
def baseEnd_5762878 : Nat := 986375455740402982340671

theorem tailTrace_5762878 : CollatzResearch.WordTrace tailWord_5762878 prefixEnd_5762878 986375455740402982340671 := by
  unfold tailWord_5762878
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273678552010587756207161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140126285610723134699771525 26273678552010587756207161)
  ·
    refine ⟨19705258914007940817155371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26273678552010587756207161 19705258914007940817155371)
    ·
      refine ⟨29557888371011911225733057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19705258914007940817155371 29557888371011911225733057)
      ·
        refine ⟨22168416278258933419299793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29557888371011911225733057 22168416278258933419299793)
        ·
          refine ⟨16626312208694200064474845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22168416278258933419299793 16626312208694200064474845)
          ·
            refine ⟨6234867078260325024178067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16626312208694200064474845 6234867078260325024178067)
            ·
              refine ⟨9352300617390487536267101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234867078260325024178067 9352300617390487536267101)
              ·
                refine ⟨3507112731521432826100163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9352300617390487536267101 3507112731521432826100163)
                ·
                  refine ⟨5260669097282149239150245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507112731521432826100163 5260669097282149239150245)
                  ·
                    refine ⟨986375455740402982340671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260669097282149239150245 986375455740402982340671)
                    ·
                      rfl

theorem cell23_5762878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_5762878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762878 prefixEnd_5762878 := by exact prefixLift 5762878
  have htrace : WordTrace (prefixWord ++ tailWord_5762878) baseStart_5762878 baseEnd_5762878 := by
    simpa [prefixWord, tailWord_5762878, baseEnd_5762878] using wordTrace_append hprefix tailTrace_5762878
  have hstable : (prefixWord ++ tailWord_5762878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762878).length < 2 ^ (prefixWord ++ tailWord_5762878).sum := by decide
  have hdescent : baseEnd_5762878 < baseStart_5762878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762887 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 1, 5]
def baseStart_5762887 : Nat := 118140960795 + 5762887 * 2 ^ 59
def prefixEnd_5762887 : Nat := 4983230072969 + 3 ^ 40 * 5762887 * 2
def baseEnd_5762887 : Nat := 986376996182366470603157

theorem tailTrace_5762887 : CollatzResearch.WordTrace tailWord_5762887 prefixEnd_5762887 986376996182366470603157 := by
  unfold tailWord_5762887
  simp only [CollatzResearch.WordTrace]
  refine ⟨210189756673052096586734915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140126504448701397724489943 210189756673052096586734915)
  ·
    refine ⟨315284635009578144880102373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210189756673052096586734915 315284635009578144880102373)
    ·
      refine ⟨59115869064295902165019195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315284635009578144880102373 59115869064295902165019195)
      ·
        refine ⟨88673803596443853247528793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59115869064295902165019195 88673803596443853247528793)
        ·
          refine ⟨66505352697332889935646595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88673803596443853247528793 66505352697332889935646595)
          ·
            refine ⟨99758029045999334903469893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66505352697332889935646595 99758029045999334903469893)
            ·
              refine ⟨18704630446124875294400605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99758029045999334903469893 18704630446124875294400605)
              ·
                refine ⟨7014236417296828235400227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18704630446124875294400605 7014236417296828235400227)
                ·
                  refine ⟨10521354625945242353100341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014236417296828235400227 10521354625945242353100341)
                  ·
                    refine ⟨986376996182366470603157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521354625945242353100341 986376996182366470603157)
                    ·
                      rfl

theorem cell23_5762887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_5762887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762887 prefixEnd_5762887 := by exact prefixLift 5762887
  have htrace : WordTrace (prefixWord ++ tailWord_5762887) baseStart_5762887 baseEnd_5762887 := by
    simpa [prefixWord, tailWord_5762887, baseEnd_5762887] using wordTrace_append hprefix tailTrace_5762887
  have hstable : (prefixWord ++ tailWord_5762887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762887).length < 2 ^ (prefixWord ++ tailWord_5762887).sum := by decide
  have hdescent : baseEnd_5762887 < baseStart_5762887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762901 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_5762901 : Nat := 118140960795 + 5762901 * 2 ^ 59
def prefixEnd_5762901 : Nat := 4983230072969 + 3 ^ 40 * 5762901 * 2
def baseEnd_5762901 : Nat := 2959138177276262357034407

theorem tailTrace_5762901 : CollatzResearch.WordTrace tailWord_5762901 prefixEnd_5762901 2959138177276262357034407 := by
  unfold tailWord_5762901
  simp only [CollatzResearch.WordTrace]
  refine ⟨210190267295001376977744557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140126844863334251318496371 210190267295001376977744557)
  ·
    refine ⟨78821350235625516366654209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210190267295001376977744557 78821350235625516366654209)
    ·
      refine ⟨59116012676719137274990657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78821350235625516366654209 59116012676719137274990657)
      ·
        refine ⟨44337009507539352956242993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59116012676719137274990657 44337009507539352956242993)
        ·
          refine ⟨33252757130654514717182245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44337009507539352956242993 33252757130654514717182245)
          ·
            refine ⟨6234891961997721509471671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33252757130654514717182245 6234891961997721509471671)
            ·
              refine ⟨9352337942996582264207507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234891961997721509471671 9352337942996582264207507)
              ·
                refine ⟨14028506914494873396311261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9352337942996582264207507 14028506914494873396311261)
                ·
                  refine ⟨5260690092935577523616723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14028506914494873396311261 5260690092935577523616723)
                  ·
                    refine ⟨7891035139403366285425085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260690092935577523616723 7891035139403366285425085)
                    ·
                      refine ⟨2959138177276262357034407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891035139403366285425085 2959138177276262357034407)
                      ·
                        rfl

theorem cell23_5762901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_5762901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762901 prefixEnd_5762901 := by exact prefixLift 5762901
  have htrace : WordTrace (prefixWord ++ tailWord_5762901) baseStart_5762901 baseEnd_5762901 := by
    simpa [prefixWord, tailWord_5762901, baseEnd_5762901] using wordTrace_append hprefix tailTrace_5762901
  have hstable : (prefixWord ++ tailWord_5762901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762901).length < 2 ^ (prefixWord ++ tailWord_5762901).sum := by decide
  have hdescent : baseEnd_5762901 < baseStart_5762901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762908 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 6]
def baseStart_5762908 : Nat := 118140960795 + 5762908 * 2 ^ 59
def prefixEnd_5762908 : Nat := 4983230072969 + 3 ^ 40 * 5762908 * 2
def baseEnd_5762908 : Nat := 328793530182315981071875

theorem tailTrace_5762908 : CollatzResearch.WordTrace tailWord_5762908 prefixEnd_5762908 328793530182315981071875 := by
  unfold tailWord_5762908
  simp only [CollatzResearch.WordTrace]
  refine ⟨105095261302988008586624689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140127015070650678115499585 105095261302988008586624689)
  ·
    refine ⟨78821445977241006439968517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105095261302988008586624689 78821445977241006439968517)
    ·
      refine ⟨14779021120732688707494097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78821445977241006439968517 14779021120732688707494097)
      ·
        refine ⟨11084265840549516530620573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14779021120732688707494097 11084265840549516530620573)
        ·
          refine ⟨4156599690206068698982715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11084265840549516530620573 4156599690206068698982715)
          ·
            refine ⟨6234899535309103048474073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156599690206068698982715 6234899535309103048474073)
            ·
              refine ⟨4676174651481827286355555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6234899535309103048474073 4676174651481827286355555)
              ·
                refine ⟨7014261977222740929533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676174651481827286355555 7014261977222740929533333)
                ·
                  refine ⟨328793530182315981071875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7014261977222740929533333 328793530182315981071875)
                  ·
                    rfl

theorem cell23_5762908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_5762908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762908 prefixEnd_5762908 := by exact prefixLift 5762908
  have htrace : WordTrace (prefixWord ++ tailWord_5762908) baseStart_5762908 baseEnd_5762908 := by
    simpa [prefixWord, tailWord_5762908, baseEnd_5762908] using wordTrace_append hprefix tailTrace_5762908
  have hstable : (prefixWord ++ tailWord_5762908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762908).length < 2 ^ (prefixWord ++ tailWord_5762908).sum := by decide
  have hdescent : baseEnd_5762908 < baseStart_5762908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762924 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_5762924 : Nat := 118140960795 + 5762924 * 2 ^ 59
def prefixEnd_5762924 : Nat := 4983230072969 + 3 ^ 40 * 5762924 * 2
def baseEnd_5762924 : Nat := 2959149987331315767046801

theorem tailTrace_5762924 : CollatzResearch.WordTrace tailWord_5762924 prefixEnd_5762924 2959149987331315767046801 := by
  unfold tailWord_5762924
  simp only [CollatzResearch.WordTrace]
  refine ⟨105095553086959025952915913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140127404115945367937221217 105095553086959025952915913)
  ·
    refine ⟨78821664815219269464686935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105095553086959025952915913 78821664815219269464686935)
    ·
      refine ⟨118232497222828904197030403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78821664815219269464686935 118232497222828904197030403)
      ·
        refine ⟨177348745834243356295545605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118232497222828904197030403 177348745834243356295545605)
        ·
          refine ⟨33252889843920629305414801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177348745834243356295545605 33252889843920629305414801)
          ·
            refine ⟨24939667382940471979061101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33252889843920629305414801 24939667382940471979061101)
            ·
              refine ⟨9352375268602676992147913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24939667382940471979061101 9352375268602676992147913)
              ·
                refine ⟨7014281451452007744110935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352375268602676992147913 7014281451452007744110935)
                ·
                  refine ⟨10521422177178011616166403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014281451452007744110935 10521422177178011616166403)
                  ·
                    refine ⟨15782133265767017424249605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10521422177178011616166403 15782133265767017424249605)
                    ·
                      refine ⟨2959149987331315767046801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15782133265767017424249605 2959149987331315767046801)
                      ·
                        rfl

theorem cell23_5762924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_5762924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762924 prefixEnd_5762924 := by exact prefixLift 5762924
  have htrace : WordTrace (prefixWord ++ tailWord_5762924) baseStart_5762924 baseEnd_5762924 := by
    simpa [prefixWord, tailWord_5762924, baseEnd_5762924] using wordTrace_append hprefix tailTrace_5762924
  have hstable : (prefixWord ++ tailWord_5762924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762924).length < 2 ^ (prefixWord ++ tailWord_5762924).sum := by decide
  have hdescent : baseEnd_5762924 < baseStart_5762924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762937 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5762937 : Nat := 118140960795 + 5762937 * 2 ^ 59
def prefixEnd_5762937 : Nat := 4983230072969 + 3 ^ 40 * 5762937 * 2
def baseEnd_5762937 : Nat := 2959156662579824216184241

theorem tailTrace_5762937 : CollatzResearch.WordTrace tailWord_5762937 prefixEnd_5762937 2959156662579824216184241 := by
  unfold tailWord_5762937
  simp only [CollatzResearch.WordTrace]
  refine ⟨210191580322870955126055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140127720215247303417370043 210191580322870955126055065)
  ·
    refine ⟨157643685242153216344541299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210191580322870955126055065 157643685242153216344541299)
    ·
      refine ⟨236465527863229824516811949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157643685242153216344541299 236465527863229824516811949)
      ·
        refine ⟨88674572948711184193804481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236465527863229824516811949 88674572948711184193804481)
        ·
          refine ⟨66505929711533388145353361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88674572948711184193804481 66505929711533388145353361)
          ·
            refine ⟨49879447283650041109015021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66505929711533388145353361 49879447283650041109015021)
            ·
              refine ⟨18704792731368765415880633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49879447283650041109015021 18704792731368765415880633)
              ·
                refine ⟨14028594548526574061910475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18704792731368765415880633 14028594548526574061910475)
                ·
                  refine ⟨21042891822789861092865713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14028594548526574061910475 21042891822789861092865713)
                  ·
                    refine ⟨15782168867092395819649285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21042891822789861092865713 15782168867092395819649285)
                    ·
                      refine ⟨2959156662579824216184241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15782168867092395819649285 2959156662579824216184241)
                      ·
                        rfl

theorem cell23_5762937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5762937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762937 prefixEnd_5762937 := by exact prefixLift 5762937
  have htrace : WordTrace (prefixWord ++ tailWord_5762937) baseStart_5762937 baseEnd_5762937 := by
    simpa [prefixWord, tailWord_5762937, baseEnd_5762937] using wordTrace_append hprefix tailTrace_5762937
  have hstable : (prefixWord ++ tailWord_5762937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762937).length < 2 ^ (prefixWord ++ tailWord_5762937).sum := by decide
  have hdescent : baseEnd_5762937 < baseStart_5762937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762951 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 2, 4]
def baseStart_5762951 : Nat := 118140960795 + 5762951 * 2 ^ 59
def prefixEnd_5762951 : Nat := 4983230072969 + 3 ^ 40 * 5762951 * 2
def baseEnd_5762951 : Nat := 986387950436329053803059

theorem tailTrace_5762951 : CollatzResearch.WordTrace tailWord_5762951 prefixEnd_5762951 986387950436329053803059 := by
  unfold tailWord_5762951
  simp only [CollatzResearch.WordTrace]
  refine ⟨210192090944820235517064707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140128060629880157011376471 210192090944820235517064707)
  ·
    refine ⟨315288136417230353275597061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210192090944820235517064707 315288136417230353275597061)
    ·
      refine ⟨59116525578230691239174449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315288136417230353275597061 59116525578230691239174449)
      ·
        refine ⟨44337394183673018429380837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59116525578230691239174449 44337394183673018429380837)
        ·
          refine ⟨8313261409438690955508907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44337394183673018429380837 8313261409438690955508907)
          ·
            refine ⟨12469892114158036433263361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313261409438690955508907 12469892114158036433263361)
            ·
              refine ⟨9352419085618527324947521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12469892114158036433263361 9352419085618527324947521)
              ·
                refine ⟨7014314314213895493710641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352419085618527324947521 7014314314213895493710641)
                ·
                  refine ⟨5260735735660421620282981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014314314213895493710641 5260735735660421620282981)
                  ·
                    refine ⟨986387950436329053803059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260735735660421620282981 986387950436329053803059)
                    ·
                      rfl

theorem cell23_5762951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_5762951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762951 prefixEnd_5762951 := by exact prefixLift 5762951
  have htrace : WordTrace (prefixWord ++ tailWord_5762951) baseStart_5762951 baseEnd_5762951 := by
    simpa [prefixWord, tailWord_5762951, baseEnd_5762951] using wordTrace_append hprefix tailTrace_5762951
  have hstable : (prefixWord ++ tailWord_5762951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762951).length < 2 ^ (prefixWord ++ tailWord_5762951).sum := by decide
  have hdescent : baseEnd_5762951 < baseStart_5762951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762952 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5762952 : Nat := 118140960795 + 5762952 * 2 ^ 59
def prefixEnd_5762952 : Nat := 4983230072969 + 3 ^ 40 * 5762952 * 2
def baseEnd_5762952 : Nat := 2959164364789641657496673

theorem tailTrace_5762952 : CollatzResearch.WordTrace tailWord_5762952 prefixEnd_5762952 2959164364789641657496673 := by
  unfold tailWord_5762952
  simp only [CollatzResearch.WordTrace]
  refine ⟨105096063708908306343925555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140128084945211075125234073 105096063708908306343925555)
  ·
    refine ⟨157644095563362459515888333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105096063708908306343925555 157644095563362459515888333)
    ·
      refine ⟨59116535836260922318458125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157644095563362459515888333 59116535836260922318458125)
      ·
        refine ⟨22168700938597845869421797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59116535836260922318458125 22168700938597845869421797)
        ·
          refine ⟨4156631425987096100516587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22168700938597845869421797 4156631425987096100516587)
          ·
            refine ⟨6234947138980644150774881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156631425987096100516587 6234947138980644150774881)
            ·
              refine ⟨4676210354235483113081161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6234947138980644150774881 4676210354235483113081161)
              ·
                refine ⟨3507157765676612334810871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676210354235483113081161 3507157765676612334810871)
                ·
                  refine ⟨5260736648514918502216307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507157765676612334810871 5260736648514918502216307)
                  ·
                    refine ⟨7891104972772377753324461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260736648514918502216307 7891104972772377753324461)
                    ·
                      refine ⟨2959164364789641657496673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891104972772377753324461 2959164364789641657496673)
                      ·
                        rfl

theorem cell23_5762952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5762952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762952 prefixEnd_5762952 := by exact prefixLift 5762952
  have htrace : WordTrace (prefixWord ++ tailWord_5762952) baseStart_5762952 baseEnd_5762952 := by
    simpa [prefixWord, tailWord_5762952, baseEnd_5762952] using wordTrace_append hprefix tailTrace_5762952
  have hstable : (prefixWord ++ tailWord_5762952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762952).length < 2 ^ (prefixWord ++ tailWord_5762952).sum := by decide
  have hdescent : baseEnd_5762952 < baseStart_5762952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762960 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_5762960 : Nat := 118140960795 + 5762960 * 2 ^ 59
def prefixEnd_5762960 : Nat := 4983230072969 + 3 ^ 40 * 5762960 * 2
def baseEnd_5762960 : Nat := 986389490878292542065545

theorem tailTrace_5762960 : CollatzResearch.WordTrace tailWord_5762960 prefixEnd_5762960 986389490878292542065545 := by
  unfold tailWord_5762960
  simp only [CollatzResearch.WordTrace]
  refine ⟨105096209600893815027071167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140128279467858420036094889 105096209600893815027071167)
  ·
    refine ⟨157644314401340722540606751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105096209600893815027071167 157644314401340722540606751)
    ·
      refine ⟨236466471602011083810910127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157644314401340722540606751 236466471602011083810910127)
      ·
        refine ⟨354699707403016625716365191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236466471602011083810910127 354699707403016625716365191)
        ·
          refine ⟨532049561104524938574547787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354699707403016625716365191 532049561104524938574547787)
          ·
            refine ⟨798074341656787407861821681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532049561104524938574547787 798074341656787407861821681)
            ·
              refine ⟨598555756242590555896366261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798074341656787407861821681 598555756242590555896366261)
              ·
                refine ⟨56114602147742864615284337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 598555756242590555896366261 56114602147742864615284337)
                ·
                  refine ⟨42085951610807148461463253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56114602147742864615284337 42085951610807148461463253)
                  ·
                    refine ⟨986389490878292542065545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42085951610807148461463253 986389490878292542065545)
                    ·
                      rfl

theorem cell23_5762960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_5762960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762960 prefixEnd_5762960 := by exact prefixLift 5762960
  have htrace : WordTrace (prefixWord ++ tailWord_5762960) baseStart_5762960 baseEnd_5762960 := by
    simpa [prefixWord, tailWord_5762960, baseEnd_5762960] using wordTrace_append hprefix tailTrace_5762960
  have hstable : (prefixWord ++ tailWord_5762960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762960).length < 2 ^ (prefixWord ++ tailWord_5762960).sum := by decide
  have hdescent : baseEnd_5762960 < baseStart_5762960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5762964 : List Nat := [2, 4, 2, 1, 1, 4, 1, 8]
def baseStart_5762964 : Nat := 118140960795 + 5762964 * 2 ^ 59
def prefixEnd_5762964 : Nat := 4983230072969 + 3 ^ 40 * 5762964 * 2
def baseEnd_5762964 : Nat := 109598908391018355946171

theorem tailTrace_5762964 : CollatzResearch.WordTrace tailWord_5762964 prefixEnd_5762964 109598908391018355946171 := by
  unfold tailWord_5762964
  simp only [CollatzResearch.WordTrace]
  refine ⟨105096282546886569368643973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140128376729182092491525297 105096282546886569368643973)
  ·
    refine ⟨19705552977541231756620745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105096282546886569368643973 19705552977541231756620745)
    ·
      refine ⟨14779164733155923817465559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19705552977541231756620745 14779164733155923817465559)
      ·
        refine ⟨22168747099733885726198339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14779164733155923817465559 22168747099733885726198339)
        ·
          refine ⟨33253120649600828589297509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22168747099733885726198339 33253120649600828589297509)
          ·
            refine ⟨6234960121800155360493283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33253120649600828589297509 6234960121800155360493283)
            ·
              refine ⟨9352440182700233040739925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234960121800155360493283 9352440182700233040739925)
              ·
                refine ⟨109598908391018355946171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9352440182700233040739925 109598908391018355946171)
                ·
                  rfl

theorem cell23_5762964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 8].length) (baseStart_5762964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5762964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5762964 prefixEnd_5762964 := by exact prefixLift 5762964
  have htrace : WordTrace (prefixWord ++ tailWord_5762964) baseStart_5762964 baseEnd_5762964 := by
    simpa [prefixWord, tailWord_5762964, baseEnd_5762964] using wordTrace_append hprefix tailTrace_5762964
  have hstable : (prefixWord ++ tailWord_5762964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5762964).length < 2 ^ (prefixWord ++ tailWord_5762964).sum := by decide
  have hdescent : baseEnd_5762964 < baseStart_5762964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5762964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763001 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5763001 : Nat := 118140960795 + 5763001 * 2 ^ 59
def prefixEnd_5763001 : Nat := 4983230072969 + 3 ^ 40 * 5763001 * 2
def baseEnd_5763001 : Nat := 2959189525341711965783947

theorem tailTrace_5763001 : CollatzResearch.WordTrace tailWord_5763001 prefixEnd_5763001 2959189525341711965783947 := by
  unfold tailWord_5763001
  simp only [CollatzResearch.WordTrace]
  refine ⟨210193914594639094056384857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140129276396426062704256571 210193914594639094056384857)
  ·
    refine ⟨157645435945979320542288643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210193914594639094056384857 157645435945979320542288643)
    ·
      refine ⟨236468153918968980813432965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157645435945979320542288643 236468153918968980813432965)
      ·
        refine ⟨44337778859806683902518681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236468153918968980813432965 44337778859806683902518681)
        ·
          refine ⟨33253334144855012926889011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44337778859806683902518681 33253334144855012926889011)
          ·
            refine ⟨49880001217282519390333517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33253334144855012926889011 49880001217282519390333517)
            ·
              refine ⟨18705000456480944771375069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49880001217282519390333517 18705000456480944771375069)
              ·
                refine ⟨7014375171180354289265651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18705000456480944771375069 7014375171180354289265651)
                ·
                  refine ⟨10521562756770531433898477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014375171180354289265651 10521562756770531433898477)
                  ·
                    refine ⟨3945586033788949287711929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10521562756770531433898477 3945586033788949287711929)
                    ·
                      refine ⟨2959189525341711965783947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945586033788949287711929 2959189525341711965783947)
                      ·
                        rfl

theorem cell23_5763001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5763001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763001 prefixEnd_5763001 := by exact prefixLift 5763001
  have htrace : WordTrace (prefixWord ++ tailWord_5763001) baseStart_5763001 baseEnd_5763001 := by
    simpa [prefixWord, tailWord_5763001, baseEnd_5763001] using wordTrace_append hprefix tailTrace_5763001
  have hstable : (prefixWord ++ tailWord_5763001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763001).length < 2 ^ (prefixWord ++ tailWord_5763001).sum := by decide
  have hdescent : baseEnd_5763001 < baseStart_5763001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763067 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 4, 5]
def baseStart_5763067 : Nat := 118140960795 + 5763067 * 2 ^ 59
def prefixEnd_5763067 : Nat := 4983230072969 + 3 ^ 40 * 5763067 * 2
def baseEnd_5763067 : Nat := 986407805021636235852881

theorem tailTrace_5763067 : CollatzResearch.WordTrace tailWord_5763067 prefixEnd_5763067 986407805021636235852881 := by
  unfold tailWord_5763067
  simp only [CollatzResearch.WordTrace]
  refine ⟨210196321812399987328287455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140130881208266658218858303 210196321812399987328287455)
  ·
    refine ⟨315294482718599980992431183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210196321812399987328287455 315294482718599980992431183)
    ·
      refine ⟨472941724077899971488646775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315294482718599980992431183 472941724077899971488646775)
      ·
        refine ⟨709412586116849957232970163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472941724077899971488646775 709412586116849957232970163)
        ·
          refine ⟨1064118879175274935849455245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709412586116849957232970163 1064118879175274935849455245)
          ·
            refine ⟨399044579690728100943545717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064118879175274935849455245 399044579690728100943545717)
            ·
              refine ⟨37410429346005759463457411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 399044579690728100943545717 37410429346005759463457411)
              ·
                refine ⟨56115644019008639195186117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37410429346005759463457411 56115644019008639195186117)
                ·
                  refine ⟨10521683253564119849097397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56115644019008639195186117 10521683253564119849097397)
                  ·
                    refine ⟨986407805021636235852881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521683253564119849097397 986407805021636235852881)
                    ·
                      rfl

theorem cell23_5763067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].length) (baseStart_5763067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763067 prefixEnd_5763067 := by exact prefixLift 5763067
  have htrace : WordTrace (prefixWord ++ tailWord_5763067) baseStart_5763067 baseEnd_5763067 := by
    simpa [prefixWord, tailWord_5763067, baseEnd_5763067] using wordTrace_append hprefix tailTrace_5763067
  have hstable : (prefixWord ++ tailWord_5763067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763067).length < 2 ^ (prefixWord ++ tailWord_5763067).sum := by decide
  have hdescent : baseEnd_5763067 < baseStart_5763067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763077 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_5763077 : Nat := 118140960795 + 5763077 * 2 ^ 59
def prefixEnd_5763077 : Nat := 4983230072969 + 3 ^ 40 * 5763077 * 2
def baseEnd_5763077 : Nat := 2959228549871453668433597

theorem tailTrace_5763077 : CollatzResearch.WordTrace tailWord_5763077 prefixEnd_5763077 2959228549871453668433597 := by
  unfold tailWord_5763077
  simp only [CollatzResearch.WordTrace]
  refine ⟨210196686542363759036151485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140131124361575839357434323 210196686542363759036151485)
  ·
    refine ⟨78823757453386409638556807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210196686542363759036151485 78823757453386409638556807)
    ·
      refine ⟨118235636180079614457835211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78823757453386409638556807 118235636180079614457835211)
      ·
        refine ⟨177353454270119421686752817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118235636180079614457835211 177353454270119421686752817)
        ·
          refine ⟨133015090702589566265064613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177353454270119421686752817 133015090702589566265064613)
          ·
            refine ⟨24940329506735543674699615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133015090702589566265064613 24940329506735543674699615)
            ·
              refine ⟨37410494260103315512049423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24940329506735543674699615 37410494260103315512049423)
              ·
                refine ⟨56115741390154973268074135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37410494260103315512049423 56115741390154973268074135)
                ·
                  refine ⟨84173612085232459902111203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56115741390154973268074135 84173612085232459902111203)
                  ·
                    refine ⟨126260418127848689853166805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84173612085232459902111203 126260418127848689853166805)
                    ·
                      refine ⟨2959228549871453668433597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126260418127848689853166805 2959228549871453668433597)
                      ·
                        rfl

theorem cell23_5763077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_5763077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763077 prefixEnd_5763077 := by exact prefixLift 5763077
  have htrace : WordTrace (prefixWord ++ tailWord_5763077) baseStart_5763077 baseEnd_5763077 := by
    simpa [prefixWord, tailWord_5763077, baseEnd_5763077] using wordTrace_append hprefix tailTrace_5763077
  have hstable : (prefixWord ++ tailWord_5763077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763077).length < 2 ^ (prefixWord ++ tailWord_5763077).sum := by decide
  have hdescent : baseEnd_5763077 < baseStart_5763077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763082 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_5763082 : Nat := 118140960795 + 5763082 * 2 ^ 59
def prefixEnd_5763082 : Nat := 4983230072969 + 3 ^ 40 * 5763082 * 2
def baseEnd_5763082 : Nat := 2959231117274726148871075

theorem tailTrace_5763082 : CollatzResearch.WordTrace tailWord_5763082 prefixEnd_5763082 2959231117274726148871075 := by
  unfold tailWord_5763082
  simp only [CollatzResearch.WordTrace]
  refine ⟨52549217226836411222520875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140131245938230429926722333 52549217226836411222520875)
  ·
    refine ⟨78823825840254616833781313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52549217226836411222520875 78823825840254616833781313)
    ·
      refine ⟨59117869380190962625335985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78823825840254616833781313 59117869380190962625335985)
      ·
        refine ⟨44338402035143221969001989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59117869380190962625335985 44338402035143221969001989)
        ·
          refine ⟨8313450381589354119187873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44338402035143221969001989 8313450381589354119187873)
          ·
            refine ⟨6235087786192015589390905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8313450381589354119187873 6235087786192015589390905)
            ·
              refine ⟨4676315839644011692043179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235087786192015589390905 4676315839644011692043179)
              ·
                refine ⟨7014473759466017538064769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676315839644011692043179 7014473759466017538064769)
                ·
                  refine ⟨5260855319599513153548577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014473759466017538064769 5260855319599513153548577)
                  ·
                    refine ⟨3945641489699634865161433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5260855319599513153548577 3945641489699634865161433)
                    ·
                      refine ⟨2959231117274726148871075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945641489699634865161433 2959231117274726148871075)
                      ·
                        rfl

theorem cell23_5763082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_5763082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763082 prefixEnd_5763082 := by exact prefixLift 5763082
  have htrace : WordTrace (prefixWord ++ tailWord_5763082) baseStart_5763082 baseEnd_5763082 := by
    simpa [prefixWord, tailWord_5763082, baseEnd_5763082] using wordTrace_append hprefix tailTrace_5763082
  have hstable : (prefixWord ++ tailWord_5763082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763082).length < 2 ^ (prefixWord ++ tailWord_5763082).sum := by decide
  have hdescent : baseEnd_5763082 < baseStart_5763082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763101 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5763101 : Nat := 118140960795 + 5763101 * 2 ^ 59
def prefixEnd_5763101 : Nat := 4983230072969 + 3 ^ 40 * 5763101 * 2
def baseEnd_5763101 : Nat := 986413624469053858177829

theorem tailTrace_5763101 : CollatzResearch.WordTrace tailWord_5763101 prefixEnd_5763101 986413624469053858177829 := by
  unfold tailWord_5763101
  simp only [CollatzResearch.WordTrace]
  refine ⟨210197561894276811135025157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140131707929517874090016771 210197561894276811135025157)
  ·
    refine ⟨39412042855176902087817217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210197561894276811135025157 39412042855176902087817217)
    ·
      refine ⟨29559032141382676565862913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39412042855176902087817217 29559032141382676565862913)
      ·
        refine ⟨22169274106037007424397185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29559032141382676565862913 22169274106037007424397185)
        ·
          refine ⟨16626955579527755568297889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22169274106037007424397185 16626955579527755568297889)
          ·
            refine ⟨12470216684645816676223417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16626955579527755568297889 12470216684645816676223417)
            ·
              refine ⟨9352662513484362507167563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12470216684645816676223417 9352662513484362507167563)
              ·
                refine ⟨14028993770226543760751345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9352662513484362507167563 14028993770226543760751345)
                ·
                  refine ⟨10521745327669907820563509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14028993770226543760751345 10521745327669907820563509)
                  ·
                    refine ⟨986413624469053858177829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521745327669907820563509 986413624469053858177829)
                    ·
                      rfl

theorem cell23_5763101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5763101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763101 prefixEnd_5763101 := by exact prefixLift 5763101
  have htrace : WordTrace (prefixWord ++ tailWord_5763101) baseStart_5763101 baseEnd_5763101 := by
    simpa [prefixWord, tailWord_5763101, baseEnd_5763101] using wordTrace_append hprefix tailTrace_5763101
  have hstable : (prefixWord ++ tailWord_5763101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763101).length < 2 ^ (prefixWord ++ tailWord_5763101).sum := by decide
  have hdescent : baseEnd_5763101 < baseStart_5763101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763127 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 8]
def baseStart_5763127 : Nat := 118140960795 + 5763127 * 2 ^ 59
def prefixEnd_5763127 : Nat := 4983230072969 + 3 ^ 40 * 5763127 * 2
def baseEnd_5763127 : Nat := 328806024878242052534263

theorem tailTrace_5763127 : CollatzResearch.WordTrace tailWord_5763127 prefixEnd_5763127 328806024878242052534263 := by
  unfold tailWord_5763127
  simp only [CollatzResearch.WordTrace]
  refine ⟨210198510192182617575471635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140132340128121745050314423 210198510192182617575471635)
  ·
    refine ⟨315297765288273926363207453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210198510192182617575471635 315297765288273926363207453)
    ·
      refine ⟨118236661983102722386202795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315297765288273926363207453 118236661983102722386202795)
      ·
        refine ⟨177354992974654083579304193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118236661983102722386202795 177354992974654083579304193)
        ·
          refine ⟨133016244730990562684478145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177354992974654083579304193 133016244730990562684478145)
          ·
            refine ⟨99762183548242922013358609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133016244730990562684478145 99762183548242922013358609)
            ·
              refine ⟨74821637661182191510018957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99762183548242922013358609 74821637661182191510018957)
              ·
                refine ⟨28058114122943321816257109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74821637661182191510018957 28058114122943321816257109)
                ·
                  refine ⟨328806024878242052534263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28058114122943321816257109 328806024878242052534263)
                  ·
                    rfl

theorem cell23_5763127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 8].length) (baseStart_5763127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763127 prefixEnd_5763127 := by exact prefixLift 5763127
  have htrace : WordTrace (prefixWord ++ tailWord_5763127) baseStart_5763127 baseEnd_5763127 := by
    simpa [prefixWord, tailWord_5763127, baseEnd_5763127] using wordTrace_append hprefix tailTrace_5763127
  have hstable : (prefixWord ++ tailWord_5763127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763127).length < 2 ^ (prefixWord ++ tailWord_5763127).sum := by decide
  have hdescent : baseEnd_5763127 < baseStart_5763127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763131 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 1, 4]
def baseStart_5763131 : Nat := 118140960795 + 5763131 * 2 ^ 59
def prefixEnd_5763131 : Nat := 4983230072969 + 3 ^ 40 * 5763131 * 2
def baseEnd_5763131 : Nat := 986418759275598819052783

theorem tailTrace_5763131 : CollatzResearch.WordTrace tailWord_5763131 prefixEnd_5763131 986418759275598819052783 := by
  unfold tailWord_5763131
  simp only [CollatzResearch.WordTrace]
  refine ⟨210198656084168126258617247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140132437389445417505744831 210198656084168126258617247)
  ·
    refine ⟨315297984126252189387925871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210198656084168126258617247 315297984126252189387925871)
    ·
      refine ⟨472946976189378284081888807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315297984126252189387925871 472946976189378284081888807)
      ·
        refine ⟨709420464284067426122833211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472946976189378284081888807 709420464284067426122833211)
        ·
          refine ⟨1064130696426101139184249817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709420464284067426122833211 1064130696426101139184249817)
          ·
            refine ⟨798098022319575854388187363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064130696426101139184249817 798098022319575854388187363)
            ·
              refine ⟨1197147033479363781582281045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798098022319575854388187363 1197147033479363781582281045)
              ·
                refine ⟨3507266699646573578854339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1197147033479363781582281045 3507266699646573578854339)
                ·
                  refine ⟨5260900049469860368281509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507266699646573578854339 5260900049469860368281509)
                  ·
                    refine ⟨986418759275598819052783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260900049469860368281509 986418759275598819052783)
                    ·
                      rfl

theorem cell23_5763131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 4].length) (baseStart_5763131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763131 prefixEnd_5763131 := by exact prefixLift 5763131
  have htrace : WordTrace (prefixWord ++ tailWord_5763131) baseStart_5763131 baseEnd_5763131 := by
    simpa [prefixWord, tailWord_5763131, baseEnd_5763131] using wordTrace_append hprefix tailTrace_5763131
  have hstable : (prefixWord ++ tailWord_5763131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763131).length < 2 ^ (prefixWord ++ tailWord_5763131).sum := by decide
  have hdescent : baseEnd_5763131 < baseStart_5763131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763147 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_5763147 : Nat := 118140960795 + 5763147 * 2 ^ 59
def prefixEnd_5763147 : Nat := 4983230072969 + 3 ^ 40 * 5763147 * 2
def baseEnd_5763147 : Nat := 2959264493517268394558275

theorem tailTrace_5763147 : CollatzResearch.WordTrace tailWord_5763147 prefixEnd_5763147 2959264493517268394558275 := by
  unfold tailWord_5763147
  simp only [CollatzResearch.WordTrace]
  refine ⟨210199239652110160991199695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140132826434740107327466463 210199239652110160991199695)
  ·
    refine ⟨315298859478165241486799543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210199239652110160991199695 315298859478165241486799543)
    ·
      refine ⟨472948289217247862230199315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315298859478165241486799543 472948289217247862230199315)
      ·
        refine ⟨709422433825871793345298973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472948289217247862230199315 709422433825871793345298973)
        ·
          refine ⟨266033412684701922504487115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709422433825871793345298973 266033412684701922504487115)
          ·
            refine ⟨399050119027052883756730673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266033412684701922504487115 399050119027052883756730673)
            ·
              refine ⟨299287589270289662817548005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399050119027052883756730673 299287589270289662817548005)
              ·
                refine ⟨56116422988179311778290251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299287589270289662817548005 56116422988179311778290251)
                ·
                  refine ⟨84174634482268967667435377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56116422988179311778290251 84174634482268967667435377)
                  ·
                    refine ⟨63130975861701725750576533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84174634482268967667435377 63130975861701725750576533)
                    ·
                      refine ⟨2959264493517268394558275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63130975861701725750576533 2959264493517268394558275)
                      ·
                        rfl

theorem cell23_5763147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_5763147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763147 prefixEnd_5763147 := by exact prefixLift 5763147
  have htrace : WordTrace (prefixWord ++ tailWord_5763147) baseStart_5763147 baseEnd_5763147 := by
    simpa [prefixWord, tailWord_5763147, baseEnd_5763147] using wordTrace_append hprefix tailTrace_5763147
  have hstable : (prefixWord ++ tailWord_5763147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763147).length < 2 ^ (prefixWord ++ tailWord_5763147).sum := by decide
  have hdescent : baseEnd_5763147 < baseStart_5763147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763165 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5763165 : Nat := 118140960795 + 5763165 * 2 ^ 59
def prefixEnd_5763165 : Nat := 4983230072969 + 3 ^ 40 * 5763165 * 2
def baseEnd_5763165 : Nat := 986424578723016441377731

theorem tailTrace_5763165 : CollatzResearch.WordTrace tailWord_5763165 prefixEnd_5763165 986424578723016441377731 := by
  unfold tailWord_5763165
  simp only [CollatzResearch.WordTrace]
  refine ⟨210199896166044950065354949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140133264110696633376903299 210199896166044950065354949)
  ·
    refine ⟨39412480531133428137254053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210199896166044950065354949 39412480531133428137254053)
    ·
      refine ⟨7389840099587517775735135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39412480531133428137254053 7389840099587517775735135)
      ·
        refine ⟨11084760149381276663602703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7389840099587517775735135 11084760149381276663602703)
        ·
          refine ⟨16627140224071914995404055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084760149381276663602703 16627140224071914995404055)
          ·
            refine ⟨24940710336107872493106083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627140224071914995404055 24940710336107872493106083)
            ·
              refine ⟨37411065504161808739659125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24940710336107872493106083 37411065504161808739659125)
              ·
                refine ⟨3507287391015169569343043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37411065504161808739659125 3507287391015169569343043)
                ·
                  refine ⟨5260931086522754354014565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507287391015169569343043 5260931086522754354014565)
                  ·
                    refine ⟨986424578723016441377731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260931086522754354014565 986424578723016441377731)
                    ·
                      rfl

theorem cell23_5763165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5763165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763165 prefixEnd_5763165 := by exact prefixLift 5763165
  have htrace : WordTrace (prefixWord ++ tailWord_5763165) baseStart_5763165 baseEnd_5763165 := by
    simpa [prefixWord, tailWord_5763165, baseEnd_5763165] using wordTrace_append hprefix tailTrace_5763165
  have hstable : (prefixWord ++ tailWord_5763165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763165).length < 2 ^ (prefixWord ++ tailWord_5763165).sum := by decide
  have hdescent : baseEnd_5763165 < baseStart_5763165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763178 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_5763178 : Nat := 118140960795 + 5763178 * 2 ^ 59
def prefixEnd_5763178 : Nat := 4983230072969 + 3 ^ 40 * 5763178 * 2
def baseEnd_5763178 : Nat := 328808934601950863696737

theorem tailTrace_5763178 : CollatzResearch.WordTrace tailWord_5763178 prefixEnd_5763178 328808934601950863696737 := by
  unfold tailWord_5763178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52550092578749463321394547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140133580209998568857052125 52550092578749463321394547)
  ·
    refine ⟨78825138868124194982091821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52550092578749463321394547 78825138868124194982091821)
    ·
      refine ⟨29559427075546573118284433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78825138868124194982091821 29559427075546573118284433)
      ·
        refine ⟨22169570306659929838713325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29559427075546573118284433 22169570306659929838713325)
        ·
          refine ⟨8313588864997473689517497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22169570306659929838713325 8313588864997473689517497)
          ·
            refine ⟨6235191648748105267138123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8313588864997473689517497 6235191648748105267138123)
            ·
              refine ⟨9352787473122157900707185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6235191648748105267138123 9352787473122157900707185)
              ·
                refine ⟨7014590604841618425530389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352787473122157900707185 7014590604841618425530389)
                ·
                  refine ⟨328808934601950863696737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7014590604841618425530389 328808934601950863696737)
                  ·
                    rfl

theorem cell23_5763178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_5763178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763178 prefixEnd_5763178 := by exact prefixLift 5763178
  have htrace : WordTrace (prefixWord ++ tailWord_5763178) baseStart_5763178 baseEnd_5763178 := by
    simpa [prefixWord, tailWord_5763178, baseEnd_5763178] using wordTrace_append hprefix tailTrace_5763178
  have hstable : (prefixWord ++ tailWord_5763178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763178).length < 2 ^ (prefixWord ++ tailWord_5763178).sum := by decide
  have hdescent : baseEnd_5763178 < baseStart_5763178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 12]
def baseStart_5763187 : Nat := 118140960795 + 5763187 * 2 ^ 59
def prefixEnd_5763187 : Nat := 4983230072969 + 3 ^ 40 * 5763187 * 2
def baseEnd_5763187 : Nat := 986428344247816079352697

theorem tailTrace_5763187 : CollatzResearch.WordTrace tailWord_5763187 prefixEnd_5763187 986428344247816079352697 := by
  unfold tailWord_5763187
  simp only [CollatzResearch.WordTrace]
  refine ⟨210200698571965247822655815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140133799047976831881770543 210200698571965247822655815)
  ·
    refine ⟨315301047857947871733983723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210200698571965247822655815 315301047857947871733983723)
    ·
      refine ⟨472951571786921807600975585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315301047857947871733983723 472951571786921807600975585)
      ·
        refine ⟨354713678840191355700731689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472951571786921807600975585 354713678840191355700731689)
        ·
          refine ⟨266035259130143516775548767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354713678840191355700731689 266035259130143516775548767)
          ·
            refine ⟨399052888695215275163323151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266035259130143516775548767 399052888695215275163323151)
            ·
              refine ⟨598579333042822912744984727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399052888695215275163323151 598579333042822912744984727)
              ·
                refine ⟨897868999564234369117477091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598579333042822912744984727 897868999564234369117477091)
                ·
                  refine ⟨1346803499346351553676215637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897868999564234369117477091 1346803499346351553676215637)
                  ·
                    refine ⟨986428344247816079352697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1346803499346351553676215637 986428344247816079352697)
                    ·
                      rfl

theorem cell23_5763187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_5763187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763187 prefixEnd_5763187 := by exact prefixLift 5763187
  have htrace : WordTrace (prefixWord ++ tailWord_5763187) baseStart_5763187 baseEnd_5763187 := by
    simpa [prefixWord, tailWord_5763187, baseEnd_5763187] using wordTrace_append hprefix tailTrace_5763187
  have hstable : (prefixWord ++ tailWord_5763187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763187).length < 2 ^ (prefixWord ++ tailWord_5763187).sum := by decide
  have hdescent : baseEnd_5763187 < baseStart_5763187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763208 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_5763208 : Nat := 118140960795 + 5763208 * 2 ^ 59
def prefixEnd_5763208 : Nat := 4983230072969 + 3 ^ 40 * 5763208 * 2
def baseEnd_5763208 : Nat := 986431938612397551965165

theorem tailTrace_5763208 : CollatzResearch.WordTrace tailWord_5763208 prefixEnd_5763208 986431938612397551965165 := by
  unfold tailWord_5763208
  simp only [CollatzResearch.WordTrace]
  refine ⟨105100732252444584204585139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140134309669926112272780185 105100732252444584204585139)
  ·
    refine ⟨157651098378666876306877709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105100732252444584204585139 157651098378666876306877709)
    ·
      refine ⟨59119161892000078615079141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157651098378666876306877709 59119161892000078615079141)
      ·
        refine ⟨11084842854750014740327339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59119161892000078615079141 11084842854750014740327339)
        ·
          refine ⟨16627264282125022110491009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084842854750014740327339 16627264282125022110491009)
          ·
            refine ⟨12470448211593766582868257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16627264282125022110491009 12470448211593766582868257)
            ·
              refine ⟨9352836158695324937151193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12470448211593766582868257 9352836158695324937151193)
              ·
                refine ⟨7014627119021493702863395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352836158695324937151193 7014627119021493702863395)
                ·
                  refine ⟨10521940678532240554295093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014627119021493702863395 10521940678532240554295093)
                  ·
                    refine ⟨986431938612397551965165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521940678532240554295093 986431938612397551965165)
                    ·
                      rfl

theorem cell23_5763208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_5763208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763208 prefixEnd_5763208 := by exact prefixLift 5763208
  have htrace : WordTrace (prefixWord ++ tailWord_5763208) baseStart_5763208 baseEnd_5763208 := by
    simpa [prefixWord, tailWord_5763208, baseEnd_5763208] using wordTrace_append hprefix tailTrace_5763208
  have hstable : (prefixWord ++ tailWord_5763208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763208).length < 2 ^ (prefixWord ++ tailWord_5763208).sum := by decide
  have hdescent : baseEnd_5763208 < baseStart_5763208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763231 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5763231 : Nat := 118140960795 + 5763231 * 2 ^ 59
def prefixEnd_5763231 : Nat := 4983230072969 + 3 ^ 40 * 5763231 * 2
def baseEnd_5763231 : Nat := 2959307625892246065907889

theorem tailTrace_5763231 : CollatzResearch.WordTrace tailWord_5763231 prefixEnd_5763231 2959307625892246065907889 := by
  unfold tailWord_5763231
  simp only [CollatzResearch.WordTrace]
  refine ⟨210202303383805843337257547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140134868922537228891505031 210202303383805843337257547)
  ·
    refine ⟨315303455075708765005886321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210202303383805843337257547 315303455075708765005886321)
    ·
      refine ⟨236477591306781573754414741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315303455075708765005886321 236477591306781573754414741)
      ·
        refine ⟨11084887092505386269738191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236477591306781573754414741 11084887092505386269738191)
        ·
          refine ⟨16627330638758079404607287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11084887092505386269738191 16627330638758079404607287)
          ·
            refine ⟨24940995958137119106910931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627330638758079404607287 24940995958137119106910931)
            ·
              refine ⟨37411493937205678660366397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24940995958137119106910931 37411493937205678660366397)
              ·
                refine ⟨14029310226452129497637399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37411493937205678660366397 14029310226452129497637399)
                ·
                  refine ⟨21043965339678194246456099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14029310226452129497637399 21043965339678194246456099)
                  ·
                    refine ⟨31565948009517291369684149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21043965339678194246456099 31565948009517291369684149)
                    ·
                      refine ⟨2959307625892246065907889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31565948009517291369684149 2959307625892246065907889)
                      ·
                        rfl

theorem cell23_5763231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5763231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763231 prefixEnd_5763231 := by exact prefixLift 5763231
  have htrace : WordTrace (prefixWord ++ tailWord_5763231) baseStart_5763231 baseEnd_5763231 := by
    simpa [prefixWord, tailWord_5763231, baseEnd_5763231] using wordTrace_append hprefix tailTrace_5763231
  have hstable : (prefixWord ++ tailWord_5763231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763231).length < 2 ^ (prefixWord ++ tailWord_5763231).sum := by decide
  have hdescent : baseEnd_5763231 < baseStart_5763231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763239 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5763239 : Nat := 118140960795 + 5763239 * 2 ^ 59
def prefixEnd_5763239 : Nat := 4983230072969 + 3 ^ 40 * 5763239 * 2
def baseEnd_5763239 : Nat := 2959311733737482034607853

theorem tailTrace_5763239 : CollatzResearch.WordTrace tailWord_5763239 prefixEnd_5763239 2959311733737482034607853 := by
  unfold tailWord_5763239
  simp only [CollatzResearch.WordTrace]
  refine ⟨210202595167776860703548771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140135063445184573802365847 210202595167776860703548771)
  ·
    refine ⟨315303892751665291055323157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210202595167776860703548771 315303892751665291055323157)
    ·
      refine ⟨14779869972734310518218273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 315303892751665291055323157 14779869972734310518218273)
      ·
        refine ⟨11084902479550732888663705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14779869972734310518218273 11084902479550732888663705)
        ·
          refine ⟨8313676859663049666497779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11084902479550732888663705 8313676859663049666497779)
          ·
            refine ⟨12470515289494574499746669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313676859663049666497779 12470515289494574499746669)
            ·
              refine ⟨4676443233560465437405001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12470515289494574499746669 4676443233560465437405001)
              ·
                refine ⟨3507332425170349078053751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676443233560465437405001 3507332425170349078053751)
                ·
                  refine ⟨5260998637755523617080627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507332425170349078053751 5260998637755523617080627)
                  ·
                    refine ⟨7891497956633285425620941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5260998637755523617080627 7891497956633285425620941)
                    ·
                      refine ⟨2959311733737482034607853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891497956633285425620941 2959311733737482034607853)
                      ·
                        rfl

theorem cell23_5763239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5763239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763239 prefixEnd_5763239 := by exact prefixLift 5763239
  have htrace : WordTrace (prefixWord ++ tailWord_5763239) baseStart_5763239 baseEnd_5763239 := by
    simpa [prefixWord, tailWord_5763239, baseEnd_5763239] using wordTrace_append hprefix tailTrace_5763239
  have hstable : (prefixWord ++ tailWord_5763239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763239).length < 2 ^ (prefixWord ++ tailWord_5763239).sum := by decide
  have hdescent : baseEnd_5763239 < baseStart_5763239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763255 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 2, 4]
def baseStart_5763255 : Nat := 118140960795 + 5763255 * 2 ^ 59
def prefixEnd_5763255 : Nat := 4983230072969 + 3 ^ 40 * 5763255 * 2
def baseEnd_5763255 : Nat := 986439983142651324002593

theorem tailTrace_5763255 : CollatzResearch.WordTrace tailWord_5763255 prefixEnd_5763255 986439983142651324002593 := by
  unfold tailWord_5763255
  simp only [CollatzResearch.WordTrace]
  refine ⟨210203178735718895436131219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140135452490479263624087479 210203178735718895436131219)
  ·
    refine ⟨315304768103578343154196829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210203178735718895436131219 315304768103578343154196829)
    ·
      refine ⟨118239288038841878682823811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315304768103578343154196829 118239288038841878682823811)
      ·
        refine ⟨177358932058262818024235717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118239288038841878682823811 177358932058262818024235717)
        ·
          refine ⟨33254799760924278379544197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177358932058262818024235717 33254799760924278379544197)
          ·
            refine ⟨6235274955173302196164537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33254799760924278379544197 6235274955173302196164537)
            ·
              refine ⟨4676456216379976647123403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235274955173302196164537 4676456216379976647123403)
              ·
                refine ⟨7014684324569964970685105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676456216379976647123403 7014684324569964970685105)
                ·
                  refine ⟨5261013243427473728013829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7014684324569964970685105 5261013243427473728013829)
                  ·
                    refine ⟨986439983142651324002593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261013243427473728013829 986439983142651324002593)
                    ·
                      rfl

theorem cell23_5763255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_5763255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763255 prefixEnd_5763255 := by exact prefixLift 5763255
  have htrace : WordTrace (prefixWord ++ tailWord_5763255) baseStart_5763255 baseEnd_5763255 := by
    simpa [prefixWord, tailWord_5763255, baseEnd_5763255] using wordTrace_append hprefix tailTrace_5763255
  have hstable : (prefixWord ++ tailWord_5763255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763255).length < 2 ^ (prefixWord ++ tailWord_5763255).sum := by decide
  have hdescent : baseEnd_5763255 < baseStart_5763255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763261 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5763261 : Nat := 118140960795 + 5763261 * 2 ^ 59
def prefixEnd_5763261 : Nat := 4983230072969 + 3 ^ 40 * 5763261 * 2
def baseEnd_5763261 : Nat := 2959323030311880948532751

theorem tailTrace_5763261 : CollatzResearch.WordTrace tailWord_5763261 prefixEnd_5763261 2959323030311880948532751 := by
  unfold tailWord_5763261
  simp only [CollatzResearch.WordTrace]
  refine ⟨210203397573697158460849637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140135598382464772307233091 210203397573697158460849637)
  ·
    refine ⟨39413137045068217211409307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210203397573697158460849637 39413137045068217211409307)
    ·
      refine ⟨59119705567602325817113961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39413137045068217211409307 59119705567602325817113961)
      ·
        refine ⟨44339779175701744362835471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59119705567602325817113961 44339779175701744362835471)
        ·
          refine ⟨66509668763552616544253207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44339779175701744362835471 66509668763552616544253207)
          ·
            refine ⟨99764503145328924816379811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66509668763552616544253207 99764503145328924816379811)
            ·
              refine ⟨149646754717993387224569717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99764503145328924816379811 149646754717993387224569717)
              ·
                refine ⟨14029383254811880052303411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149646754717993387224569717 14029383254811880052303411)
                ·
                  refine ⟨21044074882217820078455117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14029383254811880052303411 21044074882217820078455117)
                  ·
                    refine ⟨7891528080831682529420669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21044074882217820078455117 7891528080831682529420669)
                    ·
                      refine ⟨2959323030311880948532751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891528080831682529420669 2959323030311880948532751)
                      ·
                        rfl

theorem cell23_5763261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5763261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763261 prefixEnd_5763261 := by exact prefixLift 5763261
  have htrace : WordTrace (prefixWord ++ tailWord_5763261) baseStart_5763261 baseEnd_5763261 := by
    simpa [prefixWord, tailWord_5763261, baseEnd_5763261] using wordTrace_append hprefix tailTrace_5763261
  have hstable : (prefixWord ++ tailWord_5763261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763261).length < 2 ^ (prefixWord ++ tailWord_5763261).sum := by decide
  have hdescent : baseEnd_5763261 < baseStart_5763261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763262 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_5763262 : Nat := 118140960795 + 5763262 * 2 ^ 59
def prefixEnd_5763262 : Nat := 4983230072969 + 3 ^ 40 * 5763262 * 2
def baseEnd_5763262 : Nat := 2959323543792535444620247

theorem tailTrace_5763262 : CollatzResearch.WordTrace tailWord_5763262 prefixEnd_5763262 2959323543792535444620247 := by
  unfold tailWord_5763262
  simp only [CollatzResearch.WordTrace]
  refine ⟨26275429255836691953954505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140135622697795690421090693 26275429255836691953954505)
  ·
    refine ⟨19706571941877518965465879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26275429255836691953954505 19706571941877518965465879)
    ·
      refine ⟨29559857912816278448198819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19706571941877518965465879 29559857912816278448198819)
      ·
        refine ⟨44339786869224417672298229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29559857912816278448198819 44339786869224417672298229)
        ·
          refine ⟨4156855018989789156777959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44339786869224417672298229 4156855018989789156777959)
          ·
            refine ⟨6235282528484683735166939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156855018989789156777959 6235282528484683735166939)
            ·
              refine ⟨9352923792727025602750409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6235282528484683735166939 9352923792727025602750409)
              ·
                refine ⟨7014692844545269202062807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9352923792727025602750409 7014692844545269202062807)
                ·
                  refine ⟨10522039266817903803094211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7014692844545269202062807 10522039266817903803094211)
                  ·
                    refine ⟨15783058900226855704641317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10522039266817903803094211 15783058900226855704641317)
                    ·
                      refine ⟨2959323543792535444620247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15783058900226855704641317 2959323543792535444620247)
                      ·
                        rfl

theorem cell23_5763262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_5763262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763262 prefixEnd_5763262 := by exact prefixLift 5763262
  have htrace : WordTrace (prefixWord ++ tailWord_5763262) baseStart_5763262 baseEnd_5763262 := by
    simpa [prefixWord, tailWord_5763262, baseEnd_5763262] using wordTrace_append hprefix tailTrace_5763262
  have hstable : (prefixWord ++ tailWord_5763262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763262).length < 2 ^ (prefixWord ++ tailWord_5763262).sum := by decide
  have hdescent : baseEnd_5763262 < baseStart_5763262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763265 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5763265 : Nat := 118140960795 + 5763265 * 2 ^ 59
def prefixEnd_5763265 : Nat := 4983230072969 + 3 ^ 40 * 5763265 * 2
def baseEnd_5763265 : Nat := 2959325084234498932882733

theorem tailTrace_5763265 : CollatzResearch.WordTrace tailWord_5763265 prefixEnd_5763265 2959325084234498932882733 := by
  unfold tailWord_5763265
  simp only [CollatzResearch.WordTrace]
  refine ⟨210203543465682667143995249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140135695643788444762663499 210203543465682667143995249)
  ·
    refine ⟨157652657599262000357996437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210203543465682667143995249 157652657599262000357996437)
    ·
      refine ⟨7389968324965406266781083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157652657599262000357996437 7389968324965406266781083)
      ·
        refine ⟨11084952487448109400171625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7389968324965406266781083 11084952487448109400171625)
        ·
          refine ⟨8313714365586082050128719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11084952487448109400171625 8313714365586082050128719)
          ·
            refine ⟨12470571548379123075193079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313714365586082050128719 12470571548379123075193079)
            ·
              refine ⟨18705857322568684612789619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470571548379123075193079 18705857322568684612789619)
              ·
                refine ⟨28058785983853026919184429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18705857322568684612789619 28058785983853026919184429)
                ·
                  refine ⟨10522044743944885094694161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28058785983853026919184429 10522044743944885094694161)
                  ·
                    refine ⟨7891533557958663821020621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10522044743944885094694161 7891533557958663821020621)
                    ·
                      refine ⟨2959325084234498932882733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891533557958663821020621 2959325084234498932882733)
                      ·
                        rfl

theorem cell23_5763265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5763265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763265 prefixEnd_5763265 := by exact prefixLift 5763265
  have htrace : WordTrace (prefixWord ++ tailWord_5763265) baseStart_5763265 baseEnd_5763265 := by
    simpa [prefixWord, tailWord_5763265, baseEnd_5763265] using wordTrace_append hprefix tailTrace_5763265
  have hstable : (prefixWord ++ tailWord_5763265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763265).length < 2 ^ (prefixWord ++ tailWord_5763265).sum := by decide
  have hdescent : baseEnd_5763265 < baseStart_5763265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763278 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_5763278 : Nat := 118140960795 + 5763278 * 2 ^ 59
def prefixEnd_5763278 : Nat := 4983230072969 + 3 ^ 40 * 5763278 * 2
def baseEnd_5763278 : Nat := 2959331759483007382020173

theorem tailTrace_5763278 : CollatzResearch.WordTrace tailWord_5763278 prefixEnd_5763278 2959331759483007382020173 := by
  unfold tailWord_5763278
  simp only [CollatzResearch.WordTrace]
  refine ⟨26275502201829446295527311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140136011743090380242812325 26275502201829446295527311)
  ·
    refine ⟨39413253302744169443290967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26275502201829446295527311 39413253302744169443290967)
    ·
      refine ⟨59119879954116254164936451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39413253302744169443290967 59119879954116254164936451)
      ·
        refine ⟨88679819931174381247404677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59119879954116254164936451 88679819931174381247404677)
        ·
          refine ⟨16627466237095196483888377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88679819931174381247404677 16627466237095196483888377)
          ·
            refine ⟨12470599677821397362916283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16627466237095196483888377 12470599677821397362916283)
            ·
              refine ⟨18705899516732096044374425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470599677821397362916283 18705899516732096044374425)
              ·
                refine ⟨14029424637549072033280819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18705899516732096044374425 14029424637549072033280819)
                ·
                  refine ⟨21044136956323608049921229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14029424637549072033280819 21044136956323608049921229)
                  ·
                    refine ⟨7891551358621353018720461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21044136956323608049921229 7891551358621353018720461)
                    ·
                      refine ⟨2959331759483007382020173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891551358621353018720461 2959331759483007382020173)
                      ·
                        rfl

theorem cell23_5763278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_5763278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763278 prefixEnd_5763278 := by exact prefixLift 5763278
  have htrace : WordTrace (prefixWord ++ tailWord_5763278) baseStart_5763278 baseEnd_5763278 := by
    simpa [prefixWord, tailWord_5763278, baseEnd_5763278] using wordTrace_append hprefix tailTrace_5763278
  have hstable : (prefixWord ++ tailWord_5763278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763278).length < 2 ^ (prefixWord ++ tailWord_5763278).sum := by decide
  have hdescent : baseEnd_5763278 < baseStart_5763278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763301 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5763301 : Nat := 118140960795 + 5763301 * 2 ^ 59
def prefixEnd_5763301 : Nat := 4983230072969 + 3 ^ 40 * 5763301 * 2
def baseEnd_5763301 : Nat := 2959343569538060792032567

theorem tailTrace_5763301 : CollatzResearch.WordTrace tailWord_5763301 prefixEnd_5763301 2959343569538060792032567 := by
  unfold tailWord_5763301
  simp only [CollatzResearch.WordTrace]
  refine ⟨210204856493552245292305757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140136570995701496861537171 210204856493552245292305757)
  ·
    refine ⟨78826821185082091984614659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210204856493552245292305757 78826821185082091984614659)
    ·
      refine ⟨118240231777623137976921989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78826821185082091984614659 118240231777623137976921989)
      ·
        refine ⟨22170043458304338370672873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118240231777623137976921989 22170043458304338370672873)
        ·
          refine ⟨16627532593728253778004655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22170043458304338370672873 16627532593728253778004655)
          ·
            refine ⟨24941298890592380667006983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627532593728253778004655 24941298890592380667006983)
            ·
              refine ⟨37411948335888571000510475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24941298890592380667006983 37411948335888571000510475)
              ·
                refine ⟨56117922503832856500765713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37411948335888571000510475 56117922503832856500765713)
                ·
                  refine ⟨42088441877874642375574285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56117922503832856500765713 42088441877874642375574285)
                  ·
                    refine ⟨15783165704202990890840357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42088441877874642375574285 15783165704202990890840357)
                    ·
                      refine ⟨2959343569538060792032567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15783165704202990890840357 2959343569538060792032567)
                      ·
                        rfl

theorem cell23_5763301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5763301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763301 prefixEnd_5763301 := by exact prefixLift 5763301
  have htrace : WordTrace (prefixWord ++ tailWord_5763301) baseStart_5763301 baseEnd_5763301 := by
    simpa [prefixWord, tailWord_5763301, baseEnd_5763301] using wordTrace_append hprefix tailTrace_5763301
  have hstable : (prefixWord ++ tailWord_5763301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763301).length < 2 ^ (prefixWord ++ tailWord_5763301).sum := by decide
  have hdescent : baseEnd_5763301 < baseStart_5763301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763311 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 6]
def baseStart_5763311 : Nat := 118140960795 + 5763311 * 2 ^ 59
def prefixEnd_5763311 : Nat := 4983230072969 + 3 ^ 40 * 5763311 * 2
def baseEnd_5763311 : Nat := 986449568114868584302507

theorem tailTrace_5763311 : CollatzResearch.WordTrace tailWord_5763311 prefixEnd_5763311 986449568114868584302507 := by
  unfold tailWord_5763311
  simp only [CollatzResearch.WordTrace]
  refine ⟨210205221223516017000169787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140136814149010678000113191 210205221223516017000169787)
  ·
    refine ⟨315307831835274025500254681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210205221223516017000169787 315307831835274025500254681)
    ·
      refine ⟨236480873876455519125191011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315307831835274025500254681 236480873876455519125191011)
      ·
        refine ⟨354721310814683278687786517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236480873876455519125191011 354721310814683278687786517)
        ·
          refine ⟨16627561444438278688489993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354721310814683278687786517 16627561444438278688489993)
          ·
            refine ⟨12470671083328709016367495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16627561444438278688489993 12470671083328709016367495)
            ·
              refine ⟨18706006624993063524551243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470671083328709016367495 18706006624993063524551243)
              ·
                refine ⟨28059009937489595286826865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18706006624993063524551243 28059009937489595286826865)
                ·
                  refine ⟨21044257453117196465120149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28059009937489595286826865 21044257453117196465120149)
                  ·
                    refine ⟨986449568114868584302507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21044257453117196465120149 986449568114868584302507)
                    ·
                      rfl

theorem cell23_5763311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_5763311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763311 prefixEnd_5763311 := by exact prefixLift 5763311
  have htrace : WordTrace (prefixWord ++ tailWord_5763311) baseStart_5763311 baseEnd_5763311 := by
    simpa [prefixWord, tailWord_5763311, baseEnd_5763311] using wordTrace_append hprefix tailTrace_5763311
  have hstable : (prefixWord ++ tailWord_5763311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763311).length < 2 ^ (prefixWord ++ tailWord_5763311).sum := by decide
  have hdescent : baseEnd_5763311 < baseStart_5763311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763391 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_5763391 : Nat := 118140960795 + 5763391 * 2 ^ 59
def prefixEnd_5763391 : Nat := 4983230072969 + 3 ^ 40 * 5763391 * 2
def baseEnd_5763391 : Nat := 2959389782796965439907153

theorem tailTrace_5763391 : CollatzResearch.WordTrace tailWord_5763391 prefixEnd_5763391 2959389782796965439907153 := by
  unfold tailWord_5763391
  simp only [CollatzResearch.WordTrace]
  refine ⟨210208139063226190663082027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140138759375484127108721351 210208139063226190663082027)
  ·
    refine ⟨315312208594839285994623041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210208139063226190663082027 315312208594839285994623041)
    ·
      refine ⟨236484156446129464495967281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315312208594839285994623041 236484156446129464495967281)
      ·
        refine ⟨177363117334597098371975461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236484156446129464495967281 177363117334597098371975461)
        ·
          refine ⟨33255584500236955944745399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177363117334597098371975461 33255584500236955944745399)
          ·
            refine ⟨49883376750355433917118099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33255584500236955944745399 49883376750355433917118099)
            ·
              refine ⟨74825065125533150875677149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49883376750355433917118099 74825065125533150875677149)
              ·
                refine ⟨28059399422074931578378931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74825065125533150875677149 28059399422074931578378931)
                ·
                  refine ⟨42089099133112397367568397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28059399422074931578378931 42089099133112397367568397)
                  ·
                    refine ⟨15783412174917149012838149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42089099133112397367568397 15783412174917149012838149)
                    ·
                      refine ⟨2959389782796965439907153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15783412174917149012838149 2959389782796965439907153)
                      ·
                        rfl

theorem cell23_5763391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_5763391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763391 prefixEnd_5763391 := by exact prefixLift 5763391
  have htrace : WordTrace (prefixWord ++ tailWord_5763391) baseStart_5763391 baseEnd_5763391 := by
    simpa [prefixWord, tailWord_5763391, baseEnd_5763391] using wordTrace_append hprefix tailTrace_5763391
  have hstable : (prefixWord ++ tailWord_5763391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763391).length < 2 ^ (prefixWord ++ tailWord_5763391).sum := by decide
  have hdescent : baseEnd_5763391 < baseStart_5763391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763408 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_5763408 : Nat := 118140960795 + 5763408 * 2 ^ 59
def prefixEnd_5763408 : Nat := 4983230072969 + 3 ^ 40 * 5763408 * 2
def baseEnd_5763408 : Nat := 2959398511968091873394575

theorem tailTrace_5763408 : CollatzResearch.WordTrace tailWord_5763408 prefixEnd_5763408 2959398511968091873394575 := by
  unfold tailWord_5763408
  simp only [CollatzResearch.WordTrace]
  refine ⟨105104379552082301283225439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140139172736109735044300585 105104379552082301283225439)
  ·
    refine ⟨157656569328123451924838159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105104379552082301283225439 157656569328123451924838159)
    ·
      refine ⟨236484853992185177887257239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157656569328123451924838159 236484853992185177887257239)
      ·
        refine ⟨354727280988277766830885859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236484853992185177887257239 354727280988277766830885859)
        ·
          refine ⟨532090921482416650246328789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354727280988277766830885859 532090921482416650246328789)
          ·
            refine ⟨12470880972244140240148331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 532090921482416650246328789 12470880972244140240148331)
            ·
              refine ⟨18706321458366210360222497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470880972244140240148331 18706321458366210360222497)
              ·
                refine ⟨14029741093774657770166873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18706321458366210360222497 14029741093774657770166873)
                ·
                  refine ⟨10522305820330993327625155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14029741093774657770166873 10522305820330993327625155)
                  ·
                    refine ⟨15783458730496489991437733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10522305820330993327625155 15783458730496489991437733)
                    ·
                      refine ⟨2959398511968091873394575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15783458730496489991437733 2959398511968091873394575)
                      ·
                        rfl

theorem cell23_5763408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_5763408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763408 prefixEnd_5763408 := by exact prefixLift 5763408
  have htrace : WordTrace (prefixWord ++ tailWord_5763408) baseStart_5763408 baseEnd_5763408 := by
    simpa [prefixWord, tailWord_5763408, baseEnd_5763408] using wordTrace_append hprefix tailTrace_5763408
  have hstable : (prefixWord ++ tailWord_5763408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763408).length < 2 ^ (prefixWord ++ tailWord_5763408).sum := by decide
  have hdescent : baseEnd_5763408 < baseStart_5763408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763411 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3]
def baseStart_5763411 : Nat := 118140960795 + 5763411 * 2 ^ 59
def prefixEnd_5763411 : Nat := 4983230072969 + 3 ^ 40 * 5763411 * 2
def baseEnd_5763411 : Nat := 2959400052410055361657061

theorem tailTrace_5763411 : CollatzResearch.WordTrace tailWord_5763411 prefixEnd_5763411 2959400052410055361657061 := by
  unfold tailWord_5763411
  simp only [CollatzResearch.WordTrace]
  refine ⟨210208868523153734078810087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140139245682102489385873391 210208868523153734078810087)
  ·
    refine ⟨315313302784730601118215131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210208868523153734078810087 315313302784730601118215131)
    ·
      refine ⟨472969954177095901677322697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315313302784730601118215131 472969954177095901677322697)
      ·
        refine ⟨354727465632821926257992023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472969954177095901677322697 354727465632821926257992023)
        ·
          refine ⟨532091198449232889386988035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354727465632821926257992023 532091198449232889386988035)
          ·
            refine ⟨798136797673849334080482053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532091198449232889386988035 798136797673849334080482053)
            ·
              refine ⟨149650649563846750140090385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 798136797673849334080482053 149650649563846750140090385)
              ·
                refine ⟨112237987172885062605067789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149650649563846750140090385 112237987172885062605067789)
                ·
                  refine ⟨42089245189831898476900421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112237987172885062605067789 42089245189831898476900421)
                  ·
                    refine ⟨7891733473093480964418829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42089245189831898476900421 7891733473093480964418829)
                    ·
                      refine ⟨2959400052410055361657061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891733473093480964418829 2959400052410055361657061)
                      ·
                        rfl

theorem cell23_5763411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_5763411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763411 prefixEnd_5763411 := by exact prefixLift 5763411
  have htrace : WordTrace (prefixWord ++ tailWord_5763411) baseStart_5763411 baseEnd_5763411 := by
    simpa [prefixWord, tailWord_5763411, baseEnd_5763411] using wordTrace_append hprefix tailTrace_5763411
  have hstable : (prefixWord ++ tailWord_5763411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763411).length < 2 ^ (prefixWord ++ tailWord_5763411).sum := by decide
  have hdescent : baseEnd_5763411 < baseStart_5763411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763428 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_5763428 : Nat := 118140960795 + 5763428 * 2 ^ 59
def prefixEnd_5763428 : Nat := 4983230072969 + 3 ^ 40 * 5763428 * 2
def baseEnd_5763428 : Nat := 2959408781581181795144483

theorem tailTrace_5763428 : CollatzResearch.WordTrace tailWord_5763428 prefixEnd_5763428 2959408781581181795144483 := by
  unfold tailWord_5763428
  simp only [CollatzResearch.WordTrace]
  refine ⟨105104744282046072991089469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140139659042728097321452625 105104744282046072991089469)
  ·
    refine ⟨39414279105767277371658551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105104744282046072991089469 39414279105767277371658551)
    ·
      refine ⟨59121418658650916057487827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39414279105767277371658551 59121418658650916057487827)
      ·
        refine ⟨88682127987976374086231741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59121418658650916057487827 88682127987976374086231741)
        ·
          refine ⟨33255797995491140282336903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88682127987976374086231741 33255797995491140282336903)
          ·
            refine ⟨49883696993236710423505355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33255797995491140282336903 49883696993236710423505355)
            ·
              refine ⟨74825545489855065635258033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49883696993236710423505355 74825545489855065635258033)
              ·
                refine ⟨56119159117391299226443525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74825545489855065635258033 56119159117391299226443525)
                ·
                  refine ⟨10522342334510868604958161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56119159117391299226443525 10522342334510868604958161)
                  ·
                    refine ⟨7891756750883151453718621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10522342334510868604958161 7891756750883151453718621)
                    ·
                      refine ⟨2959408781581181795144483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891756750883151453718621 2959408781581181795144483)
                      ·
                        rfl

theorem cell23_5763428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_5763428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763428 prefixEnd_5763428 := by exact prefixLift 5763428
  have htrace : WordTrace (prefixWord ++ tailWord_5763428) baseStart_5763428 baseEnd_5763428 := by
    simpa [prefixWord, tailWord_5763428, baseEnd_5763428] using wordTrace_append hprefix tailTrace_5763428
  have hstable : (prefixWord ++ tailWord_5763428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763428).length < 2 ^ (prefixWord ++ tailWord_5763428).sum := by decide
  have hdescent : baseEnd_5763428 < baseStart_5763428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763445 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5763445 : Nat := 118140960795 + 5763445 * 2 ^ 59
def prefixEnd_5763445 : Nat := 4983230072969 + 3 ^ 40 * 5763445 * 2
def baseEnd_5763445 : Nat := 2959417510752308228631905

theorem tailTrace_5763445 : CollatzResearch.WordTrace tailWord_5763445 prefixEnd_5763445 2959417510752308228631905 := by
  unfold tailWord_5763445
  simp only [CollatzResearch.WordTrace]
  refine ⟨210210108605030557885547789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140140072403353705257031859 210210108605030557885547789)
  ·
    refine ⟨78828790726886459207080421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210210108605030557885547789 78828790726886459207080421)
    ·
      refine ⟨14780398261291211101327579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78828790726886459207080421 14780398261291211101327579)
      ·
        refine ⟨22170597391936816651991369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14780398261291211101327579 22170597391936816651991369)
        ·
          refine ⟨16627948043952612488993527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22170597391936816651991369 16627948043952612488993527)
          ·
            refine ⟨24941922065928918733490291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627948043952612488993527 24941922065928918733490291)
            ·
              refine ⟨37412883098893378100235437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24941922065928918733490291 37412883098893378100235437)
              ·
                refine ⟨14029831162085016787588289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37412883098893378100235437 14029831162085016787588289)
                ·
                  refine ⟨10522373371563762590691217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14029831162085016787588289 10522373371563762590691217)
                  ·
                    refine ⟨7891780028672821943018413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10522373371563762590691217 7891780028672821943018413)
                    ·
                      refine ⟨2959417510752308228631905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7891780028672821943018413 2959417510752308228631905)
                      ·
                        rfl

theorem cell23_5763445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5763445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763445 prefixEnd_5763445 := by exact prefixLift 5763445
  have htrace : WordTrace (prefixWord ++ tailWord_5763445) baseStart_5763445 baseEnd_5763445 := by
    simpa [prefixWord, tailWord_5763445, baseEnd_5763445] using wordTrace_append hprefix tailTrace_5763445
  have hstable : (prefixWord ++ tailWord_5763445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763445).length < 2 ^ (prefixWord ++ tailWord_5763445).sum := by decide
  have hdescent : baseEnd_5763445 < baseStart_5763445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_5763531 : Nat := 118140960795 + 5763531 * 2 ^ 59
def prefixEnd_5763531 : Nat := 4983230072969 + 3 ^ 40 * 5763531 * 2
def baseEnd_5763531 : Nat := 2959461670088594892156509

theorem tailTrace_5763531 : CollatzResearch.WordTrace tailWord_5763531 prefixEnd_5763531 2959461670088594892156509 := by
  unfold tailWord_5763531
  simp only [CollatzResearch.WordTrace]
  refine ⟨210213245282718994573178447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140142163521812663048785631 210213245282718994573178447)
  ·
    refine ⟨315319867924078491859767671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210213245282718994573178447 315319867924078491859767671)
    ·
      refine ⟨472979801886117737789651507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315319867924078491859767671 472979801886117737789651507)
      ·
        refine ⟨709469702829176606684477261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472979801886117737789651507 709469702829176606684477261)
        ·
          refine ⟨266051138560941227506678973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 709469702829176606684477261 266051138560941227506678973)
          ·
            refine ⟨99769176960352960315004615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266051138560941227506678973 99769176960352960315004615)
            ·
              refine ⟨149653765440529440472506923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99769176960352960315004615 149653765440529440472506923)
              ·
                refine ⟨224480648160794160708760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149653765440529440472506923 224480648160794160708760385)
                ·
                  refine ⟨168360486120595620531570289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224480648160794160708760385 168360486120595620531570289)
                  ·
                    refine ⟨126270364590446715398677717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168360486120595620531570289 126270364590446715398677717)
                    ·
                      refine ⟨2959461670088594892156509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126270364590446715398677717 2959461670088594892156509)
                      ·
                        rfl

theorem cell23_5763531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_5763531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763531 prefixEnd_5763531 := by exact prefixLift 5763531
  have htrace : WordTrace (prefixWord ++ tailWord_5763531) baseStart_5763531 baseEnd_5763531 := by
    simpa [prefixWord, tailWord_5763531, baseEnd_5763531] using wordTrace_append hprefix tailTrace_5763531
  have hstable : (prefixWord ++ tailWord_5763531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763531).length < 2 ^ (prefixWord ++ tailWord_5763531).sum := by decide
  have hdescent : baseEnd_5763531 < baseStart_5763531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763566 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_5763566 : Nat := 118140960795 + 5763566 * 2 ^ 59
def prefixEnd_5763566 : Nat := 4983230072969 + 3 ^ 40 * 5763566 * 2
def baseEnd_5763566 : Nat := 2959479641911502255218849

theorem tailTrace_5763566 : CollatzResearch.WordTrace tailWord_5763566 prefixEnd_5763566 2959479641911502255218849 := by
  unfold tailWord_5763566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26276815229699024443837819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140143014558394797033801701 26276815229699024443837819)
  ·
    refine ⟨39415222844548536665756729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26276815229699024443837819 39415222844548536665756729)
    ·
      refine ⟨29561417133411402499317547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39415222844548536665756729 29561417133411402499317547)
      ·
        refine ⟨44342125700117103748976321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29561417133411402499317547 44342125700117103748976321)
        ·
          refine ⟨33256594275087827811732241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44342125700117103748976321 33256594275087827811732241)
          ·
            refine ⟨24942445706315870858799181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33256594275087827811732241 24942445706315870858799181)
            ·
              refine ⟨9353417139868451572049693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24942445706315870858799181 9353417139868451572049693)
              ·
                refine ⟨3507531427450669339518635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9353417139868451572049693 3507531427450669339518635)
                ·
                  refine ⟨5261297141176004009277953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507531427450669339518635 5261297141176004009277953)
                  ·
                    refine ⟨3945972855882003006958465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261297141176004009277953 3945972855882003006958465)
                    ·
                      refine ⟨2959479641911502255218849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3945972855882003006958465 2959479641911502255218849)
                      ·
                        rfl

theorem cell23_5763566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_5763566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763566 prefixEnd_5763566 := by exact prefixLift 5763566
  have htrace : WordTrace (prefixWord ++ tailWord_5763566) baseStart_5763566 baseEnd_5763566 := by
    simpa [prefixWord, tailWord_5763566, baseEnd_5763566] using wordTrace_append hprefix tailTrace_5763566
  have hstable : (prefixWord ++ tailWord_5763566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763566).length < 2 ^ (prefixWord ++ tailWord_5763566).sum := by decide
  have hdescent : baseEnd_5763566 < baseStart_5763566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763626 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5763626 : Nat := 118140960795 + 5763626 * 2 ^ 59
def prefixEnd_5763626 : Nat := 4983230072969 + 3 ^ 40 * 5763626 * 2
def baseEnd_5763626 : Nat := 2959510450750772020468573

theorem tailTrace_5763626 : CollatzResearch.WordTrace tailWord_5763626 prefixEnd_5763626 2959510450750772020468573 := by
  unfold tailWord_5763626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52554177554343706449471683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140144473478249883865257821 52554177554343706449471683)
  ·
    refine ⟨78831266331515559674207525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52554177554343706449471683 78831266331515559674207525)
    ·
      refine ⟨14780862437159167438913911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78831266331515559674207525 14780862437159167438913911)
      ·
        refine ⟨22171293655738751158370867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14780862437159167438913911 22171293655738751158370867)
        ·
          refine ⟨33256940483608126737556301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22171293655738751158370867 33256940483608126737556301)
          ·
            refine ⟨12471352681353047526583613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33256940483608126737556301 12471352681353047526583613)
            ·
              refine ⟨4676757255507392822468855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12471352681353047526583613 4676757255507392822468855)
              ·
                refine ⟨7015135883261089233703283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676757255507392822468855 7015135883261089233703283)
                ·
                  refine ⟨10522703824891633850554925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015135883261089233703283 10522703824891633850554925)
                  ·
                    refine ⟨3946013934334362693958097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10522703824891633850554925 3946013934334362693958097)
                    ·
                      refine ⟨2959510450750772020468573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946013934334362693958097 2959510450750772020468573)
                      ·
                        rfl

theorem cell23_5763626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5763626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763626 prefixEnd_5763626 := by exact prefixLift 5763626
  have htrace : WordTrace (prefixWord ++ tailWord_5763626) baseStart_5763626 baseEnd_5763626 := by
    simpa [prefixWord, tailWord_5763626, baseEnd_5763626] using wordTrace_append hprefix tailTrace_5763626
  have hstable : (prefixWord ++ tailWord_5763626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763626).length < 2 ^ (prefixWord ++ tailWord_5763626).sum := by decide
  have hdescent : baseEnd_5763626 < baseStart_5763626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763639 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_5763639 : Nat := 118140960795 + 5763639 * 2 ^ 59
def prefixEnd_5763639 : Nat := 4983230072969 + 3 ^ 40 * 5763639 * 2
def baseEnd_5763639 : Nat := 2959517125999280469606013

theorem tailTrace_5763639 : CollatzResearch.WordTrace tailWord_5763639 prefixEnd_5763639 2959517125999280469606013 := by
  unfold tailWord_5763639
  simp only [CollatzResearch.WordTrace]
  refine ⟨210217184366327729018109971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140144789577551819345406647 210217184366327729018109971)
  ·
    refine ⟨315325776549491593527164957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210217184366327729018109971 315325776549491593527164957)
    ·
      refine ⟨118247166206059347572686859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315325776549491593527164957 118247166206059347572686859)
      ·
        refine ⟨177370749309089021359030289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118247166206059347572686859 177370749309089021359030289)
        ·
          refine ⟨133028061981816766019272717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177370749309089021359030289 133028061981816766019272717)
          ·
            refine ⟨49885523243181287257227269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133028061981816766019272717 49885523243181287257227269)
            ·
              refine ⟨9353535608096491360730113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49885523243181287257227269 9353535608096491360730113)
              ·
                refine ⟨7015151706072368520547585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9353535608096491360730113 7015151706072368520547585)
                ·
                  refine ⟨5261363779554276390410689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7015151706072368520547585 5261363779554276390410689)
                  ·
                    refine ⟨3946022834665707292808017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261363779554276390410689 3946022834665707292808017)
                    ·
                      refine ⟨2959517125999280469606013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946022834665707292808017 2959517125999280469606013)
                      ·
                        rfl

theorem cell23_5763639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_5763639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763639 prefixEnd_5763639 := by exact prefixLift 5763639
  have htrace : WordTrace (prefixWord ++ tailWord_5763639) baseStart_5763639 baseEnd_5763639 := by
    simpa [prefixWord, tailWord_5763639, baseEnd_5763639] using wordTrace_append hprefix tailTrace_5763639
  have hstable : (prefixWord ++ tailWord_5763639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763639).length < 2 ^ (prefixWord ++ tailWord_5763639).sum := by decide
  have hdescent : baseEnd_5763639 < baseStart_5763639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763655 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_5763655 : Nat := 118140960795 + 5763655 * 2 ^ 59
def prefixEnd_5763655 : Nat := 4983230072969 + 3 ^ 40 * 5763655 * 2
def baseEnd_5763655 : Nat := 2959525341689752407005939

theorem tailTrace_5763655 : CollatzResearch.WordTrace tailWord_5763655 prefixEnd_5763655 2959525341689752407005939 := by
  unfold tailWord_5763655
  simp only [CollatzResearch.WordTrace]
  refine ⟨210217767934269763750692419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140145178622846509167128279 210217767934269763750692419)
  ·
    refine ⟨315326651901404645626038629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210217767934269763750692419 315326651901404645626038629)
    ·
      refine ⟨59123747231513371054882243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315326651901404645626038629 59123747231513371054882243)
      ·
        refine ⟨88685620847270056582323365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59123747231513371054882243 88685620847270056582323365)
        ·
          refine ⟨16628553908863135609185631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88685620847270056582323365 16628553908863135609185631)
          ·
            refine ⟨24942830863294703413778447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16628553908863135609185631 24942830863294703413778447)
            ·
              refine ⟨37414246294942055120667671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24942830863294703413778447 37414246294942055120667671)
              ·
                refine ⟨56121369442413082681001507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37414246294942055120667671 56121369442413082681001507)
                ·
                  refine ⟨84182054163619624021502261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56121369442413082681001507 84182054163619624021502261)
                  ·
                    refine ⟨7892067577839339752015837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84182054163619624021502261 7892067577839339752015837)
                    ·
                      refine ⟨2959525341689752407005939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892067577839339752015837 2959525341689752407005939)
                      ·
                        rfl

theorem cell23_5763655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_5763655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763655 prefixEnd_5763655 := by exact prefixLift 5763655
  have htrace : WordTrace (prefixWord ++ tailWord_5763655) baseStart_5763655 baseEnd_5763655 := by
    simpa [prefixWord, tailWord_5763655, baseEnd_5763655] using wordTrace_append hprefix tailTrace_5763655
  have hstable : (prefixWord ++ tailWord_5763655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763655).length < 2 ^ (prefixWord ++ tailWord_5763655).sum := by decide
  have hdescent : baseEnd_5763655 < baseStart_5763655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763695 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_5763695 : Nat := 118140960795 + 5763695 * 2 ^ 59
def prefixEnd_5763695 : Nat := 4983230072969 + 3 ^ 40 * 5763695 * 2
def baseEnd_5763695 : Nat := 2959545880915932250505755

theorem tailTrace_5763695 : CollatzResearch.WordTrace tailWord_5763695 prefixEnd_5763695 2959545880915932250505755 := by
  unfold tailWord_5763695
  simp only [CollatzResearch.WordTrace]
  refine ⟨210219226854124850582148539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140146151236083233721432359 210219226854124850582148539)
  ·
    refine ⟨315328840281187275873222809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210219226854124850582148539 315328840281187275873222809)
    ·
      refine ⟨236496630210890456904917107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315328840281187275873222809 236496630210890456904917107)
      ·
        refine ⟨354744945316335685357375661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236496630210890456904917107 354744945316335685357375661)
        ·
          refine ⟨133029354493625882009015873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354744945316335685357375661 133029354493625882009015873)
          ·
            refine ⟨99772015870219411506761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133029354493625882009015873 99772015870219411506761905)
            ·
              refine ⟨74829011902664558630071429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99772015870219411506761905 74829011902664558630071429)
              ·
                refine ⟨14030439731749604743138393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74829011902664558630071429 14030439731749604743138393)
                ·
                  refine ⟨10522829798812203557353795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14030439731749604743138393 10522829798812203557353795)
                  ·
                    refine ⟨15784244698218305336030693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10522829798812203557353795 15784244698218305336030693)
                    ·
                      refine ⟨2959545880915932250505755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15784244698218305336030693 2959545880915932250505755)
                      ·
                        rfl

theorem cell23_5763695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_5763695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763695 prefixEnd_5763695 := by exact prefixLift 5763695
  have htrace : WordTrace (prefixWord ++ tailWord_5763695) baseStart_5763695 baseEnd_5763695 := by
    simpa [prefixWord, tailWord_5763695, baseEnd_5763695] using wordTrace_append hprefix tailTrace_5763695
  have hstable : (prefixWord ++ tailWord_5763695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763695).length < 2 ^ (prefixWord ++ tailWord_5763695).sum := by decide
  have hdescent : baseEnd_5763695 < baseStart_5763695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763712 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2]
def baseStart_5763712 : Nat := 118140960795 + 5763712 * 2 ^ 59
def prefixEnd_5763712 : Nat := 4983230072969 + 3 ^ 40 * 5763712 * 2
def baseEnd_5763712 : Nat := 2959554610087058683993177

theorem tailTrace_5763712 : CollatzResearch.WordTrace tailWord_5763712 prefixEnd_5763712 2959554610087058683993177 := by
  unfold tailWord_5763712
  simp only [CollatzResearch.WordTrace]
  refine ⟨105109923447531631242758695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140146564596708841657011593 105109923447531631242758695)
  ·
    refine ⟨157664885171297446864138043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105109923447531631242758695 157664885171297446864138043)
    ·
      refine ⟨236497327756946170296207065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157664885171297446864138043 236497327756946170296207065)
      ·
        refine ⟨177372995817709627722155299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236497327756946170296207065 177372995817709627722155299)
        ·
          refine ⟨266059493726564441583232949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177372995817709627722155299 266059493726564441583232949)
          ·
            refine ⟨24943077536865416398428089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 266059493726564441583232949 24943077536865416398428089)
            ·
              refine ⟨18707308152649062298821067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24943077536865416398428089 18707308152649062298821067)
              ·
                refine ⟨28060962228973593448231601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18707308152649062298821067 28060962228973593448231601)
                ·
                  refine ⟨21045721671730195086173701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28060962228973593448231601 21045721671730195086173701)
                  ·
                    refine ⟨3946072813449411578657569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21045721671730195086173701 3946072813449411578657569)
                    ·
                      refine ⟨2959554610087058683993177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946072813449411578657569 2959554610087058683993177)
                      ·
                        rfl

theorem cell23_5763712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_5763712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763712 prefixEnd_5763712 := by exact prefixLift 5763712
  have htrace : WordTrace (prefixWord ++ tailWord_5763712) baseStart_5763712 baseEnd_5763712 := by
    simpa [prefixWord, tailWord_5763712, baseEnd_5763712] using wordTrace_append hprefix tailTrace_5763712
  have hstable : (prefixWord ++ tailWord_5763712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763712).length < 2 ^ (prefixWord ++ tailWord_5763712).sum := by decide
  have hdescent : baseEnd_5763712 < baseStart_5763712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763715 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3]
def baseStart_5763715 : Nat := 118140960795 + 5763715 * 2 ^ 59
def prefixEnd_5763715 : Nat := 4983230072969 + 3 ^ 40 * 5763715 * 2
def baseEnd_5763715 : Nat := 2959556150529022172255663

theorem tailTrace_5763715 : CollatzResearch.WordTrace tailWord_5763715 prefixEnd_5763715 2959556150529022172255663 := by
  unfold tailWord_5763715
  simp only [CollatzResearch.WordTrace]
  refine ⟨210219956314052393997876599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140146637542701595998584399 210219956314052393997876599)
  ·
    refine ⟨315329934471078590996814899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210219956314052393997876599 315329934471078590996814899)
    ·
      refine ⟨472994901706617886495222349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315329934471078590996814899 472994901706617886495222349)
      ·
        refine ⟨177373088139981707435708381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 472994901706617886495222349 177373088139981707435708381)
        ·
          refine ⟨66514908052493140288390643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177373088139981707435708381 66514908052493140288390643)
          ·
            refine ⟨99772362078739710432585965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66514908052493140288390643 99772362078739710432585965)
            ·
              refine ⟨37414635779527391412219737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99772362078739710432585965 37414635779527391412219737)
              ·
                refine ⟨28060976834645543559164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37414635779527391412219737 28060976834645543559164803)
                ·
                  refine ⟨42091465251968315338747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28060976834645543559164803 42091465251968315338747205)
                  ·
                    refine ⟨7892149734744059126015101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42091465251968315338747205 7892149734744059126015101)
                    ·
                      refine ⟨2959556150529022172255663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892149734744059126015101 2959556150529022172255663)
                      ·
                        rfl

theorem cell23_5763715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_5763715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763715 prefixEnd_5763715 := by exact prefixLift 5763715
  have htrace : WordTrace (prefixWord ++ tailWord_5763715) baseStart_5763715 baseEnd_5763715 := by
    simpa [prefixWord, tailWord_5763715, baseEnd_5763715] using wordTrace_append hprefix tailTrace_5763715
  have hstable : (prefixWord ++ tailWord_5763715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763715).length < 2 ^ (prefixWord ++ tailWord_5763715).sum := by decide
  have hdescent : baseEnd_5763715 < baseStart_5763715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763728 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_5763728 : Nat := 118140960795 + 5763728 * 2 ^ 59
def prefixEnd_5763728 : Nat := 4983230072969 + 3 ^ 40 * 5763728 * 2
def baseEnd_5763728 : Nat := 2959562825777530621393103

theorem tailTrace_5763728 : CollatzResearch.WordTrace tailWord_5763728 prefixEnd_5763728 2959562825777530621393103 := by
  unfold tailWord_5763728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105110215231502648609049919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140146953642003531478733225 105110215231502648609049919)
  ·
    refine ⟨157665322847253972913574879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105110215231502648609049919 157665322847253972913574879)
    ·
      refine ⟨236497984270880959370362319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157665322847253972913574879 236497984270880959370362319)
      ·
        refine ⟨354746976406321439055543479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236497984270880959370362319 354746976406321439055543479)
        ·
          refine ⟨532120464609482158583315219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354746976406321439055543479 532120464609482158583315219)
          ·
            refine ⟨798180696914223237874972829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532120464609482158583315219 798180696914223237874972829)
            ·
              refine ⟨299317761342833714203114811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798180696914223237874972829 299317761342833714203114811)
              ·
                refine ⟨448976642014250571304672217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299317761342833714203114811 448976642014250571304672217)
                ·
                  refine ⟨336732481510687928478504163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448976642014250571304672217 336732481510687928478504163)
                  ·
                    refine ⟨505098722266031892717756245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336732481510687928478504163 505098722266031892717756245)
                    ·
                      refine ⟨2959562825777530621393103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 505098722266031892717756245 2959562825777530621393103)
                      ·
                        rfl

theorem cell23_5763728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_5763728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763728 prefixEnd_5763728 := by exact prefixLift 5763728
  have htrace : WordTrace (prefixWord ++ tailWord_5763728) baseStart_5763728 baseEnd_5763728 := by
    simpa [prefixWord, tailWord_5763728, baseEnd_5763728] using wordTrace_append hprefix tailTrace_5763728
  have hstable : (prefixWord ++ tailWord_5763728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763728).length < 2 ^ (prefixWord ++ tailWord_5763728).sum := by decide
  have hdescent : baseEnd_5763728 < baseStart_5763728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763799 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 1, 5]
def baseStart_5763799 : Nat := 118140960795 + 5763799 * 2 ^ 59
def prefixEnd_5763799 : Nat := 4983230072969 + 3 ^ 40 * 5763799 * 2
def baseEnd_5763799 : Nat := 986533094301333281201759

theorem tailTrace_5763799 : CollatzResearch.WordTrace tailWord_5763799 prefixEnd_5763799 986533094301333281201759 := by
  unfold tailWord_5763799
  simp only [CollatzResearch.WordTrace]
  refine ⟨210223020045748076343934451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140148680030498717562622967 210223020045748076343934451)
  ·
    refine ⟨315334530068622114515901677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210223020045748076343934451 315334530068622114515901677)
    ·
      refine ⟨118250448775733292943463129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315334530068622114515901677 118250448775733292943463129)
      ·
        refine ⟨88687836581799969707597347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118250448775733292943463129 88687836581799969707597347)
        ·
          refine ⟨133031754872699954561396021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88687836581799969707597347 133031754872699954561396021)
          ·
            refine ⟨12471727019315620740130877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133031754872699954561396021 12471727019315620740130877)
            ·
              refine ⟨4676897632243357777549079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12471727019315620740130877 4676897632243357777549079)
              ·
                refine ⟨7015346448365036666323619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676897632243357777549079 7015346448365036666323619)
                ·
                  refine ⟨10523019672547554999485429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015346448365036666323619 10523019672547554999485429)
                  ·
                    refine ⟨986533094301333281201759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10523019672547554999485429 986533094301333281201759)
                    ·
                      rfl

theorem cell23_5763799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_5763799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763799 prefixEnd_5763799 := by exact prefixLift 5763799
  have htrace : WordTrace (prefixWord ++ tailWord_5763799) baseStart_5763799 baseEnd_5763799 := by
    simpa [prefixWord, tailWord_5763799, baseEnd_5763799] using wordTrace_append hprefix tailTrace_5763799
  have hstable : (prefixWord ++ tailWord_5763799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763799).length < 2 ^ (prefixWord ++ tailWord_5763799).sum := by decide
  have hdescent : baseEnd_5763799 < baseStart_5763799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763813 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5763813 : Nat := 118140960795 + 5763813 * 2 ^ 59
def prefixEnd_5763813 : Nat := 4983230072969 + 3 ^ 40 * 5763813 * 2
def baseEnd_5763813 : Nat := 2959606471633162788830213

theorem tailTrace_5763813 : CollatzResearch.WordTrace tailWord_5763813 prefixEnd_5763813 2959606471633162788830213 := by
  unfold tailWord_5763813
  simp only [CollatzResearch.WordTrace]
  refine ⟨210223530667697356734944093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140149020445131571156629395 210223530667697356734944093)
  ·
    refine ⟨78833824000386508775604035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210223530667697356734944093 78833824000386508775604035)
    ·
      refine ⟨118250736000579763163406053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78833824000386508775604035 118250736000579763163406053)
      ·
        refine ⟨22172013000108705593138635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118250736000579763163406053 22172013000108705593138635)
        ·
          refine ⟨33258019500163058389707953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22172013000108705593138635 33258019500163058389707953)
          ·
            refine ⟨24943514625122293792280965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33258019500163058389707953 24943514625122293792280965)
            ·
              refine ⟨4676908992210430086052681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24943514625122293792280965 4676908992210430086052681)
              ·
                refine ⟨3507681744157822564539511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676908992210430086052681 3507681744157822564539511)
                ·
                  refine ⟨5261522616236733846809267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507681744157822564539511 5261522616236733846809267)
                  ·
                    refine ⟨7892283924355100770213901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5261522616236733846809267 7892283924355100770213901)
                    ·
                      refine ⟨2959606471633162788830213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892283924355100770213901 2959606471633162788830213)
                      ·
                        rfl

theorem cell23_5763813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5763813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763813 prefixEnd_5763813 := by exact prefixLift 5763813
  have htrace : WordTrace (prefixWord ++ tailWord_5763813) baseStart_5763813 baseEnd_5763813 := by
    simpa [prefixWord, tailWord_5763813, baseEnd_5763813] using wordTrace_append hprefix tailTrace_5763813
  have hstable : (prefixWord ++ tailWord_5763813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763813).length < 2 ^ (prefixWord ++ tailWord_5763813).sum := by decide
  have hdescent : baseEnd_5763813 < baseStart_5763813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763819 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 3, 2, 2]
def baseStart_5763819 : Nat := 118140960795 + 5763819 * 2 ^ 59
def prefixEnd_5763819 : Nat := 4983230072969 + 3 ^ 40 * 5763819 * 2
def baseEnd_5763819 : Nat := 2959609552517089765355185

theorem tailTrace_5763819 : CollatzResearch.WordTrace tailWord_5763819 prefixEnd_5763819 2959609552517089765355185 := by
  unfold tailWord_5763819
  simp only [CollatzResearch.WordTrace]
  refine ⟨210223749505675619759662511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140149166337117079839775007 210223749505675619759662511)
  ·
    refine ⟨315335624258513429639493767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210223749505675619759662511 315335624258513429639493767)
    ·
      refine ⟨473003436387770144459240651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315335624258513429639493767 473003436387770144459240651)
      ·
        refine ⟨709505154581655216688860977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473003436387770144459240651 709505154581655216688860977)
        ·
          refine ⟨532128865936241412516645733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709505154581655216688860977 532128865936241412516645733)
          ·
            refine ⟨99774162363045264846871075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532128865936241412516645733 99774162363045264846871075)
            ·
              refine ⟨149661243544567897270306613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99774162363045264846871075 149661243544567897270306613)
              ·
                refine ⟨14030741582303240369091245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149661243544567897270306613 14030741582303240369091245)
                ·
                  refine ⟨5261528093363715138409217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14030741582303240369091245 5261528093363715138409217)
                  ·
                    refine ⟨3946146070022786353806913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261528093363715138409217 3946146070022786353806913)
                    ·
                      refine ⟨2959609552517089765355185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946146070022786353806913 2959609552517089765355185)
                      ·
                        rfl

theorem cell23_5763819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 2, 2].length) (baseStart_5763819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763819 prefixEnd_5763819 := by exact prefixLift 5763819
  have htrace : WordTrace (prefixWord ++ tailWord_5763819) baseStart_5763819 baseEnd_5763819 := by
    simpa [prefixWord, tailWord_5763819, baseEnd_5763819] using wordTrace_append hprefix tailTrace_5763819
  have hstable : (prefixWord ++ tailWord_5763819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763819).length < 2 ^ (prefixWord ++ tailWord_5763819).sum := by decide
  have hdescent : baseEnd_5763819 < baseStart_5763819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763832 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_5763832 : Nat := 118140960795 + 5763832 * 2 ^ 59
def prefixEnd_5763832 : Nat := 4983230072969 + 3 ^ 40 * 5763832 * 2
def baseEnd_5763832 : Nat := 2959616227765598214492625

theorem tailTrace_5763832 : CollatzResearch.WordTrace tailWord_5763832 prefixEnd_5763832 2959616227765598214492625 := by
  unfold tailWord_5763832
  simp only [CollatzResearch.WordTrace]
  refine ⟨105112111827314261489942875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140149482436419015319923833 105112111827314261489942875)
  ·
    refine ⟨157668167740971392234914313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105112111827314261489942875 157668167740971392234914313)
    ·
      refine ⟨118251125805728544176185735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157668167740971392234914313 118251125805728544176185735)
      ·
        refine ⟨177376688708592816264278603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118251125805728544176185735 177376688708592816264278603)
        ·
          refine ⟨266065033062889224396417905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177376688708592816264278603 266065033062889224396417905)
          ·
            refine ⟨199548774797166918297313429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266065033062889224396417905 199548774797166918297313429)
            ·
              refine ⟨9353848818617199295186567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199548774797166918297313429 9353848818617199295186567)
              ·
                refine ⟨14030773227925798942779851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9353848818617199295186567 14030773227925798942779851)
                ·
                  refine ⟨21046159841888698414169777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14030773227925798942779851 21046159841888698414169777)
                  ·
                    refine ⟨15784619881416523810627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21046159841888698414169777 15784619881416523810627333)
                    ·
                      refine ⟨2959616227765598214492625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15784619881416523810627333 2959616227765598214492625)
                      ·
                        rfl

theorem cell23_5763832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_5763832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763832 prefixEnd_5763832 := by exact prefixLift 5763832
  have htrace : WordTrace (prefixWord ++ tailWord_5763832) baseStart_5763832 baseEnd_5763832 := by
    simpa [prefixWord, tailWord_5763832, baseEnd_5763832] using wordTrace_append hprefix tailTrace_5763832
  have hstable : (prefixWord ++ tailWord_5763832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763832).length < 2 ^ (prefixWord ++ tailWord_5763832).sum := by decide
  have hdescent : baseEnd_5763832 < baseStart_5763832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763836 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_5763836 : Nat := 118140960795 + 5763836 * 2 ^ 59
def prefixEnd_5763836 : Nat := 4983230072969 + 3 ^ 40 * 5763836 * 2
def baseEnd_5763836 : Nat := 2959618281688216198842607

theorem tailTrace_5763836 : CollatzResearch.WordTrace tailWord_5763836 prefixEnd_5763836 2959618281688216198842607 := by
  unfold tailWord_5763836
  simp only [CollatzResearch.WordTrace]
  refine ⟨105112184773307015831515681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140149579697742687775354241 105112184773307015831515681)
  ·
    refine ⟨78834138579980261873636761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105112184773307015831515681 78834138579980261873636761)
    ·
      refine ⟨59125603934985196405227571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78834138579980261873636761 59125603934985196405227571)
      ·
        refine ⟨88688405902477794607841357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59125603934985196405227571 88688405902477794607841357)
        ·
          refine ⟨33258152213429172977940509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88688405902477794607841357 33258152213429172977940509)
          ·
            refine ⟨12471807080035939866727691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33258152213429172977940509 12471807080035939866727691)
            ·
              refine ⟨18707710620053909800091537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12471807080035939866727691 18707710620053909800091537)
              ·
                refine ⟨14030782965040432350068653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18707710620053909800091537 14030782965040432350068653)
                ·
                  refine ⟨5261543611890162131275745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14030782965040432350068653 5261543611890162131275745)
                  ·
                    refine ⟨3946157708917621598456809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261543611890162131275745 3946157708917621598456809)
                    ·
                      refine ⟨2959618281688216198842607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946157708917621598456809 2959618281688216198842607)
                      ·
                        rfl

theorem cell23_5763836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_5763836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763836 prefixEnd_5763836 := by exact prefixLift 5763836
  have htrace : WordTrace (prefixWord ++ tailWord_5763836) baseStart_5763836 baseEnd_5763836 := by
    simpa [prefixWord, tailWord_5763836, baseEnd_5763836] using wordTrace_append hprefix tailTrace_5763836
  have hstable : (prefixWord ++ tailWord_5763836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763836).length < 2 ^ (prefixWord ++ tailWord_5763836).sum := by decide
  have hdescent : baseEnd_5763836 < baseStart_5763836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763863 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 2, 4]
def baseStart_5763863 : Nat := 118140960795 + 5763863 * 2 ^ 59
def prefixEnd_5763863 : Nat := 4983230072969 + 3 ^ 40 * 5763863 * 2
def baseEnd_5763863 : Nat := 986544048555295864401661

theorem tailTrace_5763863 : CollatzResearch.WordTrace tailWord_5763863 prefixEnd_5763863 986544048555295864401661 := by
  unfold tailWord_5763863
  simp only [CollatzResearch.WordTrace]
  refine ⟨210225354317516215274264243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140150236211677476849509495 210225354317516215274264243)
  ·
    refine ⟨315338031476274322911396365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210225354317516215274264243 315338031476274322911396365)
    ·
      refine ⟨118251761803602871091773637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315338031476274322911396365 118251761803602871091773637)
      ·
        refine ⟨22172205338175538329707557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118251761803602871091773637 22172205338175538329707557)
        ·
          refine ⟨4157288500907913436820167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22172205338175538329707557 4157288500907913436820167)
          ·
            refine ⟨6235932751361870155230251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157288500907913436820167 6235932751361870155230251)
            ·
              refine ⟨9353899127042805232845377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6235932751361870155230251 9353899127042805232845377)
              ·
                refine ⟨7015424345282103924634033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9353899127042805232845377 7015424345282103924634033)
                ·
                  refine ⟨5261568258961577943475525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7015424345282103924634033 5261568258961577943475525)
                  ·
                    refine ⟨986544048555295864401661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261568258961577943475525 986544048555295864401661)
                    ·
                      rfl

theorem cell23_5763863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_5763863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763863 prefixEnd_5763863 := by exact prefixLift 5763863
  have htrace : WordTrace (prefixWord ++ tailWord_5763863) baseStart_5763863 baseEnd_5763863 := by
    simpa [prefixWord, tailWord_5763863, baseEnd_5763863] using wordTrace_append hprefix tailTrace_5763863
  have hstable : (prefixWord ++ tailWord_5763863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763863).length < 2 ^ (prefixWord ++ tailWord_5763863).sum := by decide
  have hdescent : baseEnd_5763863 < baseStart_5763863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763865 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5763865 : Nat := 118140960795 + 5763865 * 2 ^ 59
def prefixEnd_5763865 : Nat := 4983230072969 + 3 ^ 40 * 5763865 * 2
def baseEnd_5763865 : Nat := 2959633172627196585379973

theorem tailTrace_5763865 : CollatzResearch.WordTrace tailWord_5763865 prefixEnd_5763865 2959633172627196585379973 := by
  unfold tailWord_5763865
  simp only [CollatzResearch.WordTrace]
  refine ⟨210225427263508969615837049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140150284842339313077224699 210225427263508969615837049)
  ·
    refine ⟨157669070447631727211877787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210225427263508969615837049 157669070447631727211877787)
    ·
      refine ⟨236503605671447590817816681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157669070447631727211877787 236503605671447590817816681)
      ·
        refine ⟨177377704253585693113362511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236503605671447590817816681 177377704253585693113362511)
        ·
          refine ⟨266066556380378539670043767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177377704253585693113362511 266066556380378539670043767)
          ·
            refine ⟨399099834570567809505065651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266066556380378539670043767 399099834570567809505065651)
            ·
              refine ⟨598649751855851714257598477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399099834570567809505065651 598649751855851714257598477)
              ·
                refine ⟨224493656945944392846599429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 598649751855851714257598477 224493656945944392846599429)
                ·
                  refine ⟨42092560677364573658737393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 224493656945944392846599429 42092560677364573658737393)
                  ·
                    refine ⟨31569420508023430244053045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42092560677364573658737393 31569420508023430244053045)
                    ·
                      refine ⟨2959633172627196585379973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31569420508023430244053045 2959633172627196585379973)
                      ·
                        rfl

theorem cell23_5763865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5763865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763865 prefixEnd_5763865 := by exact prefixLift 5763865
  have htrace : WordTrace (prefixWord ++ tailWord_5763865) baseStart_5763865 baseEnd_5763865 := by
    simpa [prefixWord, tailWord_5763865, baseEnd_5763865] using wordTrace_append hprefix tailTrace_5763865
  have hstable : (prefixWord ++ tailWord_5763865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763865).length < 2 ^ (prefixWord ++ tailWord_5763865).sum := by decide
  have hdescent : baseEnd_5763865 < baseStart_5763865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763886 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5763886 : Nat := 118140960795 + 5763886 * 2 ^ 59
def prefixEnd_5763886 : Nat := 4983230072969 + 3 ^ 40 * 5763886 * 2
def baseEnd_5763886 : Nat := 2959643955720941003217377

theorem tailTrace_5763886 : CollatzResearch.WordTrace tailWord_5763886 prefixEnd_5763886 2959643955720941003217377 := by
  unfold tailWord_5763886
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278274149554111275293939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140150795464288593468234341 26278274149554111275293939)
  ·
    refine ⟨39417411224331166912940909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26278274149554111275293939 39417411224331166912940909)
    ·
      refine ⟨14781529209124187592352841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39417411224331166912940909 14781529209124187592352841)
      ·
        refine ⟨11086146906843140694264631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14781529209124187592352841 11086146906843140694264631)
        ·
          refine ⟨16629220360264711041396947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11086146906843140694264631 16629220360264711041396947)
          ·
            refine ⟨24943830540397066562095421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16629220360264711041396947 24943830540397066562095421)
            ·
              refine ⟨9353936452648899960785783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24943830540397066562095421 9353936452648899960785783)
              ·
                refine ⟨14030904678973349941178675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9353936452648899960785783 14030904678973349941178675)
                ·
                  refine ⟨21046357018460024911768013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14030904678973349941178675 21046357018460024911768013)
                  ·
                    refine ⟨7892383881922509341913005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21046357018460024911768013 7892383881922509341913005)
                    ·
                      refine ⟨2959643955720941003217377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892383881922509341913005 2959643955720941003217377)
                      ·
                        rfl

theorem cell23_5763886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5763886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763886 prefixEnd_5763886 := by exact prefixLift 5763886
  have htrace : WordTrace (prefixWord ++ tailWord_5763886) baseStart_5763886 baseEnd_5763886 := by
    simpa [prefixWord, tailWord_5763886, baseEnd_5763886] using wordTrace_append hprefix tailTrace_5763886
  have hstable : (prefixWord ++ tailWord_5763886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763886).length < 2 ^ (prefixWord ++ tailWord_5763886).sum := by decide
  have hdescent : baseEnd_5763886 < baseStart_5763886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763896 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_5763896 : Nat := 118140960795 + 5763896 * 2 ^ 59
def prefixEnd_5763896 : Nat := 4983230072969 + 3 ^ 40 * 5763896 * 2
def baseEnd_5763896 : Nat := 2959649090527485964092331

theorem tailTrace_5763896 : CollatzResearch.WordTrace tailWord_5763896 prefixEnd_5763896 2959649090527485964092331 := by
  unfold tailWord_5763896
  simp only [CollatzResearch.WordTrace]
  refine ⟨105113278963198330955107771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140151038617597774606810361 105113278963198330955107771)
  ·
    refine ⟨157669918444797496432661657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105113278963198330955107771 157669918444797496432661657)
    ·
      refine ⟨118252438833598122324496243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157669918444797496432661657 118252438833598122324496243)
      ·
        refine ⟨177378658250397183486744365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118252438833598122324496243 177378658250397183486744365)
        ·
          refine ⟨66516996843898943807529137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177378658250397183486744365 66516996843898943807529137)
          ·
            refine ⟨49887747632924207855646853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66516996843898943807529137 49887747632924207855646853)
            ·
              refine ⟨9353952681173288972933785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49887747632924207855646853 9353952681173288972933785)
              ·
                refine ⟨7015464510879966729700339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9353952681173288972933785 7015464510879966729700339)
                ·
                  refine ⟨10523196766319950094550509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015464510879966729700339 10523196766319950094550509)
                  ·
                    refine ⟨3946198787369981285456441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10523196766319950094550509 3946198787369981285456441)
                    ·
                      refine ⟨2959649090527485964092331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946198787369981285456441 2959649090527485964092331)
                      ·
                        rfl

theorem cell23_5763896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_5763896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763896 prefixEnd_5763896 := by exact prefixLift 5763896
  have htrace : WordTrace (prefixWord ++ tailWord_5763896) baseStart_5763896 baseEnd_5763896 := by
    simpa [prefixWord, tailWord_5763896, baseEnd_5763896] using wordTrace_append hprefix tailTrace_5763896
  have hstable : (prefixWord ++ tailWord_5763896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763896).length < 2 ^ (prefixWord ++ tailWord_5763896).sum := by decide
  have hdescent : baseEnd_5763896 < baseStart_5763896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763912 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_5763912 : Nat := 118140960795 + 5763912 * 2 ^ 59
def prefixEnd_5763912 : Nat := 4983230072969 + 3 ^ 40 * 5763912 * 2
def baseEnd_5763912 : Nat := 2959657306217957901492257

theorem tailTrace_5763912 : CollatzResearch.WordTrace tailWord_5763912 prefixEnd_5763912 2959657306217957901492257 := by
  unfold tailWord_5763912
  simp only [CollatzResearch.WordTrace]
  refine ⟨105113570747169348321398995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140151427662892464428531993 105113570747169348321398995)
  ·
    refine ⟨157670356120754022482098493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105113570747169348321398995 157670356120754022482098493)
    ·
      refine ⟨59126383545282758430786935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157670356120754022482098493 59126383545282758430786935)
      ·
        refine ⟨88689575317924137646180403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59126383545282758430786935 88689575317924137646180403)
        ·
          refine ⟨133034362976886206469270605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88689575317924137646180403 133034362976886206469270605)
          ·
            refine ⟨49887886116332327425976477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133034362976886206469270605 49887886116332327425976477)
            ·
              refine ⟨18707957293624622784741179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49887886116332327425976477 18707957293624622784741179)
              ·
                refine ⟨28061935940436934177111769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18707957293624622784741179 28061935940436934177111769)
                ·
                  refine ⟨21046451955327700632833827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28061935940436934177111769 21046451955327700632833827)
                  ·
                    refine ⟨31569677932991550949250741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21046451955327700632833827 31569677932991550949250741)
                    ·
                      refine ⟨2959657306217957901492257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31569677932991550949250741 2959657306217957901492257)
                      ·
                        rfl

theorem cell23_5763912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_5763912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763912 prefixEnd_5763912 := by exact prefixLift 5763912
  have htrace : WordTrace (prefixWord ++ tailWord_5763912) baseStart_5763912 baseEnd_5763912 := by
    simpa [prefixWord, tailWord_5763912, baseEnd_5763912] using wordTrace_append hprefix tailTrace_5763912
  have hstable : (prefixWord ++ tailWord_5763912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763912).length < 2 ^ (prefixWord ++ tailWord_5763912).sum := by decide
  have hdescent : baseEnd_5763912 < baseStart_5763912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5763943 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_5763943 : Nat := 118140960795 + 5763943 * 2 ^ 59
def prefixEnd_5763943 : Nat := 4983230072969 + 3 ^ 40 * 5763943 * 2
def baseEnd_5763943 : Nat := 2959673224118247280204615

theorem tailTrace_5763943 : CollatzResearch.WordTrace tailWord_5763943 prefixEnd_5763943 2959673224118247280204615 := by
  unfold tailWord_5763943
  simp only [CollatzResearch.WordTrace]
  refine ⟨210228272157226388937176483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140152181438150925958117655 210228272157226388937176483)
  ·
    refine ⟨315342408235839583405764725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210228272157226388937176483 315342408235839583405764725)
    ·
      refine ⟨29563350772109960944290443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315342408235839583405764725 29563350772109960944290443)
      ·
        refine ⟨44345026158164941416435665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29563350772109960944290443 44345026158164941416435665)
        ·
          refine ⟨33258769618623706062326749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44345026158164941416435665 33258769618623706062326749)
          ·
            refine ⟨12472038606983889773372531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33258769618623706062326749 12472038606983889773372531)
            ·
              refine ⟨18708057910475834660058797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12472038606983889773372531 18708057910475834660058797)
              ·
                refine ⟨7015521716428437997522049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18708057910475834660058797 7015521716428437997522049)
                ·
                  refine ⟨5261641287321328498141537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7015521716428437997522049 5261641287321328498141537)
                  ·
                    refine ⟨3946230965490996373606153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261641287321328498141537 3946230965490996373606153)
                    ·
                      refine ⟨2959673224118247280204615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946230965490996373606153 2959673224118247280204615)
                      ·
                        rfl

theorem cell23_5763943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_5763943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5763943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5763943 prefixEnd_5763943 := by exact prefixLift 5763943
  have htrace : WordTrace (prefixWord ++ tailWord_5763943) baseStart_5763943 baseEnd_5763943 := by
    simpa [prefixWord, tailWord_5763943, baseEnd_5763943] using wordTrace_append hprefix tailTrace_5763943
  have hstable : (prefixWord ++ tailWord_5763943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5763943).length < 2 ^ (prefixWord ++ tailWord_5763943).sum := by decide
  have hdescent : baseEnd_5763943 < baseStart_5763943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5763943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764009 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_5764009 : Nat := 118140960795 + 5764009 * 2 ^ 59
def prefixEnd_5764009 : Nat := 4983230072969 + 3 ^ 40 * 5764009 * 2
def baseEnd_5764009 : Nat := 986569037947148007326437

theorem tailTrace_5764009 : CollatzResearch.WordTrace tailWord_5764009 prefixEnd_5764009 986569037947148007326437 := by
  unfold tailWord_5764009
  simp only [CollatzResearch.WordTrace]
  refine ⟨210230679374987282209079081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140153786249991521472719387 210230679374987282209079081)
  ·
    refine ⟨157673009531240461656809311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210230679374987282209079081 157673009531240461656809311)
    ·
      refine ⟨236509514296860692485213967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157673009531240461656809311 236509514296860692485213967)
      ·
        refine ⟨354764271445291038727820951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236509514296860692485213967 354764271445291038727820951)
        ·
          refine ⟨532146407167936558091731427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354764271445291038727820951 532146407167936558091731427)
          ·
            refine ⟨798219610751904837137597141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532146407167936558091731427 798219610751904837137597141)
            ·
              refine ⟨18708272126997769620412433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 798219610751904837137597141 18708272126997769620412433)
              ·
                refine ⟨14031204095248327215309325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18708272126997769620412433 14031204095248327215309325)
                ·
                  refine ⟨5261701535718122705740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14031204095248327215309325 5261701535718122705740997)
                  ·
                    refine ⟨986569037947148007326437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261701535718122705740997 986569037947148007326437)
                    ·
                      rfl

theorem cell23_5764009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_5764009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764009 prefixEnd_5764009 := by exact prefixLift 5764009
  have htrace : WordTrace (prefixWord ++ tailWord_5764009) baseStart_5764009 baseEnd_5764009 := by
    simpa [prefixWord, tailWord_5764009, baseEnd_5764009] using wordTrace_append hprefix tailTrace_5764009
  have hstable : (prefixWord ++ tailWord_5764009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764009).length < 2 ^ (prefixWord ++ tailWord_5764009).sum := by decide
  have hdescent : baseEnd_5764009 < baseStart_5764009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764012 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_5764012 : Nat := 118140960795 + 5764012 * 2 ^ 59
def prefixEnd_5764012 : Nat := 4983230072969 + 3 ^ 40 * 5764012 * 2
def baseEnd_5764012 : Nat := 2959708654283407510241797

theorem tailTrace_5764012 : CollatzResearch.WordTrace tailWord_5764012 prefixEnd_5764012 2959708654283407510241797 := by
  unfold tailWord_5764012
  simp only [CollatzResearch.WordTrace]
  refine ⟨105115394396988206860719145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140153859195984275814292193 105115394396988206860719145)
  ·
    refine ⟨78836545797741155145539359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105115394396988206860719145 78836545797741155145539359)
    ·
      refine ⟨118254818696611732718309039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78836545797741155145539359 118254818696611732718309039)
      ·
        refine ⟨177382228044917599077463559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118254818696611732718309039 177382228044917599077463559)
        ·
          refine ⟨266073342067376398616195339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177382228044917599077463559 266073342067376398616195339)
          ·
            refine ⟨399110013101064597924293009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266073342067376398616195339 399110013101064597924293009)
            ·
              refine ⟨299332509825798448443219757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399110013101064597924293009 299332509825798448443219757)
              ·
                refine ⟨112249691184674418166207409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299332509825798448443219757 112249691184674418166207409)
                ·
                  refine ⟨84187268388505813624655557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112249691184674418166207409 84187268388505813624655557)
                  ·
                    refine ⟨15785112822844840054622917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84187268388505813624655557 15785112822844840054622917)
                    ·
                      refine ⟨2959708654283407510241797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15785112822844840054622917 2959708654283407510241797)
                      ·
                        rfl

theorem cell23_5764012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_5764012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764012 prefixEnd_5764012 := by exact prefixLift 5764012
  have htrace : WordTrace (prefixWord ++ tailWord_5764012) baseStart_5764012 baseEnd_5764012 := by
    simpa [prefixWord, tailWord_5764012, baseEnd_5764012] using wordTrace_append hprefix tailTrace_5764012
  have hstable : (prefixWord ++ tailWord_5764012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764012).length < 2 ^ (prefixWord ++ tailWord_5764012).sum := by decide
  have hdescent : baseEnd_5764012 < baseStart_5764012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764019 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3]
def baseStart_5764019 : Nat := 118140960795 + 5764019 * 2 ^ 59
def prefixEnd_5764019 : Nat := 4983230072969 + 3 ^ 40 * 5764019 * 2
def baseEnd_5764019 : Nat := 2959712248647988982854265

theorem tailTrace_5764019 : CollatzResearch.WordTrace tailWord_5764019 prefixEnd_5764019 2959712248647988982854265 := by
  unfold tailWord_5764019
  simp only [CollatzResearch.WordTrace]
  refine ⟨210231044104951053916943111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140154029403300702611295407 210231044104951053916943111)
  ·
    refine ⟨315346566157426580875414667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210231044104951053916943111 315346566157426580875414667)
    ·
      refine ⟨473019849236139871313122001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315346566157426580875414667 473019849236139871313122001)
      ·
        refine ⟨354764886927104903484841501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473019849236139871313122001 354764886927104903484841501)
        ·
          refine ⟨133036832597664338806815563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354764886927104903484841501 133036832597664338806815563)
          ·
            refine ⟨199555248896496508210223345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133036832597664338806815563 199555248896496508210223345)
            ·
              refine ⟨149666436672372381157667509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199555248896496508210223345 149666436672372381157667509)
              ·
                refine ⟨14031228438034910733531329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149666436672372381157667509 14031228438034910733531329)
                ·
                  refine ⟨10523421328526183050148497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14031228438034910733531329 10523421328526183050148497)
                  ·
                    refine ⟨7892565996394637287611373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10523421328526183050148497 7892565996394637287611373)
                    ·
                      refine ⟨2959712248647988982854265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892565996394637287611373 2959712248647988982854265)
                      ·
                        rfl

theorem cell23_5764019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_5764019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764019 prefixEnd_5764019 := by exact prefixLift 5764019
  have htrace : WordTrace (prefixWord ++ tailWord_5764019) baseStart_5764019 baseEnd_5764019 := by
    simpa [prefixWord, tailWord_5764019, baseEnd_5764019] using wordTrace_append hprefix tailTrace_5764019
  have hstable : (prefixWord ++ tailWord_5764019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764019).length < 2 ^ (prefixWord ++ tailWord_5764019).sum := by decide
  have hdescent : baseEnd_5764019 < baseStart_5764019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764039 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 6]
def baseStart_5764039 : Nat := 118140960795 + 5764039 * 2 ^ 59
def prefixEnd_5764039 : Nat := 4983230072969 + 3 ^ 40 * 5764039 * 2
def baseEnd_5764039 : Nat := 328858057584564322733797

theorem tailTrace_5764039 : CollatzResearch.WordTrace tailWord_5764039 prefixEnd_5764039 328858057584564322733797 := by
  unfold tailWord_5764039
  simp only [CollatzResearch.WordTrace]
  refine ⟨210231773564878597332671171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140154515709919064888447447 210231773564878597332671171)
  ·
    refine ⟨315347660347317895999006757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210231773564878597332671171 315347660347317895999006757)
    ·
      refine ⟨59127686315122105499813767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315347660347317895999006757 59127686315122105499813767)
      ·
        refine ⟨88691529472683158249720651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59127686315122105499813767 88691529472683158249720651)
        ·
          refine ⟨133037294209024737374580977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88691529472683158249720651 133037294209024737374580977)
          ·
            refine ⟨99777970656768553030935733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133037294209024737374580977 99777970656768553030935733)
            ·
              refine ⟨9354184749072051846650225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99777970656768553030935733 9354184749072051846650225)
              ·
                refine ⟨7015638561804038884987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354184749072051846650225 7015638561804038884987669)
                ·
                  refine ⟨328858057584564322733797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7015638561804038884987669 328858057584564322733797)
                  ·
                    rfl

theorem cell23_5764039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 6].length) (baseStart_5764039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764039 prefixEnd_5764039 := by exact prefixLift 5764039
  have htrace : WordTrace (prefixWord ++ tailWord_5764039) baseStart_5764039 baseEnd_5764039 := by
    simpa [prefixWord, tailWord_5764039, baseEnd_5764039] using wordTrace_append hprefix tailTrace_5764039
  have hstable : (prefixWord ++ tailWord_5764039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764039).length < 2 ^ (prefixWord ++ tailWord_5764039).sum := by decide
  have hdescent : baseEnd_5764039 < baseStart_5764039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764056 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 6]
def baseStart_5764056 : Nat := 118140960795 + 5764056 * 2 ^ 59
def prefixEnd_5764056 : Nat := 4983230072969 + 3 ^ 40 * 5764056 * 2
def baseEnd_5764056 : Nat := 328859027492467259787955

theorem tailTrace_5764056 : CollatzResearch.WordTrace tailWord_5764056 prefixEnd_5764056 328859027492467259787955 := by
  unfold tailWord_5764056
  simp only [CollatzResearch.WordTrace]
  refine ⟨105116196802908504618020011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140154929070544672824026681 105116196802908504618020011)
  ·
    refine ⟨157674295204362756927030017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105116196802908504618020011 157674295204362756927030017)
    ·
      refine ⟨118255721403272067695272513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157674295204362756927030017 118255721403272067695272513)
      ·
        refine ⟨88691791052454050771454385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118255721403272067695272513 88691791052454050771454385)
        ·
          refine ⟨66518843289340538078590789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88691791052454050771454385 66518843289340538078590789)
          ·
            refine ⟨12472283116751350889735773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66518843289340538078590789 12472283116751350889735773)
            ·
              refine ⟨4677106168781756583650915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12472283116751350889735773 4677106168781756583650915)
              ·
                refine ⟨7015659253172634875476373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677106168781756583650915 7015659253172634875476373)
                ·
                  refine ⟨328859027492467259787955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7015659253172634875476373 328859027492467259787955)
                  ·
                    rfl

theorem cell23_5764056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_5764056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764056 prefixEnd_5764056 := by exact prefixLift 5764056
  have htrace : WordTrace (prefixWord ++ tailWord_5764056) baseStart_5764056 baseEnd_5764056 := by
    simpa [prefixWord, tailWord_5764056, baseEnd_5764056] using wordTrace_append hprefix tailTrace_5764056
  have hstable : (prefixWord ++ tailWord_5764056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764056).length < 2 ^ (prefixWord ++ tailWord_5764056).sum := by decide
  have hdescent : baseEnd_5764056 < baseStart_5764056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764129 : List Nat := [1, 2, 3, 2, 3, 1, 2, 9]
def baseStart_5764129 : Nat := 118140960795 + 5764129 * 2 ^ 59
def prefixEnd_5764129 : Nat := 4983230072969 + 3 ^ 40 * 5764129 * 2
def baseEnd_5764129 : Nat := 109621064130369761202917

theorem tailTrace_5764129 : CollatzResearch.WordTrace tailWord_5764129 prefixEnd_5764129 109621064130369761202917 := by
  unfold tailWord_5764129
  simp only [CollatzResearch.WordTrace]
  refine ⟨210235056134552542703447441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140156704089701695135631627 210235056134552542703447441)
  ·
    refine ⟨157676292100914407027585581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210235056134552542703447441 157676292100914407027585581)
    ·
      refine ⟨59128609537842902635344593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157676292100914407027585581 59128609537842902635344593)
      ·
        refine ⟨44346457153382176976508445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59128609537842902635344593 44346457153382176976508445)
        ·
          refine ⟨16629921432518316366190667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44346457153382176976508445 16629921432518316366190667)
          ·
            refine ⟨24944882148777474549286001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16629921432518316366190667 24944882148777474549286001)
            ·
              refine ⟨18708661611583105911964501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24944882148777474549286001 18708661611583105911964501)
              ·
                refine ⟨109621064130369761202917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18708661611583105911964501 109621064130369761202917)
                ·
                  rfl

theorem cell23_5764129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 9].length) (baseStart_5764129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764129 prefixEnd_5764129 := by exact prefixLift 5764129
  have htrace : WordTrace (prefixWord ++ tailWord_5764129) baseStart_5764129 baseEnd_5764129 := by
    simpa [prefixWord, tailWord_5764129, baseEnd_5764129] using wordTrace_append hprefix tailTrace_5764129
  have hstable : (prefixWord ++ tailWord_5764129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764129).length < 2 ^ (prefixWord ++ tailWord_5764129).sum := by decide
  have hdescent : baseEnd_5764129 < baseStart_5764129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764140 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_5764140 : Nat := 118140960795 + 5764140 * 2 ^ 59
def prefixEnd_5764140 : Nat := 4983230072969 + 3 ^ 40 * 5764140 * 2
def baseEnd_5764140 : Nat := 2959774379807183009441209

theorem tailTrace_5764140 : CollatzResearch.WordTrace tailWord_5764140 prefixEnd_5764140 2959774379807183009441209 := by
  unfold tailWord_5764140
  simp only [CollatzResearch.WordTrace]
  refine ⟨105117728668756345791048937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140156971558341794388065249 105117728668756345791048937)
  ·
    refine ⟨78838296501567259343286703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105117728668756345791048937 78838296501567259343286703)
    ·
      refine ⟨118257444752350889014930055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78838296501567259343286703 118257444752350889014930055)
      ·
        refine ⟨177386167128526333522395083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118257444752350889014930055 177386167128526333522395083)
        ·
          refine ⟨266079250692789500283592625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177386167128526333522395083 266079250692789500283592625)
          ·
            refine ⟨199559438019592125212694469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266079250692789500283592625 199559438019592125212694469)
            ·
              refine ⟨37417394628673523477380213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199559438019592125212694469 37417394628673523477380213)
              ·
                refine ⟨3507880746438142826004395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37417394628673523477380213 3507880746438142826004395)
                ·
                  refine ⟨5261821119657214239006593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507880746438142826004395 5261821119657214239006593)
                  ·
                    refine ⟨3946365839742910679254945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261821119657214239006593 3946365839742910679254945)
                    ·
                      refine ⟨2959774379807183009441209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946365839742910679254945 2959774379807183009441209)
                      ·
                        rfl

theorem cell23_5764140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_5764140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764140 prefixEnd_5764140 := by exact prefixLift 5764140
  have htrace : WordTrace (prefixWord ++ tailWord_5764140) baseStart_5764140 baseEnd_5764140 := by
    simpa [prefixWord, tailWord_5764140, baseEnd_5764140] using wordTrace_append hprefix tailTrace_5764140
  have hstable : (prefixWord ++ tailWord_5764140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764140).length < 2 ^ (prefixWord ++ tailWord_5764140).sum := by decide
  have hdescent : baseEnd_5764140 < baseStart_5764140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764150 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5764150 : Nat := 118140960795 + 5764150 * 2 ^ 59
def prefixEnd_5764150 : Nat := 4983230072969 + 3 ^ 40 * 5764150 * 2
def baseEnd_5764150 : Nat := 986593171537909323438721

theorem tailTrace_5764150 : CollatzResearch.WordTrace tailWord_5764150 prefixEnd_5764150 986593171537909323438721 := by
  unfold tailWord_5764150
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139738879217278955622619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140157214711650975526641269 13139738879217278955622619)
  ·
    refine ⟨19709608318825918433433929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13139738879217278955622619 19709608318825918433433929)
    ·
      refine ⟨14782206239119438825075447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19709608318825918433433929 14782206239119438825075447)
      ·
        refine ⟨22173309358679158237613171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14782206239119438825075447 22173309358679158237613171)
        ·
          refine ⟨33259964038018737356419757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173309358679158237613171 33259964038018737356419757)
          ·
            refine ⟨12472486514257026508657409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33259964038018737356419757 12472486514257026508657409)
            ·
              refine ⟨9354364885692769881493057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472486514257026508657409 9354364885692769881493057)
              ·
                refine ⟨7015773664269577411119793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354364885692769881493057 7015773664269577411119793)
                ·
                  refine ⟨5261830248202183058339845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7015773664269577411119793 5261830248202183058339845)
                  ·
                    refine ⟨986593171537909323438721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261830248202183058339845 986593171537909323438721)
                    ·
                      rfl

theorem cell23_5764150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5764150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764150 prefixEnd_5764150 := by exact prefixLift 5764150
  have htrace : WordTrace (prefixWord ++ tailWord_5764150) baseStart_5764150 baseEnd_5764150 := by
    simpa [prefixWord, tailWord_5764150, baseEnd_5764150] using wordTrace_append hprefix tailTrace_5764150
  have hstable : (prefixWord ++ tailWord_5764150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764150).length < 2 ^ (prefixWord ++ tailWord_5764150).sum := by decide
  have hdescent : baseEnd_5764150 < baseStart_5764150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764157 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5764157 : Nat := 118140960795 + 5764157 * 2 ^ 59
def prefixEnd_5764157 : Nat := 4983230072969 + 3 ^ 40 * 5764157 * 2
def baseEnd_5764157 : Nat := 2959783108978309442928631

theorem tailTrace_5764157 : CollatzResearch.WordTrace tailWord_5764157 prefixEnd_5764157 2959783108978309442928631 := by
  unfold tailWord_5764157
  simp only [CollatzResearch.WordTrace]
  refine ⟨210236077378451103485466725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140157384918967402323644483 210236077378451103485466725)
  ·
    refine ⟨39419264508459581903525011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210236077378451103485466725 39419264508459581903525011)
    ·
      refine ⟨59128896762689372855287517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39419264508459581903525011 59128896762689372855287517)
      ·
        refine ⟨22173336286008514820732819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59128896762689372855287517 22173336286008514820732819)
        ·
          refine ⟨33260004429012772231099229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173336286008514820732819 33260004429012772231099229)
          ·
            refine ⟨12472501660879789586662211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33260004429012772231099229 12472501660879789586662211)
            ·
              refine ⟨18708752491319684379993317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12472501660879789586662211 18708752491319684379993317)
              ·
                refine ⟨3507891092122440821248747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18708752491319684379993317 3507891092122440821248747)
                ·
                  refine ⟨5261836638183661231873121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507891092122440821248747 5261836638183661231873121)
                  ·
                    refine ⟨3946377478637745923904841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5261836638183661231873121 3946377478637745923904841)
                    ·
                      refine ⟨2959783108978309442928631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946377478637745923904841 2959783108978309442928631)
                      ·
                        rfl

theorem cell23_5764157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5764157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764157 prefixEnd_5764157 := by exact prefixLift 5764157
  have htrace : WordTrace (prefixWord ++ tailWord_5764157) baseStart_5764157 baseEnd_5764157 := by
    simpa [prefixWord, tailWord_5764157, baseEnd_5764157] using wordTrace_append hprefix tailTrace_5764157
  have hstable : (prefixWord ++ tailWord_5764157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764157).length < 2 ^ (prefixWord ++ tailWord_5764157).sum := by decide
  have hdescent : baseEnd_5764157 < baseStart_5764157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764173 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_5764173 : Nat := 118140960795 + 5764173 * 2 ^ 59
def prefixEnd_5764173 : Nat := 4983230072969 + 3 ^ 40 * 5764173 * 2
def baseEnd_5764173 : Nat := 2959791324668781380328557

theorem tailTrace_5764173 : CollatzResearch.WordTrace tailWord_5764173 prefixEnd_5764173 2959791324668781380328557 := by
  unfold tailWord_5764173
  simp only [CollatzResearch.WordTrace]
  refine ⟨210236660946393138218049173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140157773964262092145366115 210236660946393138218049173)
  ·
    refine ⟨9854843481862178353971055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 210236660946393138218049173 9854843481862178353971055)
    ·
      refine ⟨14782265222793267530956583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9854843481862178353971055 14782265222793267530956583)
      ·
        refine ⟨22173397834189901296434875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14782265222793267530956583 22173397834189901296434875)
        ·
          refine ⟨33260096751284851944652313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173397834189901296434875 33260096751284851944652313)
          ·
            refine ⟨24945072563463638958489235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33260096751284851944652313 24945072563463638958489235)
            ·
              refine ⟨37417608845195458437733853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24945072563463638958489235 37417608845195458437733853)
              ·
                refine ⟨14031603316948296914150195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37417608845195458437733853 14031603316948296914150195)
                ·
                  refine ⟨21047404975422445371225293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14031603316948296914150195 21047404975422445371225293)
                  ·
                    refine ⟨7892776865783417014209485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21047404975422445371225293 7892776865783417014209485)
                    ·
                      refine ⟨2959791324668781380328557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7892776865783417014209485 2959791324668781380328557)
                      ·
                        rfl

theorem cell23_5764173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_5764173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764173 prefixEnd_5764173 := by exact prefixLift 5764173
  have htrace : WordTrace (prefixWord ++ tailWord_5764173) baseStart_5764173 baseEnd_5764173 := by
    simpa [prefixWord, tailWord_5764173, baseEnd_5764173] using wordTrace_append hprefix tailTrace_5764173
  have hstable : (prefixWord ++ tailWord_5764173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764173).length < 2 ^ (prefixWord ++ tailWord_5764173).sum := by decide
  have hdescent : baseEnd_5764173 < baseStart_5764173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764183 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_5764183 : Nat := 118140960795 + 5764183 * 2 ^ 59
def prefixEnd_5764183 : Nat := 4983230072969 + 3 ^ 40 * 5764183 * 2
def baseEnd_5764183 : Nat := 2959796459475326341203511

theorem tailTrace_5764183 : CollatzResearch.WordTrace tailWord_5764183 prefixEnd_5764183 2959796459475326341203511 := by
  unfold tailWord_5764183
  simp only [CollatzResearch.WordTrace]
  refine ⟨210237025676356909925913203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140158017117571273283942135 210237025676356909925913203)
  ·
    refine ⟨315355538514535364888869805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210237025676356909925913203 315355538514535364888869805)
    ·
      refine ⟨118258326942950761833326177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315355538514535364888869805 118258326942950761833326177)
      ·
        refine ⟨88693745207213071374994633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118258326942950761833326177 88693745207213071374994633)
        ·
          refine ⟨66520308905409803531245975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88693745207213071374994633 66520308905409803531245975)
          ·
            refine ⟨99780463358114705296868963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66520308905409803531245975 99780463358114705296868963)
            ·
              refine ⟨149670695037172057945303445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99780463358114705296868963 149670695037172057945303445)
              ·
                refine ⟨7015813829867440216186099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149670695037172057945303445 7015813829867440216186099)
                ·
                  refine ⟨10523720744801160324279149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015813829867440216186099 10523720744801160324279149)
                  ·
                    refine ⟨3946395279300435121604681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10523720744801160324279149 3946395279300435121604681)
                    ·
                      refine ⟨2959796459475326341203511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946395279300435121604681 2959796459475326341203511)
                      ·
                        rfl

theorem cell23_5764183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_5764183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764183 prefixEnd_5764183 := by exact prefixLift 5764183
  have htrace : WordTrace (prefixWord ++ tailWord_5764183) baseStart_5764183 baseEnd_5764183 := by
    simpa [prefixWord, tailWord_5764183, baseEnd_5764183] using wordTrace_append hprefix tailTrace_5764183
  have hstable : (prefixWord ++ tailWord_5764183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764183).length < 2 ^ (prefixWord ++ tailWord_5764183).sum := by decide
  have hdescent : baseEnd_5764183 < baseStart_5764183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764206 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_5764206 : Nat := 118140960795 + 5764206 * 2 ^ 59
def prefixEnd_5764206 : Nat := 4983230072969 + 3 ^ 40 * 5764206 * 2
def baseEnd_5764206 : Nat := 986602756510126583738635

theorem tailTrace_5764206 : CollatzResearch.WordTrace tailWord_5764206 prefixEnd_5764206 986602756510126583738635 := by
  unfold tailWord_5764206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279733069409198106750059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140158576370182389902666981 26279733069409198106750059)
  ·
    refine ⟨39419599604113797160125089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26279733069409198106750059 39419599604113797160125089)
    ·
      refine ⟨29564699703085347870093817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39419599604113797160125089 29564699703085347870093817)
      ·
        refine ⟨22173524777314010902570363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29564699703085347870093817 22173524777314010902570363)
        ·
          refine ⟨33260287165971016353855545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173524777314010902570363 33260287165971016353855545)
          ·
            refine ⟨24945215374478262265391659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33260287165971016353855545 24945215374478262265391659)
            ·
              refine ⟨37417823061717393398087489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24945215374478262265391659 37417823061717393398087489)
              ·
                refine ⟨28063367296288045048565617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37417823061717393398087489 28063367296288045048565617)
                ·
                  refine ⟨21047525472216033786424213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28063367296288045048565617 21047525472216033786424213)
                  ·
                    refine ⟨986602756510126583738635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21047525472216033786424213 986602756510126583738635)
                    ·
                      rfl

theorem cell23_5764206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_5764206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764206 prefixEnd_5764206 := by exact prefixLift 5764206
  have htrace : WordTrace (prefixWord ++ tailWord_5764206) baseStart_5764206 baseEnd_5764206 := by
    simpa [prefixWord, tailWord_5764206, baseEnd_5764206] using wordTrace_append hprefix tailTrace_5764206
  have hstable : (prefixWord ++ tailWord_5764206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764206).length < 2 ^ (prefixWord ++ tailWord_5764206).sum := by decide
  have hdescent : baseEnd_5764206 < baseStart_5764206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764259 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_5764259 : Nat := 118140960795 + 5764259 * 2 ^ 59
def prefixEnd_5764259 : Nat := 4983230072969 + 3 ^ 40 * 5764259 * 2
def baseEnd_5764259 : Nat := 2959835484005068043853161

theorem tailTrace_5764259 : CollatzResearch.WordTrace tailWord_5764259 prefixEnd_5764259 2959835484005068043853161 := by
  unfold tailWord_5764259
  simp only [CollatzResearch.WordTrace]
  refine ⟨210239797624081574905679831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140159865082721049937119887 210239797624081574905679831)
  ·
    refine ⟨315359696436122362358519747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210239797624081574905679831 315359696436122362358519747)
    ·
      refine ⟨473039544654183543537779621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315359696436122362358519747 473039544654183543537779621)
      ·
        refine ⟨88694914622659414413333679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473039544654183543537779621 88694914622659414413333679)
        ·
          refine ⟨133042371933989121620000519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88694914622659414413333679 133042371933989121620000519)
          ·
            refine ⟨199563557900983682430000779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133042371933989121620000519 199563557900983682430000779)
            ·
              refine ⟨299345336851475523645001169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199563557900983682430000779 299345336851475523645001169)
              ·
                refine ⟨224509002638606642733750877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299345336851475523645001169 224509002638606642733750877)
                ·
                  refine ⟨84190875989477491025156579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224509002638606642733750877 84190875989477491025156579)
                  ·
                    refine ⟨126286313984216236537734869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84190875989477491025156579 126286313984216236537734869)
                    ·
                      refine ⟨2959835484005068043853161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126286313984216236537734869 2959835484005068043853161)
                      ·
                        rfl

theorem cell23_5764259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_5764259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764259 prefixEnd_5764259 := by exact prefixLift 5764259
  have htrace : WordTrace (prefixWord ++ tailWord_5764259) baseStart_5764259 baseEnd_5764259 := by
    simpa [prefixWord, tailWord_5764259, baseEnd_5764259] using wordTrace_append hprefix tailTrace_5764259
  have hstable : (prefixWord ++ tailWord_5764259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764259).length < 2 ^ (prefixWord ++ tailWord_5764259).sum := by decide
  have hdescent : baseEnd_5764259 < baseStart_5764259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764336 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_5764336 : Nat := 118140960795 + 5764336 * 2 ^ 59
def prefixEnd_5764336 : Nat := 4983230072969 + 3 ^ 40 * 5764336 * 2
def baseEnd_5764336 : Nat := 2959875022015464242590307

theorem tailTrace_5764336 : CollatzResearch.WordTrace tailWord_5764336 prefixEnd_5764336 2959875022015464242590307 := by
  unfold tailWord_5764336
  simp only [CollatzResearch.WordTrace]
  refine ⟨105121303022401308528116431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140161737363201744704155241 105121303022401308528116431)
  ·
    refine ⟨157681954533601962792174647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105121303022401308528116431 157681954533601962792174647)
    ·
      refine ⟨236522931800402944188261971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157681954533601962792174647 236522931800402944188261971)
      ·
        refine ⟨354784397700604416282392957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236522931800402944188261971 354784397700604416282392957)
        ·
          refine ⟨133044149137726656105897359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354784397700604416282392957 133044149137726656105897359)
          ·
            refine ⟨199566223706589984158846039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133044149137726656105897359 199566223706589984158846039)
            ·
              refine ⟨299349335559884976238269059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199566223706589984158846039 299349335559884976238269059)
              ·
                refine ⟨449024003339827464357403589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299349335559884976238269059 449024003339827464357403589)
                ·
                  refine ⟨84192000626217649567013173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 449024003339827464357403589 84192000626217649567013173)
                  ·
                    refine ⟨7893000058707904646907485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84192000626217649567013173 7893000058707904646907485)
                    ·
                      refine ⟨2959875022015464242590307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893000058707904646907485 2959875022015464242590307)
                      ·
                        rfl

theorem cell23_5764336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_5764336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764336 prefixEnd_5764336 := by exact prefixLift 5764336
  have htrace : WordTrace (prefixWord ++ tailWord_5764336) baseStart_5764336 baseEnd_5764336 := by
    simpa [prefixWord, tailWord_5764336, baseEnd_5764336] using wordTrace_append hprefix tailTrace_5764336
  have hstable : (prefixWord ++ tailWord_5764336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764336).length < 2 ^ (prefixWord ++ tailWord_5764336).sum := by decide
  have hdescent : baseEnd_5764336 < baseStart_5764336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764354 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_5764354 : Nat := 118140960795 + 5764354 * 2 ^ 59
def prefixEnd_5764354 : Nat := 4983230072969 + 3 ^ 40 * 5764354 * 2
def baseEnd_5764354 : Nat := 2959884264667245172165225

theorem tailTrace_5764354 : CollatzResearch.WordTrace tailWord_5764354 prefixEnd_5764354 2959884264667245172165225 := by
  unfold tailWord_5764354
  simp only [CollatzResearch.WordTrace]
  refine ⟨52560815639684351532597029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140162175039158270753592077 52560815639684351532597029)
  ·
    refine ⟨9855152932440815912361943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52560815639684351532597029 9855152932440815912361943)
    ·
      refine ⟨14782729398661223868542915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9855152932440815912361943 14782729398661223868542915)
      ·
        refine ⟨22174094097991835802814373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14782729398661223868542915 22174094097991835802814373)
        ·
          refine ⟨4157642643373469213027695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22174094097991835802814373 4157642643373469213027695)
          ·
            refine ⟨6236463965060203819541543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157642643373469213027695 6236463965060203819541543)
            ·
              refine ⟨9354695947590305729312315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236463965060203819541543 9354695947590305729312315)
              ·
                refine ⟨14032043921385458593968473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354695947590305729312315 14032043921385458593968473)
                ·
                  refine ⟨10524032941039093945476355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14032043921385458593968473 10524032941039093945476355)
                  ·
                    refine ⟨15786049411558640918214533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10524032941039093945476355 15786049411558640918214533)
                    ·
                      refine ⟨2959884264667245172165225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15786049411558640918214533 2959884264667245172165225)
                      ·
                        rfl

theorem cell23_5764354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_5764354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764354 prefixEnd_5764354 := by exact prefixLift 5764354
  have htrace : WordTrace (prefixWord ++ tailWord_5764354) baseStart_5764354 baseEnd_5764354 := by
    simpa [prefixWord, tailWord_5764354, baseEnd_5764354] using wordTrace_append hprefix tailTrace_5764354
  have hstable : (prefixWord ++ tailWord_5764354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764354).length < 2 ^ (prefixWord ++ tailWord_5764354).sum := by decide
  have hdescent : baseEnd_5764354 < baseStart_5764354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764380 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_5764380 : Nat := 118140960795 + 5764380 * 2 ^ 59
def prefixEnd_5764380 : Nat := 4983230072969 + 3 ^ 40 * 5764380 * 2
def baseEnd_5764380 : Nat := 2959897615164262070440105

theorem tailTrace_5764380 : CollatzResearch.WordTrace tailWord_5764380 prefixEnd_5764380 2959897615164262070440105 := by
  unfold tailWord_5764380
  simp only [CollatzResearch.WordTrace]
  refine ⟨105122105428321606285417297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140162807237762141713889729 105122105428321606285417297)
  ·
    refine ⟨78841579071241204714062973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105122105428321606285417297 78841579071241204714062973)
    ·
      refine ⟨29565592151715451767773615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78841579071241204714062973 29565592151715451767773615)
      ·
        refine ⟨44348388227573177651660423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29565592151715451767773615 44348388227573177651660423)
        ·
          refine ⟨66522582341359766477490635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44348388227573177651660423 66522582341359766477490635)
          ·
            refine ⟨99783873512039649716235953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66522582341359766477490635 99783873512039649716235953)
            ·
              refine ⟨74837905134029737287176965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99783873512039649716235953 74837905134029737287176965)
              ·
                refine ⟨14032107212630575741345681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74837905134029737287176965 14032107212630575741345681)
                ·
                  refine ⟨10524080409472931806009261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14032107212630575741345681 10524080409472931806009261)
                  ·
                    refine ⟨3946530153552349427253473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10524080409472931806009261 3946530153552349427253473)
                    ·
                      refine ⟨2959897615164262070440105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946530153552349427253473 2959897615164262070440105)
                      ·
                        rfl

theorem cell23_5764380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_5764380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764380 prefixEnd_5764380 := by exact prefixLift 5764380
  have htrace : WordTrace (prefixWord ++ tailWord_5764380) baseStart_5764380 baseEnd_5764380 := by
    simpa [prefixWord, tailWord_5764380, baseEnd_5764380] using wordTrace_append hprefix tailTrace_5764380
  have hstable : (prefixWord ++ tailWord_5764380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764380).length < 2 ^ (prefixWord ++ tailWord_5764380).sum := by decide
  have hdescent : baseEnd_5764380 < baseStart_5764380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764387 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 1, 1, 3]
def baseStart_5764387 : Nat := 118140960795 + 5764387 * 2 ^ 59
def prefixEnd_5764387 : Nat := 4983230072969 + 3 ^ 40 * 5764387 * 2
def baseEnd_5764387 : Nat := 2959901209528843543052573

theorem tailTrace_5764387 : CollatzResearch.WordTrace tailWord_5764387 prefixEnd_5764387 2959901209528843543052573 := by
  unfold tailWord_5764387
  simp only [CollatzResearch.WordTrace]
  refine ⟨210244466167617852766339415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140162977445078568510892943 210244466167617852766339415)
  ·
    refine ⟨315366699251426779149509123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210244466167617852766339415 315366699251426779149509123)
    ·
      refine ⟨473050048877140168724263685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315366699251426779149509123 473050048877140168724263685)
      ·
        refine ⟨88696884164463781635799441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473050048877140168724263685 88696884164463781635799441)
        ·
          refine ⟨66522663123347836226849581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88696884164463781635799441 66522663123347836226849581)
          ·
            refine ⟨24945998671255438585068593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66522663123347836226849581 24945998671255438585068593)
            ·
              refine ⟨18709499003441578938801445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24945998671255438585068593 18709499003441578938801445)
              ·
                refine ⟨3508031063145296051025271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18709499003441578938801445 3508031063145296051025271)
                ·
                  refine ⟨5262046594717944076537907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508031063145296051025271 5262046594717944076537907)
                  ·
                    refine ⟨7893069892076916114806861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262046594717944076537907 7893069892076916114806861)
                    ·
                      refine ⟨2959901209528843543052573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893069892076916114806861 2959901209528843543052573)
                      ·
                        rfl

theorem cell23_5764387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_5764387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764387 prefixEnd_5764387 := by exact prefixLift 5764387
  have htrace : WordTrace (prefixWord ++ tailWord_5764387) baseStart_5764387 baseEnd_5764387 := by
    simpa [prefixWord, tailWord_5764387, baseEnd_5764387] using wordTrace_append hprefix tailTrace_5764387
  have hstable : (prefixWord ++ tailWord_5764387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764387).length < 2 ^ (prefixWord ++ tailWord_5764387).sum := by decide
  have hdescent : baseEnd_5764387 < baseStart_5764387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764397 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5764397 : Nat := 118140960795 + 5764397 * 2 ^ 59
def prefixEnd_5764397 : Nat := 4983230072969 + 3 ^ 40 * 5764397 * 2
def baseEnd_5764397 : Nat := 2959906344335388503927527

theorem tailTrace_5764397 : CollatzResearch.WordTrace tailWord_5764397 prefixEnd_5764397 2959906344335388503927527 := by
  unfold tailWord_5764397
  simp only [CollatzResearch.WordTrace]
  refine ⟨210244830897581624474203445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140163220598387749649468963 210244830897581624474203445)
  ·
    refine ⟨19710452896648277294456573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210244830897581624474203445 19710452896648277294456573)
    ·
      refine ⟨7391419836243103985421215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19710452896648277294456573 7391419836243103985421215)
      ·
        refine ⟨11087129754364655978131823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391419836243103985421215 11087129754364655978131823)
        ·
          refine ⟨16630694631546983967197735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11087129754364655978131823 16630694631546983967197735)
          ·
            refine ⟨24946041947320475950796603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16630694631546983967197735 24946041947320475950796603)
            ·
              refine ⟨37419062920980713926194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24946041947320475950796603 37419062920980713926194905)
              ·
                refine ⟨28064297190735535444646179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37419062920980713926194905 28064297190735535444646179)
                ·
                  refine ⟨42096445786103303166969269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28064297190735535444646179 42096445786103303166969269)
                  ·
                    refine ⟨3946541792447184671903369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42096445786103303166969269 3946541792447184671903369)
                    ·
                      refine ⟨2959906344335388503927527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946541792447184671903369 2959906344335388503927527)
                      ·
                        rfl

theorem cell23_5764397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5764397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764397 prefixEnd_5764397 := by exact prefixLift 5764397
  have htrace : WordTrace (prefixWord ++ tailWord_5764397) baseStart_5764397 baseEnd_5764397 := by
    simpa [prefixWord, tailWord_5764397, baseEnd_5764397] using wordTrace_append hprefix tailTrace_5764397
  have hstable : (prefixWord ++ tailWord_5764397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764397).length < 2 ^ (prefixWord ++ tailWord_5764397).sum := by decide
  have hdescent : baseEnd_5764397 < baseStart_5764397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764403 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 6]
def baseStart_5764403 : Nat := 118140960795 + 5764403 * 2 ^ 59
def prefixEnd_5764403 : Nat := 4983230072969 + 3 ^ 40 * 5764403 * 2
def baseEnd_5764403 : Nat := 986636475073105160150833

theorem tailTrace_5764403 : CollatzResearch.WordTrace tailWord_5764403 prefixEnd_5764403 986636475073105160150833 := by
  unfold tailWord_5764403
  simp only [CollatzResearch.WordTrace]
  refine ⟨210245049735559887498921863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140163366490373258332614575 210245049735559887498921863)
  ·
    refine ⟨315367574603339831248382795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210245049735559887498921863 315367574603339831248382795)
    ·
      refine ⟨473051361905009746872574193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315367574603339831248382795 473051361905009746872574193)
      ·
        refine ⟨354788521428757310154430645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473051361905009746872574193 354788521428757310154430645)
        ·
          refine ⟨33261423883945997826977873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354788521428757310154430645 33261423883945997826977873)
          ·
            refine ⟨24946067912959498370233405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33261423883945997826977873 24946067912959498370233405)
            ·
              refine ⟨9354775467359811888837527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24946067912959498370233405 9354775467359811888837527)
              ·
                refine ⟨14032163201039717833256291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354775467359811888837527 14032163201039717833256291)
                ·
                  refine ⟨21048244801559576749884437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14032163201039717833256291 21048244801559576749884437)
                  ·
                    refine ⟨986636475073105160150833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21048244801559576749884437 986636475073105160150833)
                    ·
                      rfl

theorem cell23_5764403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].length) (baseStart_5764403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764403 prefixEnd_5764403 := by exact prefixLift 5764403
  have htrace : WordTrace (prefixWord ++ tailWord_5764403) baseStart_5764403 baseEnd_5764403 := by
    simpa [prefixWord, tailWord_5764403, baseEnd_5764403] using wordTrace_append hprefix tailTrace_5764403
  have hstable : (prefixWord ++ tailWord_5764403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764403).length < 2 ^ (prefixWord ++ tailWord_5764403).sum := by decide
  have hdescent : baseEnd_5764403 < baseStart_5764403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764410 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_5764410 : Nat := 118140960795 + 5764410 * 2 ^ 59
def prefixEnd_5764410 : Nat := 4983230072969 + 3 ^ 40 * 5764410 * 2
def baseEnd_5764410 : Nat := 2959913019583896953064967

theorem tailTrace_5764410 : CollatzResearch.WordTrace tailWord_5764410 prefixEnd_5764410 2959913019583896953064967 := by
  unfold tailWord_5764410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52561326261633631923606671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140163536697689685129617789 52561326261633631923606671)
  ·
    refine ⟨78841989392450447885410007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52561326261633631923606671 78841989392450447885410007)
    ·
      refine ⟨118262984088675671828115011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78841989392450447885410007 118262984088675671828115011)
      ·
        refine ⟨177394476133013507742172517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118262984088675671828115011 177394476133013507742172517)
        ·
          refine ⟨33261464274940032701657347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177394476133013507742172517 33261464274940032701657347)
          ·
            refine ⟨49892196412410049052486021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33261464274940032701657347 49892196412410049052486021)
            ·
              refine ⟨9354786827326884197341129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49892196412410049052486021 9354786827326884197341129)
              ·
                refine ⟨7016090120495163148005847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354786827326884197341129 7016090120495163148005847)
                ·
                  refine ⟨10524135180742744722008771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016090120495163148005847 10524135180742744722008771)
                  ·
                    refine ⟨15786202771114117083013157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10524135180742744722008771 15786202771114117083013157)
                    ·
                      refine ⟨2959913019583896953064967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15786202771114117083013157 2959913019583896953064967)
                      ·
                        rfl

theorem cell23_5764410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_5764410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764410 prefixEnd_5764410 := by exact prefixLift 5764410
  have htrace : WordTrace (prefixWord ++ tailWord_5764410) baseStart_5764410 baseEnd_5764410 := by
    simpa [prefixWord, tailWord_5764410, baseEnd_5764410] using wordTrace_append hprefix tailTrace_5764410
  have hstable : (prefixWord ++ tailWord_5764410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764410).length < 2 ^ (prefixWord ++ tailWord_5764410).sum := by decide
  have hdescent : baseEnd_5764410 < baseStart_5764410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764416 : List Nat := [2, 1, 1, 2, 2, 1, 5, 9]
def baseStart_5764416 : Nat := 118140960795 + 5764416 * 2 ^ 59
def prefixEnd_5764416 : Nat := 4983230072969 + 3 ^ 40 * 5764416 * 2
def baseEnd_5764416 : Nat := 109626522239549034429257

theorem tailTrace_5764416 : CollatzResearch.WordTrace tailWord_5764416 prefixEnd_5764416 109626522239549034429257 := by
  unfold tailWord_5764416
  simp only [CollatzResearch.WordTrace]
  refine ⟨105122761942256395359572551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140163682589675193812763401 105122761942256395359572551)
  ·
    refine ⟨157684142913384593039358827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105122761942256395359572551 157684142913384593039358827)
    ·
      refine ⟨236526214370076889559038241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157684142913384593039358827 236526214370076889559038241)
      ·
        refine ⟨177394660777557667169278681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236526214370076889559038241 177394660777557667169278681)
        ·
          refine ⟨133045995583168250376959011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177394660777557667169278681 133045995583168250376959011)
          ·
            refine ⟨199568993374752375565438517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133045995583168250376959011 199568993374752375565438517)
            ·
              refine ⟨18709593128883035209259861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199568993374752375565438517 18709593128883035209259861)
              ·
                refine ⟨109626522239549034429257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18709593128883035209259861 109626522239549034429257)
                ·
                  rfl

theorem cell23_5764416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_5764416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764416 prefixEnd_5764416 := by exact prefixLift 5764416
  have htrace : WordTrace (prefixWord ++ tailWord_5764416) baseStart_5764416 baseEnd_5764416 := by
    simpa [prefixWord, tailWord_5764416, baseEnd_5764416] using wordTrace_append hprefix tailTrace_5764416
  have hstable : (prefixWord ++ tailWord_5764416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764416).length < 2 ^ (prefixWord ++ tailWord_5764416).sum := by decide
  have hdescent : baseEnd_5764416 < baseStart_5764416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764430 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_5764430 : Nat := 118140960795 + 5764430 * 2 ^ 59
def prefixEnd_5764430 : Nat := 4983230072969 + 3 ^ 40 * 5764430 * 2
def baseEnd_5764430 : Nat := 2959923289196986874814875

theorem tailTrace_5764430 : CollatzResearch.WordTrace tailWord_5764430 prefixEnd_5764430 2959923289196986874814875 := by
  unfold tailWord_5764430
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280754313307758888769343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140164023004308047406769829 26280754313307758888769343)
  ·
    refine ⟨39421131469961638333154015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26280754313307758888769343 39421131469961638333154015)
    ·
      refine ⟨59131697204942457499731023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39421131469961638333154015 59131697204942457499731023)
      ·
        refine ⟨88697545807413686249596535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59131697204942457499731023 88697545807413686249596535)
        ·
          refine ⟨133046318711120529374394803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88697545807413686249596535 133046318711120529374394803)
          ·
            refine ⟨199569478066680794061592205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133046318711120529374394803 199569478066680794061592205)
            ·
              refine ⟨74838554275005297773097077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199569478066680794061592205 74838554275005297773097077)
              ·
                refine ⟨7016114463281746666227851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74838554275005297773097077 7016114463281746666227851)
                ·
                  refine ⟨10524171694922619999341777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016114463281746666227851 10524171694922619999341777)
                  ·
                    refine ⟨7893128771191964999506333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10524171694922619999341777 7893128771191964999506333)
                    ·
                      refine ⟨2959923289196986874814875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893128771191964999506333 2959923289196986874814875)
                      ·
                        rfl

theorem cell23_5764430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_5764430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764430 prefixEnd_5764430 := by exact prefixLift 5764430
  have htrace : WordTrace (prefixWord ++ tailWord_5764430) baseStart_5764430 baseEnd_5764430 := by
    simpa [prefixWord, tailWord_5764430, baseEnd_5764430] using wordTrace_append hprefix tailTrace_5764430
  have hstable : (prefixWord ++ tailWord_5764430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764430).length < 2 ^ (prefixWord ++ tailWord_5764430).sum := by decide
  have hdescent : baseEnd_5764430 < baseStart_5764430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764500 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5764500 : Nat := 118140960795 + 5764500 * 2 ^ 59
def prefixEnd_5764500 : Nat := 4983230072969 + 3 ^ 40 * 5764500 * 2
def baseEnd_5764500 : Nat := 2959959232842801600939553

theorem tailTrace_5764500 : CollatzResearch.WordTrace tailWord_5764500 prefixEnd_5764500 2959959232842801600939553 := by
  unfold tailWord_5764500
  simp only [CollatzResearch.WordTrace]
  refine ⟨105124293808104236532601477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140165725077472315376801969 105124293808104236532601477)
  ·
    refine ⟨19710805089019544349862777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105124293808104236532601477 19710805089019544349862777)
    ·
      refine ⟨14783103816764658262397083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19710805089019544349862777 14783103816764658262397083)
      ·
        refine ⟨22174655725146987393595625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14783103816764658262397083 22174655725146987393595625)
        ·
          refine ⟨16630991793860240545196719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22174655725146987393595625 16630991793860240545196719)
          ·
            refine ⟨24946487690790360817795079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16630991793860240545196719 24946487690790360817795079)
            ·
              refine ⟨37419731536185541226692619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24946487690790360817795079 37419731536185541226692619)
              ·
                refine ⟨56129597304278311840038929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37419731536185541226692619 56129597304278311840038929)
                ·
                  refine ⟨42097197978208733880029197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56129597304278311840038929 42097197978208733880029197)
                  ·
                    refine ⟨15786449241828275205010949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42097197978208733880029197 15786449241828275205010949)
                    ·
                      refine ⟨2959959232842801600939553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15786449241828275205010949 2959959232842801600939553)
                      ·
                        rfl

theorem cell23_5764500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5764500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764500 prefixEnd_5764500 := by exact prefixLift 5764500
  have htrace : WordTrace (prefixWord ++ tailWord_5764500) baseStart_5764500 baseEnd_5764500 := by
    simpa [prefixWord, tailWord_5764500, baseEnd_5764500] using wordTrace_append hprefix tailTrace_5764500
  have hstable : (prefixWord ++ tailWord_5764500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764500).length < 2 ^ (prefixWord ++ tailWord_5764500).sum := by decide
  have hdescent : baseEnd_5764500 < baseStart_5764500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764553 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_5764553 : Nat := 118140960795 + 5764553 * 2 ^ 59
def prefixEnd_5764553 : Nat := 4983230072969 + 3 ^ 40 * 5764553 * 2
def baseEnd_5764553 : Nat := 986662149105829964525603

theorem tailTrace_5764553 : CollatzResearch.WordTrace tailWord_5764553 prefixEnd_5764553 986662149105829964525603 := by
  unfold tailWord_5764553
  simp only [CollatzResearch.WordTrace]
  refine ⟨210250520685016463116882313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140167013790010975411254875 210250520685016463116882313)
  ·
    refine ⟨157687890513762347337661735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210250520685016463116882313 157687890513762347337661735)
    ·
      refine ⟨236531835770643521006492603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157687890513762347337661735 236531835770643521006492603)
      ·
        refine ⟨354797753655965281509738905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236531835770643521006492603 354797753655965281509738905)
        ·
          refine ⟨266098315241973961132304179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354797753655965281509738905 266098315241973961132304179)
          ·
            refine ⟨399147472862960941698456269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266098315241973961132304179 399147472862960941698456269)
            ·
              refine ⟨149680302323610353136921101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399147472862960941698456269 149680302323610353136921101)
              ·
                refine ⟨56130113371353882426345413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149680302323610353136921101 56130113371353882426345413)
                ·
                  refine ⟨10524396257128852954939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56130113371353882426345413 10524396257128852954939765)
                  ·
                    refine ⟨986662149105829964525603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10524396257128852954939765 986662149105829964525603)
                    ·
                      rfl

theorem cell23_5764553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_5764553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764553 prefixEnd_5764553 := by exact prefixLift 5764553
  have htrace : WordTrace (prefixWord ++ tailWord_5764553) baseStart_5764553 baseEnd_5764553 := by
    simpa [prefixWord, tailWord_5764553, baseEnd_5764553] using wordTrace_append hprefix tailTrace_5764553
  have hstable : (prefixWord ++ tailWord_5764553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764553).length < 2 ^ (prefixWord ++ tailWord_5764553).sum := by decide
  have hdescent : baseEnd_5764553 < baseStart_5764553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764590 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_5764590 : Nat := 118140960795 + 5764590 * 2 ^ 59
def prefixEnd_5764590 : Nat := 4983230072969 + 3 ^ 40 * 5764590 * 2
def baseEnd_5764590 : Nat := 2960005446101706248814139

theorem tailTrace_5764590 : CollatzResearch.WordTrace tailWord_5764590 prefixEnd_5764590 2960005446101706248814139 := by
  unfold tailWord_5764590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281483773235302304497403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140167913457254945623986149 26281483773235302304497403)
  ·
    refine ⟨39422225659852953456746105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26281483773235302304497403 39422225659852953456746105)
    ·
      refine ⟨29566669244889715092559579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39422225659852953456746105 29566669244889715092559579)
      ·
        refine ⟨44350003867334572638839369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29566669244889715092559579 44350003867334572638839369)
        ·
          refine ⟨33262502900500929479129527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44350003867334572638839369 33262502900500929479129527)
          ·
            refine ⟨49893754350751394218694291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33262502900500929479129527 49893754350751394218694291)
            ·
              refine ⟨74840631526127091328041437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49893754350751394218694291 74840631526127091328041437)
              ·
                refine ⟨28065236822297659248015539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74840631526127091328041437 28065236822297659248015539)
                ·
                  refine ⟨42097855233446488872023309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28065236822297659248015539 42097855233446488872023309)
                  ·
                    refine ⟨15786695712542433327008741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42097855233446488872023309 15786695712542433327008741)
                    ·
                      refine ⟨2960005446101706248814139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15786695712542433327008741 2960005446101706248814139)
                      ·
                        rfl

theorem cell23_5764590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_5764590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764590 prefixEnd_5764590 := by exact prefixLift 5764590
  have htrace : WordTrace (prefixWord ++ tailWord_5764590) baseStart_5764590 baseEnd_5764590 := by
    simpa [prefixWord, tailWord_5764590, baseEnd_5764590] using wordTrace_append hprefix tailTrace_5764590
  have hstable : (prefixWord ++ tailWord_5764590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764590).length < 2 ^ (prefixWord ++ tailWord_5764590).sum := by decide
  have hdescent : baseEnd_5764590 < baseStart_5764590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764603 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_5764603 : Nat := 118140960795 + 5764603 * 2 ^ 59
def prefixEnd_5764603 : Nat := 4983230072969 + 3 ^ 40 * 5764603 * 2
def baseEnd_5764603 : Nat := 2960012121350214697951579

theorem tailTrace_5764603 : CollatzResearch.WordTrace tailWord_5764603 prefixEnd_5764603 2960012121350214697951579 := by
  unfold tailWord_5764603
  simp only [CollatzResearch.WordTrace]
  refine ⟨210252344334835321656202463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140168229556556881104134975 210252344334835321656202463)
  ·
    refine ⟨315378516502252982484303695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210252344334835321656202463 315378516502252982484303695)
    ·
      refine ⟨473067774753379473726455543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315378516502252982484303695 473067774753379473726455543)
      ·
        refine ⟨709601662130069210589683315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473067774753379473726455543 709601662130069210589683315)
        ·
          refine ⟨1064402493195103815884524973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709601662130069210589683315 1064402493195103815884524973)
          ·
            refine ⟨399150934948163930956696865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1064402493195103815884524973 399150934948163930956696865)
            ·
              refine ⟨299363201211122948217522649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399150934948163930956696865 299363201211122948217522649)
              ·
                refine ⟨224522400908342211163141987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299363201211122948217522649 224522400908342211163141987)
                ·
                  refine ⟨336783601362513316744712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224522400908342211163141987 336783601362513316744712981)
                  ·
                    refine ⟨15786731313867811722408421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 336783601362513316744712981 15786731313867811722408421)
                    ·
                      refine ⟨2960012121350214697951579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15786731313867811722408421 2960012121350214697951579)
                      ·
                        rfl

theorem cell23_5764603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_5764603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764603 prefixEnd_5764603 := by exact prefixLift 5764603
  have htrace : WordTrace (prefixWord ++ tailWord_5764603) baseStart_5764603 baseEnd_5764603 := by
    simpa [prefixWord, tailWord_5764603, baseEnd_5764603] using wordTrace_append hprefix tailTrace_5764603
  have hstable : (prefixWord ++ tailWord_5764603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764603).length < 2 ^ (prefixWord ++ tailWord_5764603).sum := by decide
  have hdescent : baseEnd_5764603 < baseStart_5764603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764638 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5764638 : Nat := 118140960795 + 5764638 * 2 ^ 59
def prefixEnd_5764638 : Nat := 4983230072969 + 3 ^ 40 * 5764638 * 2
def baseEnd_5764638 : Nat := 986676697724374020337973

theorem tailTrace_5764638 : CollatzResearch.WordTrace tailWord_5764638 prefixEnd_5764638 986676697724374020337973 := by
  unfold tailWord_5764638
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281702611213565329215821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140169080593139015089151045 26281702611213565329215821)
  ·
    refine ⟨9855638479205086998455933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26281702611213565329215821 9855638479205086998455933)
    ·
      refine ⟨3695864429701907624420975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9855638479205086998455933 3695864429701907624420975)
      ·
        refine ⟨5543796644552861436631463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695864429701907624420975 5543796644552861436631463)
        ·
          refine ⟨8315694966829292154947195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543796644552861436631463 8315694966829292154947195)
          ·
            refine ⟨12473542450243938232420793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315694966829292154947195 12473542450243938232420793)
            ·
              refine ⟨9355156837682953674315595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12473542450243938232420793 9355156837682953674315595)
              ·
                refine ⟨14032735256524430511473393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355156837682953674315595 14032735256524430511473393)
                ·
                  refine ⟨10524551442393322883605045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14032735256524430511473393 10524551442393322883605045)
                  ·
                    refine ⟨986676697724374020337973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10524551442393322883605045 986676697724374020337973)
                    ·
                      rfl

theorem cell23_5764638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5764638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764638 prefixEnd_5764638 := by exact prefixLift 5764638
  have htrace : WordTrace (prefixWord ++ tailWord_5764638) baseStart_5764638 baseEnd_5764638 := by
    simpa [prefixWord, tailWord_5764638, baseEnd_5764638] using wordTrace_append hprefix tailTrace_5764638
  have hstable : (prefixWord ++ tailWord_5764638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764638).length < 2 ^ (prefixWord ++ tailWord_5764638).sum := by decide
  have hdescent : baseEnd_5764638 < baseStart_5764638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764668 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_5764668 : Nat := 118140960795 + 5764668 * 2 ^ 59
def prefixEnd_5764668 : Nat := 4983230072969 + 3 ^ 40 * 5764668 * 2
def baseEnd_5764668 : Nat := 986681832530918981212927

theorem tailTrace_5764668 : CollatzResearch.WordTrace tailWord_5764668 prefixEnd_5764668 986681832530918981212927 := by
  unfold tailWord_5764668
  simp only [CollatzResearch.WordTrace]
  refine ⟨105127357539799918878659329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140169810053066558504879105 105127357539799918878659329)
  ·
    refine ⟨78845518154849939158994497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105127357539799918878659329 78845518154849939158994497)
    ·
      refine ⟨59134138616137454369245873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78845518154849939158994497 59134138616137454369245873)
      ·
        refine ⟨44350603962103090776934405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59134138616137454369245873 44350603962103090776934405)
        ·
          refine ⟨8315738242894329520675201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44350603962103090776934405 8315738242894329520675201)
          ·
            refine ⟨6236803682170747140506401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8315738242894329520675201 6236803682170747140506401)
            ·
              refine ⟨4677602761628060355379801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236803682170747140506401 4677602761628060355379801)
              ·
                refine ⟨3508202071221045266534851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4677602761628060355379801 3508202071221045266534851)
                ·
                  refine ⟨5262303106831567899802277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508202071221045266534851 5262303106831567899802277)
                  ·
                    refine ⟨986681832530918981212927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262303106831567899802277 986681832530918981212927)
                    ·
                      rfl

theorem cell23_5764668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_5764668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764668 prefixEnd_5764668 := by exact prefixLift 5764668
  have htrace : WordTrace (prefixWord ++ tailWord_5764668) baseStart_5764668 baseEnd_5764668 := by
    simpa [prefixWord, tailWord_5764668, baseEnd_5764668] using wordTrace_append hprefix tailTrace_5764668
  have hstable : (prefixWord ++ tailWord_5764668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764668).length < 2 ^ (prefixWord ++ tailWord_5764668).sum := by decide
  have hdescent : baseEnd_5764668 < baseStart_5764668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764714 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5764714 : Nat := 118140960795 + 5764714 * 2 ^ 59
def prefixEnd_5764714 : Nat := 4983230072969 + 3 ^ 40 * 5764714 * 2
def baseEnd_5764714 : Nat := 2960069117702863763663569

theorem tailTrace_5764714 : CollatzResearch.WordTrace tailWord_5764714 prefixEnd_5764714 2960069117702863763663569 := by
  unfold tailWord_5764714
  simp only [CollatzResearch.WordTrace]
  refine ⟨52564098209358296903373299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140170928558288791742328797 52564098209358296903373299)
  ·
    refine ⟨78846147314037445355059949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52564098209358296903373299 78846147314037445355059949)
    ·
      refine ⟨29567305242764042008147481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78846147314037445355059949 29567305242764042008147481)
      ·
        refine ⟨22175478932073031506110611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29567305242764042008147481 22175478932073031506110611)
        ·
          refine ⟨33263218398109547259165917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22175478932073031506110611 33263218398109547259165917)
          ·
            refine ⟨12473706899291080222187219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33263218398109547259165917 12473706899291080222187219)
            ·
              refine ⟨18710560348936620333280829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12473706899291080222187219 18710560348936620333280829)
              ·
                refine ⟨7016460130851232624980311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18710560348936620333280829 7016460130851232624980311)
                ·
                  refine ⟨10524690196276848937470467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016460130851232624980311 10524690196276848937470467)
                  ·
                    refine ⟨15787035294415273406205701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10524690196276848937470467 15787035294415273406205701)
                    ·
                      refine ⟨2960069117702863763663569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15787035294415273406205701 2960069117702863763663569)
                      ·
                        rfl

theorem cell23_5764714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5764714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764714 prefixEnd_5764714 := by exact prefixLift 5764714
  have htrace : WordTrace (prefixWord ++ tailWord_5764714) baseStart_5764714 baseEnd_5764714 := by
    simpa [prefixWord, tailWord_5764714, baseEnd_5764714] using wordTrace_append hprefix tailTrace_5764714
  have hstable : (prefixWord ++ tailWord_5764714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764714).length < 2 ^ (prefixWord ++ tailWord_5764714).sum := by decide
  have hdescent : baseEnd_5764714 < baseStart_5764714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764720 : List Nat := [2, 1, 1, 1, 6, 2, 10]
def baseStart_5764720 : Nat := 118140960795 + 5764720 * 2 ^ 59
def prefixEnd_5764720 : Nat := 4983230072969 + 3 ^ 40 * 5764720 * 2
def baseEnd_5764720 : Nat := 36544101217120873335661

theorem tailTrace_5764720 : CollatzResearch.WordTrace tailWord_5764720 prefixEnd_5764720 36544101217120873335661 := by
  unfold tailWord_5764720
  simp only [CollatzResearch.WordTrace]
  refine ⟨105128305837705725319105807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140171074450274300425474409 105128305837705725319105807)
  ·
    refine ⟨157692458756558587978658711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105128305837705725319105807 157692458756558587978658711)
    ·
      refine ⟨236538688134837881967988067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157692458756558587978658711 236538688134837881967988067)
      ·
        refine ⟨354808032202256822951982101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236538688134837881967988067 354808032202256822951982101)
        ·
          refine ⟨16631626509480788575874161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 354808032202256822951982101 16631626509480788575874161)
          ·
            refine ⟨12473719882110591431905621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16631626509480788575874161 12473719882110591431905621)
            ·
              refine ⟨36544101217120873335661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12473719882110591431905621 36544101217120873335661)
              ·
                rfl

theorem cell23_5764720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 10].length) (baseStart_5764720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764720 prefixEnd_5764720 := by exact prefixLift 5764720
  have htrace : WordTrace (prefixWord ++ tailWord_5764720) baseStart_5764720 baseEnd_5764720 := by
    simpa [prefixWord, tailWord_5764720, baseEnd_5764720] using wordTrace_append hprefix tailTrace_5764720
  have hstable : (prefixWord ++ tailWord_5764720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764720).length < 2 ^ (prefixWord ++ tailWord_5764720).sum := by decide
  have hdescent : baseEnd_5764720 < baseStart_5764720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764731 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 1, 2, 2]
def baseStart_5764731 : Nat := 118140960795 + 5764731 * 2 ^ 59
def prefixEnd_5764731 : Nat := 4983230072969 + 3 ^ 40 * 5764731 * 2
def baseEnd_5764731 : Nat := 2960077846873990197150991

theorem tailTrace_5764731 : CollatzResearch.WordTrace tailWord_5764731 prefixEnd_5764731 2960077846873990197150991 := by
  unfold tailWord_5764731
  simp only [CollatzResearch.WordTrace]
  refine ⟨210257012878371599516862047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140171341918914399677908031 210257012878371599516862047)
  ·
    refine ⟨315385519317557399275293071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210257012878371599516862047 315385519317557399275293071)
    ·
      refine ⟨473078278976336098912939607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315385519317557399275293071 473078278976336098912939607)
      ·
        refine ⟨709617418464504148369409411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473078278976336098912939607 709617418464504148369409411)
        ·
          refine ⟨1064426127696756222554114117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709617418464504148369409411 1064426127696756222554114117)
          ·
            refine ⟨199579898943141791728896397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1064426127696756222554114117 199579898943141791728896397)
            ·
              refine ⟨74842462103678171898336149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199579898943141791728896397 74842462103678171898336149)
              ·
                refine ⟨3508240411109914307734507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74842462103678171898336149 3508240411109914307734507)
                ·
                  refine ⟨5262360616664871461601761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508240411109914307734507 5262360616664871461601761)
                  ·
                    refine ⟨3946770462498653596201321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5262360616664871461601761 3946770462498653596201321)
                    ·
                      refine ⟨2960077846873990197150991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946770462498653596201321 2960077846873990197150991)
                      ·
                        rfl

theorem cell23_5764731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 2, 2].length) (baseStart_5764731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764731 prefixEnd_5764731 := by exact prefixLift 5764731
  have htrace : WordTrace (prefixWord ++ tailWord_5764731) baseStart_5764731 baseEnd_5764731 := by
    simpa [prefixWord, tailWord_5764731, baseEnd_5764731] using wordTrace_append hprefix tailTrace_5764731
  have hstable : (prefixWord ++ tailWord_5764731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764731).length < 2 ^ (prefixWord ++ tailWord_5764731).sum := by decide
  have hdescent : baseEnd_5764731 < baseStart_5764731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764744 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5764744 : Nat := 118140960795 + 5764744 * 2 ^ 59
def prefixEnd_5764744 : Nat := 4983230072969 + 3 ^ 40 * 5764744 * 2
def baseEnd_5764744 : Nat := 2960084522122498646288431

theorem tailTrace_5764744 : CollatzResearch.WordTrace tailWord_5764744 prefixEnd_5764744 2960084522122498646288431 := by
  unfold tailWord_5764744
  simp only [CollatzResearch.WordTrace]
  refine ⟨105128743513662251368542643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140171658018216335158056857 105128743513662251368542643)
  ·
    refine ⟨157693115270493377052813965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105128743513662251368542643 157693115270493377052813965)
    ·
      refine ⟨59134918226435016394805237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157693115270493377052813965 59134918226435016394805237)
      ·
        refine ⟨5543898583728282787012991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59134918226435016394805237 5543898583728282787012991)
        ·
          refine ⟨8315847875592424180519487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543898583728282787012991 8315847875592424180519487)
          ·
            refine ⟨12473771813388636270779231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8315847875592424180519487 12473771813388636270779231)
            ·
              refine ⟨18710657720082954406168847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12473771813388636270779231 18710657720082954406168847)
              ·
                refine ⟨28065986580124431609253271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18710657720082954406168847 28065986580124431609253271)
                ·
                  refine ⟨42098979870186647413879907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28065986580124431609253271 42098979870186647413879907)
                  ·
                    refine ⟨63148469805279971120819861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42098979870186647413879907 63148469805279971120819861)
                    ·
                      refine ⟨2960084522122498646288431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63148469805279971120819861 2960084522122498646288431)
                      ·
                        rfl

theorem cell23_5764744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5764744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764744 prefixEnd_5764744 := by exact prefixLift 5764744
  have htrace : WordTrace (prefixWord ++ tailWord_5764744) baseStart_5764744 baseEnd_5764744 := by
    simpa [prefixWord, tailWord_5764744, baseEnd_5764744] using wordTrace_append hprefix tailTrace_5764744
  have hstable : (prefixWord ++ tailWord_5764744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764744).length < 2 ^ (prefixWord ++ tailWord_5764744).sum := by decide
  have hdescent : baseEnd_5764744 < baseStart_5764744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764757 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 7, 2]
def baseStart_5764757 : Nat := 118140960795 + 5764757 * 2 ^ 59
def prefixEnd_5764757 : Nat := 4983230072969 + 3 ^ 40 * 5764757 * 2
def baseEnd_5764757 : Nat := 2960091197371007095425871

theorem tailTrace_5764757 : CollatzResearch.WordTrace tailWord_5764757 prefixEnd_5764757 2960091197371007095425871 := by
  unfold tailWord_5764757
  simp only [CollatzResearch.WordTrace]
  refine ⟨210257961176277405957308525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140171974117518270638205683 210257961176277405957308525)
  ·
    refine ⟨78846735441104027233990697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210257961176277405957308525 78846735441104027233990697)
    ·
      refine ⟨59135051580828020425493023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78846735441104027233990697 59135051580828020425493023)
      ·
        refine ⟨88702577371242030638239535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59135051580828020425493023 88702577371242030638239535)
        ·
          refine ⟨133053866056863045957359303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88702577371242030638239535 133053866056863045957359303)
          ·
            refine ⟨199580799085294568936038955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133053866056863045957359303 199580799085294568936038955)
            ·
              refine ⟨299371198627941853404058433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199580799085294568936038955 299371198627941853404058433)
              ·
                refine ⟨224528398970956390053043825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299371198627941853404058433 224528398970956390053043825)
                ·
                  refine ⟨168396299228217292539782869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224528398970956390053043825 168396299228217292539782869)
                  ·
                    refine ⟨3946788263161342793901161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168396299228217292539782869 3946788263161342793901161)
                    ·
                      refine ⟨2960091197371007095425871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946788263161342793901161 2960091197371007095425871)
                      ·
                        rfl

theorem cell23_5764757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_5764757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764757 prefixEnd_5764757 := by exact prefixLift 5764757
  have htrace : WordTrace (prefixWord ++ tailWord_5764757) baseStart_5764757 baseEnd_5764757 := by
    simpa [prefixWord, tailWord_5764757, baseEnd_5764757] using wordTrace_append hprefix tailTrace_5764757
  have hstable : (prefixWord ++ tailWord_5764757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764757).length < 2 ^ (prefixWord ++ tailWord_5764757).sum := by decide
  have hdescent : baseEnd_5764757 < baseStart_5764757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764781 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_5764781 : Nat := 118140960795 + 5764781 * 2 ^ 59
def prefixEnd_5764781 : Nat := 4983230072969 + 3 ^ 40 * 5764781 * 2
def baseEnd_5764781 : Nat := 2960103520906715001525761

theorem tailTrace_5764781 : CollatzResearch.WordTrace tailWord_5764781 prefixEnd_5764781 2960103520906715001525761 := by
  unfold tailWord_5764781
  simp only [CollatzResearch.WordTrace]
  refine ⟨210258836528190458056182197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140172557685460305370788131 210258836528190458056182197)
  ·
    refine ⟨19711765924517855442767081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210258836528190458056182197 19711765924517855442767081)
    ·
      refine ⟨14783824443388391582075311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19711765924517855442767081 14783824443388391582075311)
      ·
        refine ⟨22175736665082587373112967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14783824443388391582075311 22175736665082587373112967)
        ·
          refine ⟨33263604997623881059669451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22175736665082587373112967 33263604997623881059669451)
          ·
            refine ⟨49895407496435821589504177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33263604997623881059669451 49895407496435821589504177)
            ·
              refine ⟨37421555622326866192128133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49895407496435821589504177 37421555622326866192128133)
              ·
                refine ⟨7016541679186287411024025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37421555622326866192128133 7016541679186287411024025)
                ·
                  refine ⟨5262406259389715558268019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7016541679186287411024025 5262406259389715558268019)
                  ·
                    refine ⟨7893609389084573337402029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262406259389715558268019 7893609389084573337402029)
                    ·
                      refine ⟨2960103520906715001525761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893609389084573337402029 2960103520906715001525761)
                      ·
                        rfl

theorem cell23_5764781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_5764781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764781 prefixEnd_5764781 := by exact prefixLift 5764781
  have htrace : WordTrace (prefixWord ++ tailWord_5764781) baseStart_5764781 baseEnd_5764781 := by
    simpa [prefixWord, tailWord_5764781, baseEnd_5764781] using wordTrace_append hprefix tailTrace_5764781
  have hstable : (prefixWord ++ tailWord_5764781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764781).length < 2 ^ (prefixWord ++ tailWord_5764781).sum := by decide
  have hdescent : baseEnd_5764781 < baseStart_5764781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764782 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5764782 : Nat := 118140960795 + 5764782 * 2 ^ 59
def prefixEnd_5764782 : Nat := 4983230072969 + 3 ^ 40 * 5764782 * 2
def baseEnd_5764782 : Nat := 2960104034387369497613257

theorem tailTrace_5764782 : CollatzResearch.WordTrace tailWord_5764782 prefixEnd_5764782 2960104034387369497613257 := by
  unfold tailWord_5764782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282359125148354403371075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140172582000791223484645733 26282359125148354403371075)
  ·
    refine ⟨39423538687722531605056613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26282359125148354403371075 39423538687722531605056613)
    ·
      refine ⟨7391913503947974675948115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39423538687722531605056613 7391913503947974675948115)
      ·
        refine ⟨11087870255921962013922173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391913503947974675948115 11087870255921962013922173)
        ·
          refine ⟨4157951345970735755220815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11087870255921962013922173 4157951345970735755220815)
          ·
            refine ⟨6236927018956103632831223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157951345970735755220815 6236927018956103632831223)
            ·
              refine ⟨9355390528434155449246835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236927018956103632831223 9355390528434155449246835)
              ·
                refine ⟨14033085792651233173870253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9355390528434155449246835 14033085792651233173870253)
                ·
                  refine ⟨5262407172244212440201345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14033085792651233173870253 5262407172244212440201345)
                  ·
                    refine ⟨3946805379183159330151009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5262407172244212440201345 3946805379183159330151009)
                    ·
                      refine ⟨2960104034387369497613257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3946805379183159330151009 2960104034387369497613257)
                      ·
                        rfl

theorem cell23_5764782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5764782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764782 prefixEnd_5764782 := by exact prefixLift 5764782
  have htrace : WordTrace (prefixWord ++ tailWord_5764782) baseStart_5764782 baseEnd_5764782 := by
    simpa [prefixWord, tailWord_5764782, baseEnd_5764782] using wordTrace_append hprefix tailTrace_5764782
  have hstable : (prefixWord ++ tailWord_5764782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764782).length < 2 ^ (prefixWord ++ tailWord_5764782).sum := by decide
  have hdescent : baseEnd_5764782 < baseStart_5764782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5764798 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_5764798 : Nat := 118140960795 + 5764798 * 2 ^ 59
def prefixEnd_5764798 : Nat := 4983230072969 + 3 ^ 40 * 5764798 * 2
def baseEnd_5764798 : Nat := 2960112250077841435013183

theorem tailTrace_5764798 : CollatzResearch.WordTrace tailWord_5764798 prefixEnd_5764798 2960112250077841435013183 := by
  unfold tailWord_5764798
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282432071141108744943881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140172971046085913306367365 26282432071141108744943881)
  ·
    refine ⟨19711824053355831558707911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26282432071141108744943881 19711824053355831558707911)
    ·
      refine ⟨29567736080033747338061867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19711824053355831558707911 29567736080033747338061867)
      ·
        refine ⟨44351604120050621007092801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29567736080033747338061867 44351604120050621007092801)
        ·
          refine ⟨33263703090037965755319601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44351604120050621007092801 33263703090037965755319601)
          ·
            refine ⟨24947777317528474316489701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33263703090037965755319601 24947777317528474316489701)
            ·
              refine ⟨4677708247036588934341819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24947777317528474316489701 4677708247036588934341819)
              ·
                refine ⟨7016562370554883401512729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677708247036588934341819 7016562370554883401512729)
                ·
                  refine ⟨5262421777916162551134547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7016562370554883401512729 5262421777916162551134547)
                  ·
                    refine ⟨7893632666874243826701821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5262421777916162551134547 7893632666874243826701821)
                    ·
                      refine ⟨2960112250077841435013183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7893632666874243826701821 2960112250077841435013183)
                      ·
                        rfl

theorem cell23_5764798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_5764798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5764798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5764798 prefixEnd_5764798 := by exact prefixLift 5764798
  have htrace : WordTrace (prefixWord ++ tailWord_5764798) baseStart_5764798 baseEnd_5764798 := by
    simpa [prefixWord, tailWord_5764798, baseEnd_5764798] using wordTrace_append hprefix tailTrace_5764798
  have hstable : (prefixWord ++ tailWord_5764798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5764798).length < 2 ^ (prefixWord ++ tailWord_5764798).sum := by decide
  have hdescent : baseEnd_5764798 < baseStart_5764798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5764798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
