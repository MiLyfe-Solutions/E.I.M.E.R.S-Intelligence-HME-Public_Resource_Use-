import V185TrunkScan20Chunk065

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_401826 : List Nat := [3, 3, 1, 2, 1, 1, 9]
def baseStart_401826 : Nat := 118140960795 + 401826 * 2 ^ 59
def prefixEnd_401826 : Nat := 4983230072969 + 3 ^ 40 * 401826 * 2
def baseEnd_401826 : Nat := 20378259503570379024893

theorem tailTrace_401826 : CollatzResearch.WordTrace tailWord_401826 prefixEnd_401826 20378259503570379024893 := by
  unfold tailWord_401826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663949560565125815570333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9770532161507002174854221 3663949560565125815570333)
  ·
    refine ⟨1373981085211922180838875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3663949560565125815570333 1373981085211922180838875)
    ·
      refine ⟨2060971627817883271258313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373981085211922180838875 2060971627817883271258313)
      ·
        refine ⟨1545728720863412453443735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2060971627817883271258313 1545728720863412453443735)
        ·
          refine ⟨2318593081295118680165603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545728720863412453443735 2318593081295118680165603)
          ·
            refine ⟨3477889621942678020248405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318593081295118680165603 3477889621942678020248405)
            ·
              refine ⟨20378259503570379024893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3477889621942678020248405 20378259503570379024893)
              ·
                rfl

theorem cell20_401826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_401826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401826 prefixEnd_401826 := by exact prefixLift 401826
  have htrace : WordTrace (prefixWord ++ tailWord_401826) baseStart_401826 baseEnd_401826 := by
    simpa [prefixWord, tailWord_401826, baseEnd_401826] using wordTrace_append hprefix tailTrace_401826
  have hstable : (prefixWord ++ tailWord_401826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401826).length < 2 ^ (prefixWord ++ tailWord_401826).sum := by decide
  have hdescent : baseEnd_401826 < baseStart_401826 := by decide
  rcases family_descends (prefixWord ++ tailWord_401826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401864 : List Nat := [2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_401864 : Nat := 118140960795 + 401864 * 2 ^ 59
def prefixEnd_401864 : Nat := 4983230072969 + 3 ^ 40 * 401864 * 2
def baseEnd_401864 : Nat := 61140559922524722652405

theorem tailTrace_401864 : CollatzResearch.WordTrace tailWord_401864 prefixEnd_401864 61140559922524722652405 := by
  unfold tailWord_401864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328592108061417876082323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9771456144081890501443097 7328592108061417876082323)
  ·
    refine ⟨10992888162092126814123485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7328592108061417876082323 10992888162092126814123485)
    ·
      refine ⟨4122333060784547555296307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10992888162092126814123485 4122333060784547555296307)
      ·
        refine ⟨6183499591176821332944461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122333060784547555296307 6183499591176821332944461)
        ·
          refine ⟨2318812346691307999854173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6183499591176821332944461 2318812346691307999854173)
          ·
            refine ⟨869554630009240499945315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2318812346691307999854173 869554630009240499945315)
            ·
              refine ⟨1304331945013860749917973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869554630009240499945315 1304331945013860749917973)
              ·
                refine ⟨61140559922524722652405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1304331945013860749917973 61140559922524722652405)
                ·
                  rfl

theorem cell20_401864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_401864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401864 prefixEnd_401864 := by exact prefixLift 401864
  have htrace : WordTrace (prefixWord ++ tailWord_401864) baseStart_401864 baseEnd_401864 := by
    simpa [prefixWord, tailWord_401864, baseEnd_401864] using wordTrace_append hprefix tailTrace_401864
  have hstable : (prefixWord ++ tailWord_401864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401864).length < 2 ^ (prefixWord ++ tailWord_401864).sum := by decide
  have hdescent : baseEnd_401864 < baseStart_401864 := by decide
  rcases family_descends (prefixWord ++ tailWord_401864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401891 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 4]
def baseStart_401891 : Nat := 118140960795 + 401891 * 2 ^ 59
def prefixEnd_401891 : Nat := 4983230072969 + 3 ^ 40 * 401891 * 2
def baseEnd_401891 : Nat := 183434003303282074057105

theorem tailTrace_401891 : CollatzResearch.WordTrace tailWord_401891 prefixEnd_401891 183434003303282074057105 := by
  unfold tailWord_401891
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658168987025019363397527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9772112658016679575598351 14658168987025019363397527)
  ·
    refine ⟨21987253480537529045096291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14658168987025019363397527 21987253480537529045096291)
    ·
      refine ⟨32980880220806293567644437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21987253480537529045096291 32980880220806293567644437)
      ·
        refine ⟨1545978760350295010983333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32980880220806293567644437 1545978760350295010983333)
        ·
          refine ⟨289871017565680314559375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1545978760350295010983333 289871017565680314559375)
          ·
            refine ⟨434806526348520471839063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289871017565680314559375 434806526348520471839063)
            ·
              refine ⟨652209789522780707758595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434806526348520471839063 652209789522780707758595)
              ·
                refine ⟨978314684284171061637893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652209789522780707758595 978314684284171061637893)
                ·
                  refine ⟨183434003303282074057105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978314684284171061637893 183434003303282074057105)
                  ·
                    rfl

theorem cell20_401891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 4].length) (baseStart_401891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401891 prefixEnd_401891 := by exact prefixLift 401891
  have htrace : WordTrace (prefixWord ++ tailWord_401891) baseStart_401891 baseEnd_401891 := by
    simpa [prefixWord, tailWord_401891, baseEnd_401891] using wordTrace_append hprefix tailTrace_401891
  have hstable : (prefixWord ++ tailWord_401891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401891).length < 2 ^ (prefixWord ++ tailWord_401891).sum := by decide
  have hdescent : baseEnd_401891 < baseStart_401891 := by decide
  rcases family_descends (prefixWord ++ tailWord_401891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401902 : List Nat := [4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_401902 : Nat := 118140960795 + 401902 * 2 ^ 59
def prefixEnd_401902 : Nat := 4983230072969 + 3 ^ 40 * 401902 * 2
def baseEnd_401902 : Nat := 61146341334338308230131

theorem tailTrace_401902 : CollatzResearch.WordTrace tailWord_401902 prefixEnd_401902 61146341334338308230131 := by
  unfold tailWord_401902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832321273748146030255995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9772380126656778828031973 1832321273748146030255995)
  ·
    refine ⟨2748481910622219045383993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1832321273748146030255995 2748481910622219045383993)
    ·
      refine ⟨2061361432966664284037995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748481910622219045383993 2061361432966664284037995)
      ·
        refine ⟨3092042149449996426056993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061361432966664284037995 3092042149449996426056993)
        ·
          refine ⟨2319031612087497319542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092042149449996426056993 2319031612087497319542745)
          ·
            refine ⟨1739273709065622989657059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319031612087497319542745 1739273709065622989657059)
            ·
              refine ⟨2608910563598434484485589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739273709065622989657059 2608910563598434484485589)
              ·
                refine ⟨61146341334338308230131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2608910563598434484485589 61146341334338308230131)
                ·
                  rfl

theorem cell20_401902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_401902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401902 prefixEnd_401902 := by exact prefixLift 401902
  have htrace : WordTrace (prefixWord ++ tailWord_401902) baseStart_401902 baseEnd_401902 := by
    simpa [prefixWord, tailWord_401902, baseEnd_401902] using wordTrace_append hprefix tailTrace_401902
  have hstable : (prefixWord ++ tailWord_401902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401902).length < 2 ^ (prefixWord ++ tailWord_401902).sum := by decide
  have hdescent : baseEnd_401902 < baseStart_401902 := by decide
  rcases family_descends (prefixWord ++ tailWord_401902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401916 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_401916 : Nat := 118140960795 + 401916 * 2 ^ 59
def prefixEnd_401916 : Nat := 4983230072969 + 3 ^ 40 * 401916 * 2
def baseEnd_401916 : Nat := 183445413984493098223669

theorem tailTrace_401916 : CollatzResearch.WordTrace tailWord_401916 prefixEnd_401916 183445413984493098223669 := by
  unfold tailWord_401916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329540405967224316528801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9772720541289632422038401 7329540405967224316528801)
  ·
    refine ⟨5497155304475418237396601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7329540405967224316528801 5497155304475418237396601)
    ·
      refine ⟨4122866478356563678047451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5497155304475418237396601 4122866478356563678047451)
      ·
        refine ⟨6184299717534845517071177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122866478356563678047451 6184299717534845517071177)
        ·
          refine ⟨4638224788151134137803383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184299717534845517071177 4638224788151134137803383)
          ·
            refine ⟨6957337182226701206705075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638224788151134137803383 6957337182226701206705075)
            ·
              refine ⟨10436005773340051810057613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957337182226701206705075 10436005773340051810057613)
              ·
                refine ⟨3913502165002519428771605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10436005773340051810057613 3913502165002519428771605)
                ·
                  refine ⟨183445413984493098223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3913502165002519428771605 183445413984493098223669)
                  ·
                    rfl

theorem cell20_401916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_401916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401916 prefixEnd_401916 := by exact prefixLift 401916
  have htrace : WordTrace (prefixWord ++ tailWord_401916) baseStart_401916 baseEnd_401916 := by
    simpa [prefixWord, tailWord_401916, baseEnd_401916] using wordTrace_append hprefix tailTrace_401916
  have hstable : (prefixWord ++ tailWord_401916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401916).length < 2 ^ (prefixWord ++ tailWord_401916).sum := by decide
  have hdescent : baseEnd_401916 < baseStart_401916 := by decide
  rcases family_descends (prefixWord ++ tailWord_401916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401923 : List Nat := [1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_401923 : Nat := 118140960795 + 401923 * 2 ^ 59
def prefixEnd_401923 : Nat := 4983230072969 + 3 ^ 40 * 401923 * 2
def baseEnd_401923 : Nat := 61149536325077394996769

theorem tailTrace_401923 : CollatzResearch.WordTrace tailWord_401923 prefixEnd_401923 61149536325077394996769 := by
  unfold tailWord_401923
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659336122909088828562423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9772890748606059219041615 14659336122909088828562423)
  ·
    refine ⟨21989004184363633242843635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14659336122909088828562423 21989004184363633242843635)
    ·
      refine ⟨32983506276545449864265453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21989004184363633242843635 32983506276545449864265453)
      ·
        refine ⟨12368814853704543699099545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32983506276545449864265453 12368814853704543699099545)
        ·
          refine ⟨9276611140278407774324659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12368814853704543699099545 9276611140278407774324659)
          ·
            refine ⟨13914916710417611661486989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9276611140278407774324659 13914916710417611661486989)
            ·
              refine ⟨5218093766406604373057621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13914916710417611661486989 5218093766406604373057621)
              ·
                refine ⟨61149536325077394996769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5218093766406604373057621 61149536325077394996769)
                ·
                  rfl

theorem cell20_401923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_401923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401923 prefixEnd_401923 := by exact prefixLift 401923
  have htrace : WordTrace (prefixWord ++ tailWord_401923) baseStart_401923 baseEnd_401923 := by
    simpa [prefixWord, tailWord_401923, baseEnd_401923] using wordTrace_append hprefix tailTrace_401923
  have hstable : (prefixWord ++ tailWord_401923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401923).length < 2 ^ (prefixWord ++ tailWord_401923).sum := by decide
  have hdescent : baseEnd_401923 < baseStart_401923 := by decide
  rcases family_descends (prefixWord ++ tailWord_401923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401974 : List Nat := [5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_401974 : Nat := 118140960795 + 401974 * 2 ^ 59
def prefixEnd_401974 : Nat := 4983230072969 + 3 ^ 40 * 401974 * 2
def baseEnd_401974 : Nat := 61157295588300891430033

theorem tailTrace_401974 : CollatzResearch.WordTrace tailWord_401974 prefixEnd_401974 61157295588300891430033 := by
  unfold tailWord_401974
  simp only [CollatzResearch.WordTrace]
  refine ⟨916324765357770283666811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9774130830482883025779317 916324765357770283666811)
  ·
    refine ⟨1374487148036655425500217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916324765357770283666811 1374487148036655425500217)
    ·
      refine ⟨1030865361027491569125163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1374487148036655425500217 1030865361027491569125163)
      ·
        refine ⟨1546298041541237353687745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030865361027491569125163 1546298041541237353687745)
        ·
          refine ⟨1159723531155928015265809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546298041541237353687745 1159723531155928015265809)
          ·
            refine ⟨869792648366946011449357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159723531155928015265809 869792648366946011449357)
            ·
              refine ⟨326172243137604754293509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 869792648366946011449357 326172243137604754293509)
              ·
                refine ⟨61157295588300891430033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326172243137604754293509 61157295588300891430033)
                ·
                  rfl

theorem cell20_401974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_401974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401974 prefixEnd_401974 := by exact prefixLift 401974
  have htrace : WordTrace (prefixWord ++ tailWord_401974) baseStart_401974 baseEnd_401974 := by
    simpa [prefixWord, tailWord_401974, baseEnd_401974] using wordTrace_append hprefix tailTrace_401974
  have hstable : (prefixWord ++ tailWord_401974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401974).length < 2 ^ (prefixWord ++ tailWord_401974).sum := by decide
  have hdescent : baseEnd_401974 < baseStart_401974 := by decide
  rcases family_descends (prefixWord ++ tailWord_401974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 2]
def baseStart_402047 : Nat := 118140960795 + 402047 * 2 ^ 59
def prefixEnd_402047 : Nat := 4983230072969 + 3 ^ 40 * 402047 * 2
def baseEnd_402047 : Nat := 183505205954038864856467

theorem tailTrace_402047 : CollatzResearch.WordTrace tailWord_402047 prefixEnd_402047 183505205954038864856467 := by
  unfold tailWord_402047
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663858774459858006076395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9775905849639905337384263 14663858774459858006076395)
  ·
    refine ⟨21995788161689787009114593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14663858774459858006076395 21995788161689787009114593)
    ·
      refine ⟨16496841121267340256835945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21995788161689787009114593 16496841121267340256835945)
      ·
        refine ⟨12372630840950505192626959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16496841121267340256835945 12372630840950505192626959)
        ·
          refine ⟨18558946261425757788940439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372630840950505192626959 18558946261425757788940439)
          ·
            refine ⟨27838419392138636683410659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558946261425757788940439 27838419392138636683410659)
            ·
              refine ⟨41757629088207955025115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27838419392138636683410659 41757629088207955025115989)
              ·
                refine ⟨244673607938718486475289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 41757629088207955025115989 244673607938718486475289)
                ·
                  refine ⟨183505205954038864856467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244673607938718486475289 183505205954038864856467)
                  ·
                    rfl

theorem cell20_402047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2].length) (baseStart_402047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402047 prefixEnd_402047 := by exact prefixLift 402047
  have htrace : WordTrace (prefixWord ++ tailWord_402047) baseStart_402047 baseEnd_402047 := by
    simpa [prefixWord, tailWord_402047, baseEnd_402047] using wordTrace_append hprefix tailTrace_402047
  have hstable : (prefixWord ++ tailWord_402047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402047).length < 2 ^ (prefixWord ++ tailWord_402047).sum := by decide
  have hdescent : baseEnd_402047 < baseStart_402047 := by decide
  rcases family_descends (prefixWord ++ tailWord_402047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402116 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_402116 : Nat := 118140960795 + 402116 * 2 ^ 59
def prefixEnd_402116 : Nat := 4983230072969 + 3 ^ 40 * 402116 * 2
def baseEnd_402116 : Nat := 183536699434181291556185

theorem tailTrace_402116 : CollatzResearch.WordTrace tailWord_402116 prefixEnd_402116 183536699434181291556185 := by
  unfold tailWord_402116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333187705604941395169101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9777583607473255193558801 7333187705604941395169101)
  ·
    refine ⟨2749945389601853023188413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7333187705604941395169101 2749945389601853023188413)
    ·
      refine ⟨1031229521100694883695655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2749945389601853023188413 1031229521100694883695655)
      ·
        refine ⟨1546844281651042325543483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031229521100694883695655 1546844281651042325543483)
        ·
          refine ⟨2320266422476563488315225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546844281651042325543483 2320266422476563488315225)
          ·
            refine ⟨1740199816857422616236419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320266422476563488315225 1740199816857422616236419)
            ·
              refine ⟨2610299725286133924354629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740199816857422616236419 2610299725286133924354629)
              ·
                refine ⟨489431198491150110816493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2610299725286133924354629 489431198491150110816493)
                ·
                  refine ⟨183536699434181291556185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489431198491150110816493 183536699434181291556185)
                  ·
                    rfl

theorem cell20_402116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_402116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402116 prefixEnd_402116 := by exact prefixLift 402116
  have htrace : WordTrace (prefixWord ++ tailWord_402116) baseStart_402116 baseEnd_402116 := by
    simpa [prefixWord, tailWord_402116, baseEnd_402116] using wordTrace_append hprefix tailTrace_402116
  have hstable : (prefixWord ++ tailWord_402116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402116).length < 2 ^ (prefixWord ++ tailWord_402116).sum := by decide
  have hdescent : baseEnd_402116 < baseStart_402116 := by decide
  rcases family_descends (prefixWord ++ tailWord_402116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402137 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_402137 : Nat := 118140960795 + 402137 * 2 ^ 59
def prefixEnd_402137 : Nat := 4983230072969 + 3 ^ 40 * 402137 * 2
def baseEnd_402137 : Nat := 183546284406398551856099

theorem tailTrace_402137 : CollatzResearch.WordTrace tailWord_402137 prefixEnd_402137 183546284406398551856099 := by
  unfold tailWord_402137
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667141344133803376852665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9778094229422535584568443 14667141344133803376852665)
  ·
    refine ⟨11000356008100352532639499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14667141344133803376852665 11000356008100352532639499)
    ·
      refine ⟨16500534012150528798959249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11000356008100352532639499 16500534012150528798959249)
      ·
        refine ⟨12375400509112896599219437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16500534012150528798959249 12375400509112896599219437)
        ·
          refine ⟨4640775190917336224707289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12375400509112896599219437 4640775190917336224707289)
          ·
            refine ⟨3480581393188002168530467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640775190917336224707289 3480581393188002168530467)
            ·
              refine ⟨5220872089782003252795701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480581393188002168530467 5220872089782003252795701)
              ·
                refine ⟨489456758417062804949597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5220872089782003252795701 489456758417062804949597)
                ·
                  refine ⟨183546284406398551856099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489456758417062804949597 183546284406398551856099)
                  ·
                    rfl

theorem cell20_402137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_402137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402137 prefixEnd_402137 := by exact prefixLift 402137
  have htrace : WordTrace (prefixWord ++ tailWord_402137) baseStart_402137 baseEnd_402137 := by
    simpa [prefixWord, tailWord_402137, baseEnd_402137] using wordTrace_append hprefix tailTrace_402137
  have hstable : (prefixWord ++ tailWord_402137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402137).length < 2 ^ (prefixWord ++ tailWord_402137).sum := by decide
  have hdescent : baseEnd_402137 < baseStart_402137 := by decide
  rcases family_descends (prefixWord ++ tailWord_402137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402140 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_402140 : Nat := 118140960795 + 402140 * 2 ^ 59
def prefixEnd_402140 : Nat := 4983230072969 + 3 ^ 40 * 402140 * 2
def baseEnd_402140 : Nat := 183547653688143874756087

theorem tailTrace_402140 : CollatzResearch.WordTrace tailWord_402140 prefixEnd_402140 183547653688143874756087 := by
  unfold tailWord_402140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333625381561467444605937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9778167175415289926141249 7333625381561467444605937)
  ·
    refine ⟨5500219036171100583454453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7333625381561467444605937 5500219036171100583454453)
    ·
      refine ⟨515645534641040679698855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5500219036171100583454453 515645534641040679698855)
      ·
        refine ⟨773468301961561019548283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515645534641040679698855 773468301961561019548283)
        ·
          refine ⟨1160202452942341529322425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773468301961561019548283 1160202452942341529322425)
          ·
            refine ⟨870151839706756146991819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160202452942341529322425 870151839706756146991819)
            ·
              refine ⟨1305227759560134220487729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870151839706756146991819 1305227759560134220487729)
              ·
                refine ⟨978920819670100665365797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305227759560134220487729 978920819670100665365797)
                ·
                  refine ⟨183547653688143874756087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 978920819670100665365797 183547653688143874756087)
                  ·
                    rfl

theorem cell20_402140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_402140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402140 prefixEnd_402140 := by exact prefixLift 402140
  have htrace : WordTrace (prefixWord ++ tailWord_402140) baseStart_402140 baseEnd_402140 := by
    simpa [prefixWord, tailWord_402140, baseEnd_402140] using wordTrace_append hprefix tailTrace_402140
  have hstable : (prefixWord ++ tailWord_402140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402140).length < 2 ^ (prefixWord ++ tailWord_402140).sum := by decide
  have hdescent : baseEnd_402140 < baseStart_402140 := by decide
  rcases family_descends (prefixWord ++ tailWord_402140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402147 : List Nat := [1, 1, 1, 7, 1, 2, 3, 4]
def baseStart_402147 : Nat := 118140960795 + 402147 * 2 ^ 59
def prefixEnd_402147 : Nat := 4983230072969 + 3 ^ 40 * 402147 * 2
def baseEnd_402147 : Nat := 61183616226294320507575

theorem tailTrace_402147 : CollatzResearch.WordTrace tailWord_402147 prefixEnd_402147 61183616226294320507575 := by
  unfold tailWord_402147
  simp only [CollatzResearch.WordTrace]
  refine ⟨14667506074097575084716695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9778337382731716723144463 14667506074097575084716695)
  ·
    refine ⟨22001259111146362627075043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14667506074097575084716695 22001259111146362627075043)
    ·
      refine ⟨33001888666719543940612565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22001259111146362627075043 33001888666719543940612565)
      ·
        refine ⟨773481765626239311108107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33001888666719543940612565 773481765626239311108107)
        ·
          refine ⟨1160222648439358966662161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773481765626239311108107 1160222648439358966662161)
          ·
            refine ⟨870166986329519224996621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160222648439358966662161 870166986329519224996621)
            ·
              refine ⟨326312619873569709373733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870166986329519224996621 326312619873569709373733)
              ·
                refine ⟨61183616226294320507575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326312619873569709373733 61183616226294320507575)
                ·
                  rfl

theorem cell20_402147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_402147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402147 prefixEnd_402147 := by exact prefixLift 402147
  have htrace : WordTrace (prefixWord ++ tailWord_402147) baseStart_402147 baseEnd_402147 := by
    simpa [prefixWord, tailWord_402147, baseEnd_402147] using wordTrace_append hprefix tailTrace_402147
  have hstable : (prefixWord ++ tailWord_402147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402147).length < 2 ^ (prefixWord ++ tailWord_402147).sum := by decide
  have hdescent : baseEnd_402147 < baseStart_402147 := by decide
  rcases family_descends (prefixWord ++ tailWord_402147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402164 : List Nat := [2, 6, 1, 1, 2, 1, 7]
def baseStart_402164 : Nat := 118140960795 + 402164 * 2 ^ 59
def prefixEnd_402164 : Nat := 4983230072969 + 3 ^ 40 * 402164 * 2
def baseEnd_402164 : Nat := 20395400882456273106221

theorem tailTrace_402164 : CollatzResearch.WordTrace tailWord_402164 prefixEnd_402164 20395400882456273106221 := by
  unfold tailWord_402164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334063057517993494042773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9778750743357324658723697 7334063057517993494042773)
  ·
    refine ⟨343784205821155945033255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7334063057517993494042773 343784205821155945033255)
    ·
      refine ⟨515676308731733917549883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343784205821155945033255 515676308731733917549883)
      ·
        refine ⟨773514463097600876324825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515676308731733917549883 773514463097600876324825)
        ·
          refine ⟨580135847323200657243619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773514463097600876324825 580135847323200657243619)
          ·
            refine ⟨870203770984800985865429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580135847323200657243619 870203770984800985865429)
            ·
              refine ⟨20395400882456273106221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 870203770984800985865429 20395400882456273106221)
              ·
                rfl

theorem cell20_402164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_402164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402164 prefixEnd_402164 := by exact prefixLift 402164
  have htrace : WordTrace (prefixWord ++ tailWord_402164) baseStart_402164 baseEnd_402164 := by
    simpa [prefixWord, tailWord_402164, baseEnd_402164] using wordTrace_append hprefix tailTrace_402164
  have hstable : (prefixWord ++ tailWord_402164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402164).length < 2 ^ (prefixWord ++ tailWord_402164).sum := by decide
  have hdescent : baseEnd_402164 < baseStart_402164 := by decide
  rcases family_descends (prefixWord ++ tailWord_402164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402178 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_402178 : Nat := 118140960795 + 402178 * 2 ^ 59
def prefixEnd_402178 : Nat := 4983230072969 + 3 ^ 40 * 402178 * 2
def baseEnd_402178 : Nat := 183564997923584631489265

theorem tailTrace_402178 : CollatzResearch.WordTrace tailWord_402178 prefixEnd_402178 183564997923584631489265 := by
  unfold tailWord_402178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3667159184246316844773797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9779091157990178252730125 3667159184246316844773797)
  ·
    refine ⟨687592347046184408395087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3667159184246316844773797 687592347046184408395087)
    ·
      refine ⟨1031388520569276612592631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687592347046184408395087 1031388520569276612592631)
      ·
        refine ⟨1547082780853914918888947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031388520569276612592631 1547082780853914918888947)
        ·
          refine ⟨2320624171280872378333421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547082780853914918888947 2320624171280872378333421)
          ·
            refine ⟨870234064230327141875033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2320624171280872378333421 870234064230327141875033)
            ·
              refine ⟨652675548172745356406275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870234064230327141875033 652675548172745356406275)
              ·
                refine ⟨979013322259118034609413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652675548172745356406275 979013322259118034609413)
                ·
                  refine ⟨183564997923584631489265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 979013322259118034609413 183564997923584631489265)
                  ·
                    rfl

theorem cell20_402178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_402178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402178 prefixEnd_402178 := by exact prefixLift 402178
  have htrace : WordTrace (prefixWord ++ tailWord_402178) baseStart_402178 baseEnd_402178 := by
    simpa [prefixWord, tailWord_402178, baseEnd_402178] using wordTrace_append hprefix tailTrace_402178
  have hstable : (prefixWord ++ tailWord_402178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402178).length < 2 ^ (prefixWord ++ tailWord_402178).sum := by decide
  have hdescent : baseEnd_402178 < baseStart_402178 := by decide
  rcases family_descends (prefixWord ++ tailWord_402178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402212 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_402212 : Nat := 118140960795 + 402212 * 2 ^ 59
def prefixEnd_402212 : Nat := 4983230072969 + 3 ^ 40 * 402212 * 2
def baseEnd_402212 : Nat := 183580516450031624355793

theorem tailTrace_402212 : CollatzResearch.WordTrace tailWord_402212 prefixEnd_402212 183580516450031624355793 := by
  unfold tailWord_402212
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334938409431045592916445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9779917879241394123888593 7334938409431045592916445)
  ·
    refine ⟨2750601903536642097343667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7334938409431045592916445 2750601903536642097343667)
    ·
      refine ⟨4125902855304963146015501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750601903536642097343667 4125902855304963146015501)
      ·
        refine ⟨1547213570739361179755813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4125902855304963146015501 1547213570739361179755813)
        ·
          refine ⟨290102544513630221204215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1547213570739361179755813 290102544513630221204215)
          ·
            refine ⟨435153816770445331806323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290102544513630221204215 435153816770445331806323)
            ·
              refine ⟨652730725155667997709485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435153816770445331806323 652730725155667997709485)
              ·
                refine ⟨244774021933375499141057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652730725155667997709485 244774021933375499141057)
                ·
                  refine ⟨183580516450031624355793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244774021933375499141057 183580516450031624355793)
                  ·
                    rfl

theorem cell20_402212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_402212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402212 prefixEnd_402212 := by exact prefixLift 402212
  have htrace : WordTrace (prefixWord ++ tailWord_402212) baseStart_402212 baseEnd_402212 := by
    simpa [prefixWord, tailWord_402212, baseEnd_402212] using wordTrace_append hprefix tailTrace_402212
  have hstable : (prefixWord ++ tailWord_402212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402212).length < 2 ^ (prefixWord ++ tailWord_402212).sum := by decide
  have hdescent : baseEnd_402212 < baseStart_402212 := by decide
  rcases family_descends (prefixWord ++ tailWord_402212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402227 : List Nat := [1, 1, 1, 2, 6, 1, 8]
def baseStart_402227 : Nat := 118140960795 + 402227 * 2 ^ 59
def prefixEnd_402227 : Nat := 4983230072969 + 3 ^ 40 * 402227 * 2
def baseEnd_402227 : Nat := 20398595873195359872859

theorem tailTrace_402227 : CollatzResearch.WordTrace tailWord_402227 prefixEnd_402227 20398595873195359872859 := by
  unfold tailWord_402227
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670423913807748747628935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9780282609205165831752623 14670423913807748747628935)
  ·
    refine ⟨22005635870711623121443403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14670423913807748747628935 22005635870711623121443403)
    ·
      refine ⟨33008453806067434682165105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22005635870711623121443403 33008453806067434682165105)
      ·
        refine ⟨24756340354550576011623829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33008453806067434682165105 24756340354550576011623829)
        ·
          refine ⟨1160453454119558250544867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24756340354550576011623829 1160453454119558250544867)
          ·
            refine ⟨1740680181179337375817301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160453454119558250544867 1740680181179337375817301)
            ·
              refine ⟨20398595873195359872859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1740680181179337375817301 20398595873195359872859)
              ·
                rfl

theorem cell20_402227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_402227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402227 prefixEnd_402227 := by exact prefixLift 402227
  have htrace : WordTrace (prefixWord ++ tailWord_402227) baseStart_402227 baseEnd_402227 := by
    simpa [prefixWord, tailWord_402227, baseEnd_402227] using wordTrace_append hprefix tailTrace_402227
  have hstable : (prefixWord ++ tailWord_402227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402227).length < 2 ^ (prefixWord ++ tailWord_402227).sum := by decide
  have hdescent : baseEnd_402227 < baseStart_402227 := by decide
  rcases family_descends (prefixWord ++ tailWord_402227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402258 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_402258 : Nat := 118140960795 + 402258 * 2 ^ 59
def prefixEnd_402258 : Nat := 4983230072969 + 3 ^ 40 * 402258 * 2
def baseEnd_402258 : Nat := 183601512103459908822271

theorem tailTrace_402258 : CollatzResearch.WordTrace tailWord_402258 prefixEnd_402258 183601512103459908822271 := by
  unfold tailWord_402258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3667888644173860260501857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9781036384463627361338285 3667888644173860260501857)
  ·
    refine ⟨2750916483130395195376393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3667888644173860260501857 2750916483130395195376393)
    ·
      refine ⟨2063187362347796396532295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2750916483130395195376393 2063187362347796396532295)
      ·
        refine ⟨3094781043521694594798443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063187362347796396532295 3094781043521694594798443)
        ·
          refine ⟨4642171565282541892197665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094781043521694594798443 4642171565282541892197665)
          ·
            refine ⟨3481628673961906419148249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4642171565282541892197665 3481628673961906419148249)
            ·
              refine ⟨2611221505471429814361187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481628673961906419148249 2611221505471429814361187)
              ·
                refine ⟨3916832258207144721541781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611221505471429814361187 3916832258207144721541781)
                ·
                  refine ⟨183601512103459908822271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3916832258207144721541781 183601512103459908822271)
                  ·
                    rfl

theorem cell20_402258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_402258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402258 prefixEnd_402258 := by exact prefixLift 402258
  have htrace : WordTrace (prefixWord ++ tailWord_402258) baseStart_402258 baseEnd_402258 := by
    simpa [prefixWord, tailWord_402258, baseEnd_402258] using wordTrace_append hprefix tailTrace_402258
  have hstable : (prefixWord ++ tailWord_402258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402258).length < 2 ^ (prefixWord ++ tailWord_402258).sum := by decide
  have hdescent : baseEnd_402258 < baseStart_402258 := by decide
  rcases family_descends (prefixWord ++ tailWord_402258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402265 : List Nat := [1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_402265 : Nat := 118140960795 + 402265 * 2 ^ 59
def prefixEnd_402265 : Nat := 4983230072969 + 3 ^ 40 * 402265 * 2
def baseEnd_402265 : Nat := 61201569031399665196303

theorem tailTrace_402265 : CollatzResearch.WordTrace tailWord_402265 prefixEnd_402265 61201569031399665196303 := by
  unfold tailWord_402265
  simp only [CollatzResearch.WordTrace]
  refine ⟨14671809887670081237512249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9781206591780054158341499 14671809887670081237512249)
  ·
    refine ⟨11003857415752560928134187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14671809887670081237512249 11003857415752560928134187)
    ·
      refine ⟨16505786123628841392201281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11003857415752560928134187 16505786123628841392201281)
      ·
        refine ⟨12379339592721631044150961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16505786123628841392201281 12379339592721631044150961)
        ·
          refine ⟨9284504694541223283113221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12379339592721631044150961 9284504694541223283113221)
          ·
            refine ⟨1740844630226479365583729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9284504694541223283113221 1740844630226479365583729)
            ·
              refine ⟨1305633472669859524187797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740844630226479365583729 1305633472669859524187797)
              ·
                refine ⟨61201569031399665196303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1305633472669859524187797 61201569031399665196303)
                ·
                  rfl

theorem cell20_402265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_402265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402265 prefixEnd_402265 := by exact prefixLift 402265
  have htrace : WordTrace (prefixWord ++ tailWord_402265) baseStart_402265 baseEnd_402265 := by
    simpa [prefixWord, tailWord_402265, baseEnd_402265] using wordTrace_append hprefix tailTrace_402265
  have hstable : (prefixWord ++ tailWord_402265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402265).length < 2 ^ (prefixWord ++ tailWord_402265).sum := by decide
  have hdescent : baseEnd_402265 < baseStart_402265 := by decide
  rcases family_descends (prefixWord ++ tailWord_402265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402289 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_402289 : Nat := 118140960795 + 402289 * 2 ^ 59
def prefixEnd_402289 : Nat := 4983230072969 + 3 ^ 40 * 402289 * 2
def baseEnd_402289 : Nat := 183615661348161578788811

theorem tailTrace_402289 : CollatzResearch.WordTrace tailWord_402289 prefixEnd_402289 183615661348161578788811 := by
  unfold tailWord_402289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672685239583133336385921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9781790159722088890923947 14672685239583133336385921)
  ·
    refine ⟨11004513929687350002289441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14672685239583133336385921 11004513929687350002289441)
    ·
      refine ⟨8253385447265512501717081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11004513929687350002289441 8253385447265512501717081)
      ·
        refine ⟨6190039085449134376287811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253385447265512501717081 6190039085449134376287811)
        ·
          refine ⟨9285058628173701564431717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190039085449134376287811 9285058628173701564431717)
          ·
            refine ⟨1740948492782569043330947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9285058628173701564431717 1740948492782569043330947)
            ·
              refine ⟨2611422739173853564996421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740948492782569043330947 2611422739173853564996421)
              ·
                refine ⟨489641763595097543436829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611422739173853564996421 489641763595097543436829)
                ·
                  refine ⟨183615661348161578788811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489641763595097543436829 183615661348161578788811)
                  ·
                    rfl

theorem cell20_402289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_402289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402289 prefixEnd_402289 := by exact prefixLift 402289
  have htrace : WordTrace (prefixWord ++ tailWord_402289) baseStart_402289 baseEnd_402289 := by
    simpa [prefixWord, tailWord_402289, baseEnd_402289] using wordTrace_append hprefix tailTrace_402289
  have hstable : (prefixWord ++ tailWord_402289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402289).length < 2 ^ (prefixWord ++ tailWord_402289).sum := by decide
  have hdescent : baseEnd_402289 < baseStart_402289 := by decide
  rcases family_descends (prefixWord ++ tailWord_402289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402303 : List Nat := [1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_402303 : Nat := 118140960795 + 402303 * 2 ^ 59
def prefixEnd_402303 : Nat := 4983230072969 + 3 ^ 40 * 402303 * 2
def baseEnd_402303 : Nat := 61207350443213250774029

theorem tailTrace_402303 : CollatzResearch.WordTrace tailWord_402303 prefixEnd_402303 61207350443213250774029 := by
  unfold tailWord_402303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673195861532413727395563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9782130574354942484930375 14673195861532413727395563)
  ·
    refine ⟨22009793792298620591093345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14673195861532413727395563 22009793792298620591093345)
    ·
      refine ⟨16507345344223965443320009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22009793792298620591093345 16507345344223965443320009)
      ·
        refine ⟨12380509008167974082490007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16507345344223965443320009 12380509008167974082490007)
        ·
          refine ⟨18570763512251961123735011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12380509008167974082490007 18570763512251961123735011)
          ·
            refine ⟨27856145268377941685602517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18570763512251961123735011 27856145268377941685602517)
            ·
              refine ⟨652878404727608008256309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27856145268377941685602517 652878404727608008256309)
              ·
                refine ⟨61207350443213250774029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 652878404727608008256309 61207350443213250774029)
                ·
                  rfl

theorem cell20_402303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_402303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402303 prefixEnd_402303 := by exact prefixLift 402303
  have htrace : WordTrace (prefixWord ++ tailWord_402303) baseStart_402303 baseEnd_402303 := by
    simpa [prefixWord, tailWord_402303, baseEnd_402303] using wordTrace_append hprefix tailTrace_402303
  have hstable : (prefixWord ++ tailWord_402303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402303).length < 2 ^ (prefixWord ++ tailWord_402303).sum := by decide
  have hdescent : baseEnd_402303 < baseStart_402303 := by decide
  rcases family_descends (prefixWord ++ tailWord_402303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402326 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_402326 : Nat := 118140960795 + 402326 * 2 ^ 59
def prefixEnd_402326 : Nat := 4983230072969 + 3 ^ 40 * 402326 * 2
def baseEnd_402326 : Nat := 183632549156353894555327

theorem tailTrace_402326 : CollatzResearch.WordTrace tailWord_402326 prefixEnd_402326 183632549156353894555327 := by
  unfold tailWord_402326
  simp only [CollatzResearch.WordTrace]
  refine ⟨917127171278068040967677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9782689826966059103655221 917127171278068040967677)
  ·
    refine ⟨343922689229275515362879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 917127171278068040967677 343922689229275515362879)
    ·
      refine ⟨515884033843913273044319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343922689229275515362879 515884033843913273044319)
      ·
        refine ⟨773826050765869909566479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515884033843913273044319 773826050765869909566479)
        ·
          refine ⟨1160739076148804864349719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773826050765869909566479 1160739076148804864349719)
          ·
            refine ⟨1741108614223207296524579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160739076148804864349719 1741108614223207296524579)
            ·
              refine ⟨2611662921334810944786869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741108614223207296524579 2611662921334810944786869)
              ·
                refine ⟨244843398875138526073769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2611662921334810944786869 244843398875138526073769)
                ·
                  refine ⟨183632549156353894555327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244843398875138526073769 183632549156353894555327)
                  ·
                    rfl

theorem cell20_402326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_402326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402326 prefixEnd_402326 := by exact prefixLift 402326
  have htrace : WordTrace (prefixWord ++ tailWord_402326) baseStart_402326 baseEnd_402326 := by
    simpa [prefixWord, tailWord_402326, baseEnd_402326] using wordTrace_append hprefix tailTrace_402326
  have hstable : (prefixWord ++ tailWord_402326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402326).length < 2 ^ (prefixWord ++ tailWord_402326).sum := by decide
  have hdescent : baseEnd_402326 < baseStart_402326 := by decide
  rcases family_descends (prefixWord ++ tailWord_402326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402348 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_402348 : Nat := 118140960795 + 402348 * 2 ^ 59
def prefixEnd_402348 : Nat := 4983230072969 + 3 ^ 40 * 402348 * 2
def baseEnd_402348 : Nat := 183642590555819595821903

theorem tailTrace_402348 : CollatzResearch.WordTrace tailWord_402348 prefixEnd_402348 183642590555819595821903 := by
  unfold tailWord_402348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337418573184693206391849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9783224764246257608522465 7337418573184693206391849)
  ·
    refine ⟨5503063929888519904793887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7337418573184693206391849 5503063929888519904793887)
    ·
      refine ⟨8254595894832779857190831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503063929888519904793887 8254595894832779857190831)
      ·
        refine ⟨12381893842249169785786247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254595894832779857190831 12381893842249169785786247)
        ·
          refine ⟨18572840763373754678679371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381893842249169785786247 18572840763373754678679371)
          ·
            refine ⟨27859261145060632018019057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572840763373754678679371 27859261145060632018019057)
            ·
              refine ⟨20894445858795474013514293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27859261145060632018019057 20894445858795474013514293)
              ·
                refine ⟨1958854299262075688766965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20894445858795474013514293 1958854299262075688766965)
                ·
                  refine ⟨183642590555819595821903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1958854299262075688766965 183642590555819595821903)
                  ·
                    rfl

theorem cell20_402348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_402348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402348 prefixEnd_402348 := by exact prefixLift 402348
  have htrace : WordTrace (prefixWord ++ tailWord_402348) baseStart_402348 baseEnd_402348 := by
    simpa [prefixWord, tailWord_402348, baseEnd_402348] using wordTrace_append hprefix tailTrace_402348
  have hstable : (prefixWord ++ tailWord_402348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402348).length < 2 ^ (prefixWord ++ tailWord_402348).sum := by decide
  have hdescent : baseEnd_402348 < baseStart_402348 := by decide
  rcases family_descends (prefixWord ++ tailWord_402348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402379 : List Nat := [1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_402379 : Nat := 118140960795 + 402379 * 2 ^ 59
def prefixEnd_402379 : Nat := 4983230072969 + 3 ^ 40 * 402379 * 2
def baseEnd_402379 : Nat := 61218913266840421929481

theorem tailTrace_402379 : CollatzResearch.WordTrace tailWord_402379 prefixEnd_402379 61218913266840421929481 := by
  unfold tailWord_402379
  simp only [CollatzResearch.WordTrace]
  refine ⟨14675967809257078707162191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9783978539504719138108127 14675967809257078707162191)
  ·
    refine ⟨22013951713885618060743287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14675967809257078707162191 22013951713885618060743287)
    ·
      refine ⟨33020927570828427091114931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22013951713885618060743287 33020927570828427091114931)
      ·
        refine ⟨49531391356242640636672397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33020927570828427091114931 49531391356242640636672397)
        ·
          refine ⟨18574271758590990238752149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49531391356242640636672397 18574271758590990238752149)
          ·
            refine ⟨870668988683952667441507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18574271758590990238752149 870668988683952667441507)
            ·
              refine ⟨1306003483025929001162261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870668988683952667441507 1306003483025929001162261)
              ·
                refine ⟨61218913266840421929481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1306003483025929001162261 61218913266840421929481)
                ·
                  rfl

theorem cell20_402379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_402379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402379 prefixEnd_402379 := by exact prefixLift 402379
  have htrace : WordTrace (prefixWord ++ tailWord_402379) baseStart_402379 baseEnd_402379 := by
    simpa [prefixWord, tailWord_402379, baseEnd_402379] using wordTrace_append hprefix tailTrace_402379
  have hstable : (prefixWord ++ tailWord_402379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402379).length < 2 ^ (prefixWord ++ tailWord_402379).sum := by decide
  have hdescent : baseEnd_402379 < baseStart_402379 := by decide
  rcases family_descends (prefixWord ++ tailWord_402379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402402 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_402402 : Nat := 118140960795 + 402402 * 2 ^ 59
def prefixEnd_402402 : Nat := 4983230072969 + 3 ^ 40 * 402402 * 2
def baseEnd_402402 : Nat := 183667237627235408021683

theorem tailTrace_402402 : CollatzResearch.WordTrace tailWord_402402 prefixEnd_402402 183667237627235408021683 := by
  unfold tailWord_402402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669201672043438408812365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9784537792115835756832973 3669201672043438408812365)
  ·
    refine ⟨1375950627016289403304637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3669201672043438408812365 1375950627016289403304637)
    ·
      refine ⟨515981485131108526239239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1375950627016289403304637 515981485131108526239239)
      ·
        refine ⟨773972227696662789358859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515981485131108526239239 773972227696662789358859)
        ·
          refine ⟨1160958341544994184038289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773972227696662789358859 1160958341544994184038289)
          ·
            refine ⟨870718756158745638028717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160958341544994184038289 870718756158745638028717)
            ·
              refine ⟨326519533559529614260769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870718756158745638028717 326519533559529614260769)
              ·
                refine ⟨244889650169647210695577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326519533559529614260769 244889650169647210695577)
                ·
                  refine ⟨183667237627235408021683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244889650169647210695577 183667237627235408021683)
                  ·
                    rfl

theorem cell20_402402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_402402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402402 prefixEnd_402402 := by exact prefixLift 402402
  have htrace : WordTrace (prefixWord ++ tailWord_402402) baseStart_402402 baseEnd_402402 := by
    simpa [prefixWord, tailWord_402402, baseEnd_402402] using wordTrace_append hprefix tailTrace_402402
  have hstable : (prefixWord ++ tailWord_402402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402402).length < 2 ^ (prefixWord ++ tailWord_402402).sum := by decide
  have hdescent : baseEnd_402402 < baseStart_402402 := by decide
  rcases family_descends (prefixWord ++ tailWord_402402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402403 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_402403 : Nat := 118140960795 + 402403 * 2 ^ 59
def prefixEnd_402403 : Nat := 4983230072969 + 3 ^ 40 * 402403 * 2
def baseEnd_402403 : Nat := 183667694054483848988345

theorem tailTrace_402403 : CollatzResearch.WordTrace tailWord_402403 prefixEnd_402403 183667694054483848988345 := by
  unfold tailWord_402403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676843161170130806035863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9784562107446753870690575 14676843161170130806035863)
  ·
    refine ⟨22015264741755196209053795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14676843161170130806035863 22015264741755196209053795)
    ·
      refine ⟨33022897112632794313580693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22015264741755196209053795 33022897112632794313580693)
      ·
        refine ⟨1547948302154662233449095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33022897112632794313580693 1547948302154662233449095)
        ·
          refine ⟨2321922453231993350173643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547948302154662233449095 2321922453231993350173643)
          ·
            refine ⟨3482883679847990025260465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321922453231993350173643 3482883679847990025260465)
            ·
              refine ⟨2612162759885992518945349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482883679847990025260465 2612162759885992518945349)
              ·
                refine ⟨489780517478623597302253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2612162759885992518945349 489780517478623597302253)
                ·
                  refine ⟨183667694054483848988345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489780517478623597302253 183667694054483848988345)
                  ·
                    rfl

theorem cell20_402403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_402403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402403 prefixEnd_402403 := by exact prefixLift 402403
  have htrace : WordTrace (prefixWord ++ tailWord_402403) baseStart_402403 baseEnd_402403 := by
    simpa [prefixWord, tailWord_402403, baseEnd_402403] using wordTrace_append hprefix tailTrace_402403
  have hstable : (prefixWord ++ tailWord_402403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402403).length < 2 ^ (prefixWord ++ tailWord_402403).sum := by decide
  have hdescent : baseEnd_402403 < baseStart_402403 := by decide
  rcases family_descends (prefixWord ++ tailWord_402403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402417 : List Nat := [1, 2, 2, 2, 4, 1, 1, 7]
def baseStart_402417 : Nat := 118140960795 + 402417 * 2 ^ 59
def prefixEnd_402417 : Nat := 4983230072969 + 3 ^ 40 * 402417 * 2
def baseEnd_402417 : Nat := 61224694678654007507207

theorem tailTrace_402417 : CollatzResearch.WordTrace tailWord_402417 prefixEnd_402417 61224694678654007507207 := by
  unfold tailWord_402417
  simp only [CollatzResearch.WordTrace]
  refine ⟨14677353783119411197045505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9784902522079607464697003 14677353783119411197045505)
  ·
    refine ⟨11008015337339558397784129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14677353783119411197045505 11008015337339558397784129)
    ·
      refine ⟨8256011503004668798338097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11008015337339558397784129 8256011503004668798338097)
      ·
        refine ⟨6192008627253501598753573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8256011503004668798338097 6192008627253501598753573)
        ·
          refine ⟨1161001617610031549766295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6192008627253501598753573 1161001617610031549766295)
          ·
            refine ⟨1741502426415047324649443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161001617610031549766295 1741502426415047324649443)
            ·
              refine ⟨2612253639622570986974165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741502426415047324649443 2612253639622570986974165)
              ·
                refine ⟨61224694678654007507207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2612253639622570986974165 61224694678654007507207)
                ·
                  rfl

theorem cell20_402417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_402417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402417 prefixEnd_402417 := by exact prefixLift 402417
  have htrace : WordTrace (prefixWord ++ tailWord_402417) baseStart_402417 baseEnd_402417 := by
    simpa [prefixWord, tailWord_402417, baseEnd_402417] using wordTrace_append hprefix tailTrace_402417
  have hstable : (prefixWord ++ tailWord_402417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402417).length < 2 ^ (prefixWord ++ tailWord_402417).sum := by decide
  have hdescent : baseEnd_402417 < baseStart_402417 := by decide
  rcases family_descends (prefixWord ++ tailWord_402417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402455 : List Nat := [1, 1, 3, 5, 1, 9]
def baseStart_402455 : Nat := 118140960795 + 402455 * 2 ^ 59
def prefixEnd_402455 : Nat := 4983230072969 + 3 ^ 40 * 402455 * 2
def baseEnd_402455 : Nat := 6803386232274177009437

theorem tailTrace_402455 : CollatzResearch.WordTrace tailWord_402455 prefixEnd_402455 6803386232274177009437 := by
  unfold tailWord_402455
  simp only [CollatzResearch.WordTrace]
  refine ⟨14678739756981743686928819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9785826504654495791285879 14678739756981743686928819)
  ·
    refine ⟨22018109635472615530393229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14678739756981743686928819 22018109635472615530393229)
    ·
      refine ⟨8256791113302230823897461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22018109635472615530393229 8256791113302230823897461)
      ·
        refine ⟨774074166872084139740387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8256791113302230823897461 774074166872084139740387)
        ·
          refine ⟨1161111250308126209610581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774074166872084139740387 1161111250308126209610581)
          ·
            refine ⟨6803386232274177009437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1161111250308126209610581 6803386232274177009437)
            ·
              rfl

theorem cell20_402455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_402455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402455 prefixEnd_402455 := by exact prefixLift 402455
  have htrace : WordTrace (prefixWord ++ tailWord_402455) baseStart_402455 baseEnd_402455 := by
    simpa [prefixWord, tailWord_402455, baseEnd_402455] using wordTrace_append hprefix tailTrace_402455
  have hstable : (prefixWord ++ tailWord_402455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402455).length < 2 ^ (prefixWord ++ tailWord_402455).sum := by decide
  have hdescent : baseEnd_402455 < baseStart_402455 := by decide
  rcases family_descends (prefixWord ++ tailWord_402455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402503 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 2]
def baseStart_402503 : Nat := 118140960795 + 402503 * 2 ^ 59
def prefixEnd_402503 : Nat := 4983230072969 + 3 ^ 40 * 402503 * 2
def baseEnd_402503 : Nat := 183713336779327945654603

theorem tailTrace_402503 : CollatzResearch.WordTrace tailWord_402503 prefixEnd_402503 183713336779327945654603 := by
  unfold tailWord_402503
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680490460807847884676163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786993640538565256450775 14680490460807847884676163)
  ·
    refine ⟨22020735691211771827014245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14680490460807847884676163 22020735691211771827014245)
    ·
      refine ⟨4128887942102207217565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22020735691211771827014245 4128887942102207217565171)
      ·
        refine ⟨6193331913153310826347757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128887942102207217565171 6193331913153310826347757)
        ·
          refine ⟨2322499467432491559880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6193331913153310826347757 2322499467432491559880409)
          ·
            refine ⟨1741874600574368669910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322499467432491559880409 1741874600574368669910307)
            ·
              refine ⟨2612811900861553004865461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741874600574368669910307 2612811900861553004865461)
              ·
                refine ⟨244951115705770594206137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2612811900861553004865461 244951115705770594206137)
                ·
                  refine ⟨183713336779327945654603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244951115705770594206137 183713336779327945654603)
                  ·
                    rfl

theorem cell20_402503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2].length) (baseStart_402503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402503 prefixEnd_402503 := by exact prefixLift 402503
  have htrace : WordTrace (prefixWord ++ tailWord_402503) baseStart_402503 baseEnd_402503 := by
    simpa [prefixWord, tailWord_402503, baseEnd_402503] using wordTrace_append hprefix tailTrace_402503
  have hstable : (prefixWord ++ tailWord_402503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402503).length < 2 ^ (prefixWord ++ tailWord_402503).sum := by decide
  have hdescent : baseEnd_402503 < baseStart_402503 := by decide
  rcases family_descends (prefixWord ++ tailWord_402503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402545 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_402545 : Nat := 118140960795 + 402545 * 2 ^ 59
def prefixEnd_402545 : Nat := 4983230072969 + 3 ^ 40 * 402545 * 2
def baseEnd_402545 : Nat := 183732506723762466254431

theorem tailTrace_402545 : CollatzResearch.WordTrace tailWord_402545 prefixEnd_402545 183732506723762466254431 := by
  unfold tailWord_402545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682022326655689057705089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9788014884437126038470059 14682022326655689057705089)
  ·
    refine ⟨11011516744991766793278817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14682022326655689057705089 11011516744991766793278817)
    ·
      refine ⟨8258637558743825094959113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011516744991766793278817 8258637558743825094959113)
      ·
        refine ⟨6193978169057868821219335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8258637558743825094959113 6193978169057868821219335)
        ·
          refine ⟨9290967253586803231829003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193978169057868821219335 9290967253586803231829003)
          ·
            refine ⟨13936450880380204847743505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290967253586803231829003 13936450880380204847743505)
            ·
              refine ⟨10452338160285153635807629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13936450880380204847743505 10452338160285153635807629)
              ·
                refine ⟨3919626810106932613427861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10452338160285153635807629 3919626810106932613427861)
                ·
                  refine ⟨183732506723762466254431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3919626810106932613427861 183732506723762466254431)
                  ·
                    rfl

theorem cell20_402545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_402545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402545 prefixEnd_402545 := by exact prefixLift 402545
  have htrace : WordTrace (prefixWord ++ tailWord_402545) baseStart_402545 baseEnd_402545 := by
    simpa [prefixWord, tailWord_402545, baseEnd_402545] using wordTrace_append hprefix tailTrace_402545
  have hstable : (prefixWord ++ tailWord_402545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402545).length < 2 ^ (prefixWord ++ tailWord_402545).sum := by decide
  have hdescent : baseEnd_402545 < baseStart_402545 := by decide
  rcases family_descends (prefixWord ++ tailWord_402545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402569 : List Nat := [1, 2, 1, 1, 4, 5, 6]
def baseStart_402569 : Nat := 118140960795 + 402569 * 2 ^ 59
def prefixEnd_402569 : Nat := 4983230072969 + 3 ^ 40 * 402569 * 2
def baseEnd_402569 : Nat := 20415940108636116606037

theorem tailTrace_402569 : CollatzResearch.WordTrace tailWord_402569 prefixEnd_402569 20415940108636116606037 := by
  unfold tailWord_402569
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682897678568741156578761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9788598452379160771052507 14682897678568741156578761)
  ·
    refine ⟨11012173258926555867434071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14682897678568741156578761 11012173258926555867434071)
    ·
      refine ⟨16518259888389833801151107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012173258926555867434071 16518259888389833801151107)
      ·
        refine ⟨24777389832584750701726661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16518259888389833801151107 24777389832584750701726661)
        ·
          refine ⟨4645760593609640756573749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24777389832584750701726661 4645760593609640756573749)
          ·
            refine ⟨435540055650903820928789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4645760593609640756573749 435540055650903820928789)
            ·
              refine ⟨20415940108636116606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 435540055650903820928789 20415940108636116606037)
              ·
                rfl

theorem cell20_402569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_402569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402569 prefixEnd_402569 := by exact prefixLift 402569
  have htrace : WordTrace (prefixWord ++ tailWord_402569) baseStart_402569 baseEnd_402569 := by
    simpa [prefixWord, tailWord_402569, baseEnd_402569] using wordTrace_append hprefix tailTrace_402569
  have hstable : (prefixWord ++ tailWord_402569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402569).length < 2 ^ (prefixWord ++ tailWord_402569).sum := by decide
  have hdescent : baseEnd_402569 < baseStart_402569 := by decide
  rcases family_descends (prefixWord ++ tailWord_402569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402586 : List Nat := [3, 1, 1, 5, 1, 2, 2, 5]
def baseStart_402586 : Nat := 118140960795 + 402586 * 2 ^ 59
def prefixEnd_402586 : Nat := 4983230072969 + 3 ^ 40 * 402586 * 2
def baseEnd_402586 : Nat := 61250406746982848629199

theorem tailTrace_402586 : CollatzResearch.WordTrace tailWord_402586 prefixEnd_402586 61250406746982848629199 := by
  unfold tailWord_402586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670879429876788264986903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9789011813004768706631741 3670879429876788264986903)
  ·
    refine ⟨5506319144815182397480355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3670879429876788264986903 5506319144815182397480355)
    ·
      refine ⟨8259478717222773596220533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5506319144815182397480355 8259478717222773596220533)
      ·
        refine ⟨774326129739635024645675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8259478717222773596220533 774326129739635024645675)
        ·
          refine ⟨1161489194609452536968513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774326129739635024645675 1161489194609452536968513)
          ·
            refine ⟨871116895957089402726385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161489194609452536968513 871116895957089402726385)
            ·
              refine ⟨653337671967817052044789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871116895957089402726385 653337671967817052044789)
              ·
                refine ⟨61250406746982848629199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653337671967817052044789 61250406746982848629199)
                ·
                  rfl

theorem cell20_402586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_402586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402586 prefixEnd_402586 := by exact prefixLift 402586
  have htrace : WordTrace (prefixWord ++ tailWord_402586) baseStart_402586 baseEnd_402586 := by
    simpa [prefixWord, tailWord_402586, baseEnd_402586] using wordTrace_append hprefix tailTrace_402586
  have hstable : (prefixWord ++ tailWord_402586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402586).length < 2 ^ (prefixWord ++ tailWord_402586).sum := by decide
  have hdescent : baseEnd_402586 < baseStart_402586 := by decide
  rcases family_descends (prefixWord ++ tailWord_402586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402593 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_402593 : Nat := 118140960795 + 402593 * 2 ^ 59
def prefixEnd_402593 : Nat := 4983230072969 + 3 ^ 40 * 402593 * 2
def baseEnd_402593 : Nat := 183754415231687632654235

theorem tailTrace_402593 : CollatzResearch.WordTrace tailWord_402593 prefixEnd_402593 183754415231687632654235 := by
  unfold tailWord_402593
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683773030481793255452433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9789182020321195503634955 14683773030481793255452433)
  ·
    refine ⟨11012829772861344941589325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14683773030481793255452433 11012829772861344941589325)
    ·
      refine ⟨4129811164823004353095997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11012829772861344941589325 4129811164823004353095997)
      ·
        refine ⟨1548679186808626632410999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4129811164823004353095997 1548679186808626632410999)
        ·
          refine ⟨2323018780212939948616499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548679186808626632410999 2323018780212939948616499)
          ·
            refine ⟨3484528170319409922924749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323018780212939948616499 3484528170319409922924749)
            ·
              refine ⟨1306698063869778721096781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3484528170319409922924749 1306698063869778721096781)
              ·
                refine ⟨490011773951167020411293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306698063869778721096781 490011773951167020411293)
                ·
                  refine ⟨183754415231687632654235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490011773951167020411293 183754415231687632654235)
                  ·
                    rfl

theorem cell20_402593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_402593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402593 prefixEnd_402593 := by exact prefixLift 402593
  have htrace : WordTrace (prefixWord ++ tailWord_402593) baseStart_402593 baseEnd_402593 := by
    simpa [prefixWord, tailWord_402593, baseEnd_402593] using wordTrace_append hprefix tailTrace_402593
  have hstable : (prefixWord ++ tailWord_402593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402593).length < 2 ^ (prefixWord ++ tailWord_402593).sum := by decide
  have hdescent : baseEnd_402593 < baseStart_402593 := by decide
  rcases family_descends (prefixWord ++ tailWord_402593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402626 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_402626 : Nat := 118140960795 + 402626 * 2 ^ 59
def prefixEnd_402626 : Nat := 4983230072969 + 3 ^ 40 * 402626 * 2
def baseEnd_402626 : Nat := 183769477330886184554101

theorem tailTrace_402626 : CollatzResearch.WordTrace tailWord_402626 prefixEnd_402626 183769477330886184554101 := by
  unfold tailWord_402626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671244159840559972850933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9789984426241493260935821 3671244159840559972850933)
  ·
    refine ⟨344179139985052497454775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3671244159840559972850933 344179139985052497454775)
    ·
      refine ⟨516268709977578746182163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344179139985052497454775 516268709977578746182163)
      ·
        refine ⟨774403064966368119273245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516268709977578746182163 774403064966368119273245)
        ·
          refine ⟨290401149362388044727467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774403064966368119273245 290401149362388044727467)
          ·
            refine ⟨435601724043582067091201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290401149362388044727467 435601724043582067091201)
            ·
              refine ⟨326701293032686550318401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435601724043582067091201 326701293032686550318401)
              ·
                refine ⟨245025969774514912738801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326701293032686550318401 245025969774514912738801)
                ·
                  refine ⟨183769477330886184554101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245025969774514912738801 183769477330886184554101)
                  ·
                    rfl

theorem cell20_402626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_402626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402626 prefixEnd_402626 := by exact prefixLift 402626
  have htrace : WordTrace (prefixWord ++ tailWord_402626) baseStart_402626 baseEnd_402626 := by
    simpa [prefixWord, tailWord_402626, baseEnd_402626] using wordTrace_append hprefix tailTrace_402626
  have hstable : (prefixWord ++ tailWord_402626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402626).length < 2 ^ (prefixWord ++ tailWord_402626).sum := by decide
  have hdescent : baseEnd_402626 < baseStart_402626 := by decide
  rcases family_descends (prefixWord ++ tailWord_402626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402634 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_402634 : Nat := 118140960795 + 402634 * 2 ^ 59
def prefixEnd_402634 : Nat := 4983230072969 + 3 ^ 40 * 402634 * 2
def baseEnd_402634 : Nat := 183773128748873712287401

theorem tailTrace_402634 : CollatzResearch.WordTrace tailWord_402634 prefixEnd_402634 183773128748873712287401 := by
  unfold tailWord_402634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3671317105833314314423739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9790178948888838171796637 3671317105833314314423739)
  ·
    refine ⟨5506975658749971471635609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3671317105833314314423739 5506975658749971471635609)
    ·
      refine ⟨4130231744062478603726707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5506975658749971471635609 4130231744062478603726707)
      ·
        refine ⟨6195347616093717905590061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130231744062478603726707 6195347616093717905590061)
        ·
          refine ⟨2323255356035144214596273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6195347616093717905590061 2323255356035144214596273)
          ·
            refine ⟨1742441517026358160947205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323255356035144214596273 1742441517026358160947205)
            ·
              refine ⟨326707784442442155177601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1742441517026358160947205 326707784442442155177601)
              ·
                refine ⟨245030838331831616383201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326707784442442155177601 245030838331831616383201)
                ·
                  refine ⟨183773128748873712287401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245030838331831616383201 183773128748873712287401)
                  ·
                    rfl

theorem cell20_402634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_402634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402634 prefixEnd_402634 := by exact prefixLift 402634
  have htrace : WordTrace (prefixWord ++ tailWord_402634) baseStart_402634 baseEnd_402634 := by
    simpa [prefixWord, tailWord_402634, baseEnd_402634] using wordTrace_append hprefix tailTrace_402634
  have hstable : (prefixWord ++ tailWord_402634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402634).length < 2 ^ (prefixWord ++ tailWord_402634).sum := by decide
  have hdescent : baseEnd_402634 < baseStart_402634 := by decide
  rcases family_descends (prefixWord ++ tailWord_402634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402637 : List Nat := [1, 6, 2, 2, 2, 1, 1, 5]
def baseStart_402637 : Nat := 118140960795 + 402637 * 2 ^ 59
def prefixEnd_402637 : Nat := 4983230072969 + 3 ^ 40 * 402637 * 2
def baseEnd_402637 : Nat := 61258166010206345062463

theorem tailTrace_402637 : CollatzResearch.WordTrace tailWord_402637 prefixEnd_402637 61258166010206345062463 := by
  unfold tailWord_402637
  simp only [CollatzResearch.WordTrace]
  refine ⟨14685377842322388770054165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9790251894881592513369443 14685377842322388770054165)
  ·
    refine ⟨688377086358861973596289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14685377842322388770054165 688377086358861973596289)
    ·
      refine ⟨516282814769146480197217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688377086358861973596289 516282814769146480197217)
      ·
        refine ⟨387212111076859860147913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516282814769146480197217 387212111076859860147913)
        ·
          refine ⟨290409083307644895110935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387212111076859860147913 290409083307644895110935)
          ·
            refine ⟨435613624961467342666403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290409083307644895110935 435613624961467342666403)
            ·
              refine ⟨653420437442201013999605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435613624961467342666403 653420437442201013999605)
              ·
                refine ⟨61258166010206345062463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653420437442201013999605 61258166010206345062463)
                ·
                  rfl

theorem cell20_402637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_402637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402637 prefixEnd_402637 := by exact prefixLift 402637
  have htrace : WordTrace (prefixWord ++ tailWord_402637) baseStart_402637 baseEnd_402637 := by
    simpa [prefixWord, tailWord_402637, baseEnd_402637] using wordTrace_append hprefix tailTrace_402637
  have hstable : (prefixWord ++ tailWord_402637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402637).length < 2 ^ (prefixWord ++ tailWord_402637).sum := by decide
  have hdescent : baseEnd_402637 < baseStart_402637 := by decide
  rcases family_descends (prefixWord ++ tailWord_402637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402686 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_402686 : Nat := 118140960795 + 402686 * 2 ^ 59
def prefixEnd_402686 : Nat := 4983230072969 + 3 ^ 40 * 402686 * 2
def baseEnd_402686 : Nat := 183796862965792642553855

theorem tailTrace_402686 : CollatzResearch.WordTrace tailWord_402686 prefixEnd_402686 183796862965792642553855 := by
  unfold tailWord_402686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835895627393108767323489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9791443346096580092391941 1835895627393108767323489)
  ·
    refine ⟨1376921720544831575492617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1835895627393108767323489 1376921720544831575492617)
    ·
      refine ⟨1032691290408623681619463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1376921720544831575492617 1032691290408623681619463)
      ·
        refine ⟨1549036935612935522429195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032691290408623681619463 1549036935612935522429195)
        ·
          refine ⟨2323555403419403283643793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549036935612935522429195 2323555403419403283643793)
          ·
            refine ⟨1742666552564552462732845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323555403419403283643793 1742666552564552462732845)
            ·
              refine ⟨653499957211707173524817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742666552564552462732845 653499957211707173524817)
              ·
                refine ⟨490124967908780380143613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653499957211707173524817 490124967908780380143613)
                ·
                  refine ⟨183796862965792642553855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490124967908780380143613 183796862965792642553855)
                  ·
                    rfl

theorem cell20_402686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_402686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402686 prefixEnd_402686 := by exact prefixLift 402686
  have htrace : WordTrace (prefixWord ++ tailWord_402686) baseStart_402686 baseEnd_402686 := by
    simpa [prefixWord, tailWord_402686, baseEnd_402686] using wordTrace_append hprefix tailTrace_402686
  have hstable : (prefixWord ++ tailWord_402686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402686).length < 2 ^ (prefixWord ++ tailWord_402686).sum := by decide
  have hdescent : baseEnd_402686 < baseStart_402686 := by decide
  rcases family_descends (prefixWord ++ tailWord_402686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402714 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_402714 : Nat := 118140960795 + 402714 * 2 ^ 59
def prefixEnd_402714 : Nat := 4983230072969 + 3 ^ 40 * 402714 * 2
def baseEnd_402714 : Nat := 183809642928748989620407

theorem tailTrace_402714 : CollatzResearch.WordTrace tailWord_402714 prefixEnd_402714 183809642928748989620407 := by
  unfold tailWord_402714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672046565760857730151799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9792124175362287280404797 3672046565760857730151799)
  ·
    refine ⟨5508069848641286595227699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3672046565760857730151799 5508069848641286595227699)
    ·
      refine ⟨8262104772961929892841549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508069848641286595227699 8262104772961929892841549)
      ·
        refine ⟨3098289289860723709815581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8262104772961929892841549 3098289289860723709815581)
        ·
          refine ⟨1161858483697771391180843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3098289289860723709815581 1161858483697771391180843)
          ·
            refine ⟨1742787725546657086771265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161858483697771391180843 1742787725546657086771265)
            ·
              refine ⟨1307090794159992815078449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742787725546657086771265 1307090794159992815078449)
              ·
                refine ⟨980318095619994611308837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307090794159992815078449 980318095619994611308837)
                ·
                  refine ⟨183809642928748989620407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980318095619994611308837 183809642928748989620407)
                  ·
                    rfl

theorem cell20_402714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_402714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402714 prefixEnd_402714 := by exact prefixLift 402714
  have htrace : WordTrace (prefixWord ++ tailWord_402714) baseStart_402714 baseEnd_402714 := by
    simpa [prefixWord, tailWord_402714, baseEnd_402714] using wordTrace_append hprefix tailTrace_402714
  have hstable : (prefixWord ++ tailWord_402714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402714).length < 2 ^ (prefixWord ++ tailWord_402714).sum := by decide
  have hdescent : baseEnd_402714 < baseStart_402714 := by decide
  rcases family_descends (prefixWord ++ tailWord_402714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402717 : List Nat := [1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_402717 : Nat := 118140960795 + 402717 * 2 ^ 59
def prefixEnd_402717 : Nat := 4983230072969 + 3 ^ 40 * 402717 * 2
def baseEnd_402717 : Nat := 61270337403498104173465

theorem tailTrace_402717 : CollatzResearch.WordTrace tailWord_402717 prefixEnd_402717 61270337403498104173465 := by
  unfold tailWord_402717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14688295682032562432966405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9792197121355041621977603 14688295682032562432966405)
  ·
    refine ⟨2754055440381105456181201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14688295682032562432966405 2754055440381105456181201)
    ·
      refine ⟨2065541580285829092135901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2754055440381105456181201 2065541580285829092135901)
      ·
        refine ⟨774578092607185909550963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2065541580285829092135901 774578092607185909550963)
        ·
          refine ⟨1161867138910778864326445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774578092607185909550963 1161867138910778864326445)
          ·
            refine ⟨435700177091542074122417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1161867138910778864326445 435700177091542074122417)
            ·
              refine ⟨326775132818656555591813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435700177091542074122417 326775132818656555591813)
              ·
                refine ⟨61270337403498104173465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326775132818656555591813 61270337403498104173465)
                ·
                  rfl

theorem cell20_402717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_402717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402717 prefixEnd_402717 := by exact prefixLift 402717
  have htrace : WordTrace (prefixWord ++ tailWord_402717) baseStart_402717 baseEnd_402717 := by
    simpa [prefixWord, tailWord_402717, baseEnd_402717] using wordTrace_append hprefix tailTrace_402717
  have hstable : (prefixWord ++ tailWord_402717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402717).length < 2 ^ (prefixWord ++ tailWord_402717).sum := by decide
  have hdescent : baseEnd_402717 < baseStart_402717 := by decide
  rcases family_descends (prefixWord ++ tailWord_402717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402748 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_402748 : Nat := 118140960795 + 402748 * 2 ^ 59
def prefixEnd_402748 : Nat := 4983230072969 + 3 ^ 40 * 402748 * 2
def baseEnd_402748 : Nat := 183825161455195982486935

theorem tailTrace_402748 : CollatzResearch.WordTrace tailWord_402748 prefixEnd_402748 183825161455195982486935 := by
  unfold tailWord_402748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344713172460127363672449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9792950896613503151563265 7344713172460127363672449)
  ·
    refine ⟨5508534879345095522754337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7344713172460127363672449 5508534879345095522754337)
    ·
      refine ⟨4131401159508821642065753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5508534879345095522754337 4131401159508821642065753)
      ·
        refine ⟨3098550869631616231549315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131401159508821642065753 3098550869631616231549315)
        ·
          refine ⟨4647826304447424347323973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098550869631616231549315 4647826304447424347323973)
          ·
            refine ⟨871467432083892065123245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4647826304447424347323973 871467432083892065123245)
            ·
              refine ⟨326800287031459524421217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871467432083892065123245 326800287031459524421217)
              ·
                refine ⟨245100215273594643315913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326800287031459524421217 245100215273594643315913)
                ·
                  refine ⟨183825161455195982486935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245100215273594643315913 183825161455195982486935)
                  ·
                    rfl

theorem cell20_402748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_402748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402748 prefixEnd_402748 := by exact prefixLift 402748
  have htrace : WordTrace (prefixWord ++ tailWord_402748) baseStart_402748 baseEnd_402748 := by
    simpa [prefixWord, tailWord_402748, baseEnd_402748] using wordTrace_append hprefix tailTrace_402748
  have hstable : (prefixWord ++ tailWord_402748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402748).length < 2 ^ (prefixWord ++ tailWord_402748).sum := by decide
  have hdescent : baseEnd_402748 < baseStart_402748 := by decide
  rcases family_descends (prefixWord ++ tailWord_402748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402758 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_402758 : Nat := 118140960795 + 402758 * 2 ^ 59
def prefixEnd_402758 : Nat := 4983230072969 + 3 ^ 40 * 402758 * 2
def baseEnd_402758 : Nat := 183829725727680392153561

theorem tailTrace_402758 : CollatzResearch.WordTrace tailWord_402758 prefixEnd_402758 183829725727680392153561 := by
  unfold tailWord_402758
  simp only [CollatzResearch.WordTrace]
  refine ⟨459055971090125826100279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9793194049922684290139285 459055971090125826100279)
  ·
    refine ⟨688583956635188739150419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459055971090125826100279 688583956635188739150419)
    ·
      refine ⟨1032875934952783108725629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688583956635188739150419 1032875934952783108725629)
      ·
        refine ⟨387328475607293665772111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1032875934952783108725629 387328475607293665772111)
        ·
          refine ⟨580992713410940498658167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387328475607293665772111 580992713410940498658167)
          ·
            refine ⟨871489070116410747987251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580992713410940498658167 871489070116410747987251)
            ·
              refine ⟨1307233605174616121980877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871489070116410747987251 1307233605174616121980877)
              ·
                refine ⟨490212601940481045742829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307233605174616121980877 490212601940481045742829)
                ·
                  refine ⟨183829725727680392153561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490212601940481045742829 183829725727680392153561)
                  ·
                    rfl

theorem cell20_402758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_402758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402758 prefixEnd_402758 := by exact prefixLift 402758
  have htrace : WordTrace (prefixWord ++ tailWord_402758) baseStart_402758 baseEnd_402758 := by
    simpa [prefixWord, tailWord_402758, baseEnd_402758] using wordTrace_append hprefix tailTrace_402758
  have hstable : (prefixWord ++ tailWord_402758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402758).length < 2 ^ (prefixWord ++ tailWord_402758).sum := by decide
  have hdescent : baseEnd_402758 < baseStart_402758 := by decide
  rcases family_descends (prefixWord ++ tailWord_402758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402759 : List Nat := [1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_402759 : Nat := 118140960795 + 402759 * 2 ^ 59
def prefixEnd_402759 : Nat := 4983230072969 + 3 ^ 40 * 402759 * 2
def baseEnd_402759 : Nat := 61276727384976277706741

theorem tailTrace_402759 : CollatzResearch.WordTrace tailWord_402759 prefixEnd_402759 61276727384976277706741 := by
  unfold tailWord_402759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689827547880403605995331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9793218365253602403996887 14689827547880403605995331)
  ·
    refine ⟨22034741321820605408992997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14689827547880403605995331 22034741321820605408992997)
    ·
      refine ⟨4131513997841363514186187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22034741321820605408992997 4131513997841363514186187)
      ·
        refine ⟨6197270996762045271279281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4131513997841363514186187 6197270996762045271279281)
        ·
          refine ⟨4647953247571533953459461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6197270996762045271279281 4647953247571533953459461)
          ·
            refine ⟨871491233919662616273649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4647953247571533953459461 871491233919662616273649)
            ·
              refine ⟨653618425439746962205237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871491233919662616273649 653618425439746962205237)
              ·
                refine ⟨61276727384976277706741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653618425439746962205237 61276727384976277706741)
                ·
                  rfl

theorem cell20_402759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_402759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402759 prefixEnd_402759 := by exact prefixLift 402759
  have htrace : WordTrace (prefixWord ++ tailWord_402759) baseStart_402759 baseEnd_402759 := by
    simpa [prefixWord, tailWord_402759, baseEnd_402759] using wordTrace_append hprefix tailTrace_402759
  have hstable : (prefixWord ++ tailWord_402759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402759).length < 2 ^ (prefixWord ++ tailWord_402759).sum := by decide
  have hdescent : baseEnd_402759 < baseStart_402759 := by decide
  rcases family_descends (prefixWord ++ tailWord_402759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402811 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_402811 : Nat := 118140960795 + 402811 * 2 ^ 59
def prefixEnd_402811 : Nat := 4983230072969 + 3 ^ 40 * 402811 * 2
def baseEnd_402811 : Nat := 183853916371847763386677

theorem tailTrace_402811 : CollatzResearch.WordTrace tailWord_402811 prefixEnd_402811 183853916371847763386677 := by
  unfold tailWord_402811
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691724143692016486888287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9794482762461344324592191 14691724143692016486888287)
  ·
    refine ⟨22037586215538024730332431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14691724143692016486888287 22037586215538024730332431)
    ·
      refine ⟨33056379323307037095498647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22037586215538024730332431 33056379323307037095498647)
      ·
        refine ⟨49584568984960555643247971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33056379323307037095498647 49584568984960555643247971)
        ·
          refine ⟨74376853477440833464871957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49584568984960555643247971 74376853477440833464871957)
          ·
            refine ⟨3486415006755039068665873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74376853477440833464871957 3486415006755039068665873)
            ·
              refine ⟨2614811255066279301499405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486415006755039068665873 2614811255066279301499405)
              ·
                refine ⟨980554220649854738062277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614811255066279301499405 980554220649854738062277)
                ·
                  refine ⟨183853916371847763386677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980554220649854738062277 183853916371847763386677)
                  ·
                    rfl

theorem cell20_402811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_402811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402811 prefixEnd_402811 := by exact prefixLift 402811
  have htrace : WordTrace (prefixWord ++ tailWord_402811) baseStart_402811 baseEnd_402811 := by
    simpa [prefixWord, tailWord_402811, baseEnd_402811] using wordTrace_append hprefix tailTrace_402811
  have hstable : (prefixWord ++ tailWord_402811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402811).length < 2 ^ (prefixWord ++ tailWord_402811).sum := by decide
  have hdescent : baseEnd_402811 < baseStart_402811 := by decide
  rcases family_descends (prefixWord ++ tailWord_402811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402842 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_402842 : Nat := 118140960795 + 402842 * 2 ^ 59
def prefixEnd_402842 : Nat := 4983230072969 + 3 ^ 40 * 402842 * 2
def baseEnd_402842 : Nat := 183868065616549433353217

theorem tailTrace_402842 : CollatzResearch.WordTrace tailWord_402842 prefixEnd_402842 183868065616549433353217 := by
  unfold tailWord_402842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673213701644927195316695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9795236537719805854177853 3673213701644927195316695)
  ·
    refine ⟨5509820552467390792975043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673213701644927195316695 5509820552467390792975043)
    ·
      refine ⟨8264730828701086189462565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5509820552467390792975043 8264730828701086189462565)
      ·
        refine ⟨1549637030381453660524231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8264730828701086189462565 1549637030381453660524231)
        ·
          refine ⟨2324455545572180490786347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549637030381453660524231 2324455545572180490786347)
          ·
            refine ⟨3486683318358270736179521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324455545572180490786347 3486683318358270736179521)
            ·
              refine ⟨2615012488768703052134641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3486683318358270736179521 2615012488768703052134641)
              ·
                refine ⟨1961259366576527289100981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615012488768703052134641 1961259366576527289100981)
                ·
                  refine ⟨183868065616549433353217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1961259366576527289100981 183868065616549433353217)
                  ·
                    rfl

theorem cell20_402842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_402842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402842 prefixEnd_402842 := by exact prefixLift 402842
  have htrace : WordTrace (prefixWord ++ tailWord_402842) baseStart_402842 baseEnd_402842 := by
    simpa [prefixWord, tailWord_402842, baseEnd_402842] using wordTrace_append hprefix tailTrace_402842
  have hstable : (prefixWord ++ tailWord_402842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402842).length < 2 ^ (prefixWord ++ tailWord_402842).sum := by decide
  have hdescent : baseEnd_402842 < baseStart_402842 := by decide
  rcases family_descends (prefixWord ++ tailWord_402842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402845 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 2]
def baseStart_402845 : Nat := 118140960795 + 402845 * 2 ^ 59
def prefixEnd_402845 : Nat := 4983230072969 + 3 ^ 40 * 402845 * 2
def baseEnd_402845 : Nat := 183869434898294756253205

theorem tailTrace_402845 : CollatzResearch.WordTrace tailWord_402845 prefixEnd_402845 183869434898294756253205 := by
  unfold tailWord_402845
  simp only [CollatzResearch.WordTrace]
  refine ⟨14692964225568840293625989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9795309483712560195750659 14692964225568840293625989)
  ·
    refine ⟨2754930792294157555054873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14692964225568840293625989 2754930792294157555054873)
    ·
      refine ⟨2066198094220618166291155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2754930792294157555054873 2066198094220618166291155)
      ·
        refine ⟨3099297141330927249436733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2066198094220618166291155 3099297141330927249436733)
        ·
          refine ⟨1162236427999097718538775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3099297141330927249436733 1162236427999097718538775)
          ·
            refine ⟨1743354641998646577808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162236427999097718538775 1743354641998646577808163)
            ·
              refine ⟨2615031962997969866712245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743354641998646577808163 2615031962997969866712245)
              ·
                refine ⟨245159246531059675004273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2615031962997969866712245 245159246531059675004273)
                ·
                  refine ⟨183869434898294756253205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245159246531059675004273 183869434898294756253205)
                  ·
                    rfl

theorem cell20_402845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_402845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402845 prefixEnd_402845 := by exact prefixLift 402845
  have htrace : WordTrace (prefixWord ++ tailWord_402845) baseStart_402845 baseEnd_402845 := by
    simpa [prefixWord, tailWord_402845, baseEnd_402845] using wordTrace_append hprefix tailTrace_402845
  have hstable : (prefixWord ++ tailWord_402845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402845).length < 2 ^ (prefixWord ++ tailWord_402845).sum := by decide
  have hdescent : baseEnd_402845 < baseStart_402845 := by decide
  rcases family_descends (prefixWord ++ tailWord_402845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402880 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_402880 : Nat := 118140960795 + 402880 * 2 ^ 59
def prefixEnd_402880 : Nat := 4983230072969 + 3 ^ 40 * 402880 * 2
def baseEnd_402880 : Nat := 183885409851990190086395

theorem tailTrace_402880 : CollatzResearch.WordTrace tailWord_402880 prefixEnd_402880 183885409851990190086395 := by
  unfold tailWord_402880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347120390221020635575047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9796160520294694180766729 7347120390221020635575047)
  ·
    refine ⟨11020680585331530953362571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7347120390221020635575047 11020680585331530953362571)
    ·
      refine ⟨16531020877997296430043857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11020680585331530953362571 16531020877997296430043857)
      ·
        refine ⟨12398265658497972322532893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16531020877997296430043857 12398265658497972322532893)
        ·
          refine ⟨4649349621936739620949835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12398265658497972322532893 4649349621936739620949835)
          ·
            refine ⟨6974024432905109431424753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649349621936739620949835 6974024432905109431424753)
            ·
              refine ⟨5230518324678832073568565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974024432905109431424753 5230518324678832073568565)
              ·
                refine ⟨490361092938640506897053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5230518324678832073568565 490361092938640506897053)
                ·
                  refine ⟨183885409851990190086395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490361092938640506897053 183885409851990190086395)
                  ·
                    rfl

theorem cell20_402880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_402880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402880 prefixEnd_402880 := by exact prefixLift 402880
  have htrace : WordTrace (prefixWord ++ tailWord_402880) baseStart_402880 baseEnd_402880 := by
    simpa [prefixWord, tailWord_402880, baseEnd_402880] using wordTrace_append hprefix tailTrace_402880
  have hstable : (prefixWord ++ tailWord_402880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402880).length < 2 ^ (prefixWord ++ tailWord_402880).sum := by decide
  have hdescent : baseEnd_402880 < baseStart_402880 := by decide
  rcases family_descends (prefixWord ++ tailWord_402880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402882 : List Nat := [3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_402882 : Nat := 118140960795 + 402882 * 2 ^ 59
def prefixEnd_402882 : Nat := 4983230072969 + 3 ^ 40 * 402882 * 2
def baseEnd_402882 : Nat := 61295440902162357339907

theorem tailTrace_402882 : CollatzResearch.WordTrace tailWord_402882 prefixEnd_402882 61295440902162357339907 := by
  unfold tailWord_402882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673578431608698903180725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9796209150956530408481933 3673578431608698903180725)
  ·
    refine ⟨344397977963315522173193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3673578431608698903180725 344397977963315522173193)
    ·
      refine ⟨258298483472486641629895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344397977963315522173193 258298483472486641629895)
      ·
        refine ⟨387447725208729962444843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258298483472486641629895 387447725208729962444843)
        ·
          refine ⟨581171587813094943667265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387447725208729962444843 581171587813094943667265)
          ·
            refine ⟨435878690859821207750449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581171587813094943667265 435878690859821207750449)
            ·
              refine ⟨326909018144865905812837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435878690859821207750449 326909018144865905812837)
              ·
                refine ⟨61295440902162357339907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326909018144865905812837 61295440902162357339907)
                ·
                  rfl

theorem cell20_402882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_402882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402882 prefixEnd_402882 := by exact prefixLift 402882
  have htrace : WordTrace (prefixWord ++ tailWord_402882) baseStart_402882 baseEnd_402882 := by
    simpa [prefixWord, tailWord_402882, baseEnd_402882] using wordTrace_append hprefix tailTrace_402882
  have hstable : (prefixWord ++ tailWord_402882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402882).length < 2 ^ (prefixWord ++ tailWord_402882).sum := by decide
  have hdescent : baseEnd_402882 < baseStart_402882 := by decide
  rcases family_descends (prefixWord ++ tailWord_402882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402887 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_402887 : Nat := 118140960795 + 402887 * 2 ^ 59
def prefixEnd_402887 : Nat := 4983230072969 + 3 ^ 40 * 402887 * 2
def baseEnd_402887 : Nat := 183888604842729276853033

theorem tailTrace_402887 : CollatzResearch.WordTrace tailWord_402887 prefixEnd_402887 183888604842729276853033 := by
  unfold tailWord_402887
  simp only [CollatzResearch.WordTrace]
  refine ⟨14694496091416681466654915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9796330727611120977769943 14694496091416681466654915)
  ·
    refine ⟨22041744137125022199982373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14694496091416681466654915 22041744137125022199982373)
    ·
      refine ⟨4132827025710941662496695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22041744137125022199982373 4132827025710941662496695)
      ·
        refine ⟨6199240538566412493745043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132827025710941662496695 6199240538566412493745043)
        ·
          refine ⟨9298860807849618740617565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199240538566412493745043 9298860807849618740617565)
          ·
            refine ⟨3487072802943607027731587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9298860807849618740617565 3487072802943607027731587)
            ·
              refine ⟨5230609204415410541597381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3487072802943607027731587 5230609204415410541597381)
              ·
                refine ⟨980739225827889476549509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5230609204415410541597381 980739225827889476549509)
                ·
                  refine ⟨183888604842729276853033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 980739225827889476549509 183888604842729276853033)
                  ·
                    rfl

theorem cell20_402887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_402887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402887 prefixEnd_402887 := by exact prefixLift 402887
  have htrace : WordTrace (prefixWord ++ tailWord_402887) baseStart_402887 baseEnd_402887 := by
    simpa [prefixWord, tailWord_402887, baseEnd_402887] using wordTrace_append hprefix tailTrace_402887
  have hstable : (prefixWord ++ tailWord_402887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402887).length < 2 ^ (prefixWord ++ tailWord_402887).sum := by decide
  have hdescent : baseEnd_402887 < baseStart_402887 := by decide
  rcases family_descends (prefixWord ++ tailWord_402887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402890 : List Nat := [3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_402890 : Nat := 118140960795 + 402890 * 2 ^ 59
def prefixEnd_402890 : Nat := 4983230072969 + 3 ^ 40 * 402890 * 2
def baseEnd_402890 : Nat := 61296658041491533251007

theorem tailTrace_402890 : CollatzResearch.WordTrace tailWord_402890 prefixEnd_402890 61296658041491533251007 := by
  unfold tailWord_402890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673651377601453244753531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9796403673603875319342749 3673651377601453244753531)
  ·
    refine ⟨5510477066402179867130297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673651377601453244753531 5510477066402179867130297)
    ·
      refine ⟨4132857799801634900347723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5510477066402179867130297 4132857799801634900347723)
      ·
        refine ⟨6199286699702452350521585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132857799801634900347723 6199286699702452350521585)
        ·
          refine ⟨4649465024776839262891189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199286699702452350521585 4649465024776839262891189)
          ·
            refine ⟨435887346072828680896049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4649465024776839262891189 435887346072828680896049)
            ·
              refine ⟨326915509554621510672037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435887346072828680896049 326915509554621510672037)
              ·
                refine ⟨61296658041491533251007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326915509554621510672037 61296658041491533251007)
                ·
                  rfl

theorem cell20_402890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_402890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402890 prefixEnd_402890 := by exact prefixLift 402890
  have htrace : WordTrace (prefixWord ++ tailWord_402890) baseStart_402890 baseEnd_402890 := by
    simpa [prefixWord, tailWord_402890, baseEnd_402890] using wordTrace_append hprefix tailTrace_402890
  have hstable : (prefixWord ++ tailWord_402890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402890).length < 2 ^ (prefixWord ++ tailWord_402890).sum := by decide
  have hdescent : baseEnd_402890 < baseStart_402890 := by decide
  rcases family_descends (prefixWord ++ tailWord_402890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402973 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_402973 : Nat := 118140960795 + 402973 * 2 ^ 59
def prefixEnd_402973 : Nat := 4983230072969 + 3 ^ 40 * 402973 * 2
def baseEnd_402973 : Nat := 183927857586095199986015

theorem tailTrace_402973 : CollatzResearch.WordTrace tailWord_402973 prefixEnd_402973 183927857586095199986015 := by
  unfold tailWord_402973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697632769105118154285573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9798421846070078769523715 14697632769105118154285573)
  ·
    refine ⟨2755806144207209653928545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14697632769105118154285573 2755806144207209653928545)
    ·
      refine ⟨2066854608155407240446409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2755806144207209653928545 2066854608155407240446409)
      ·
        refine ⟨1550140956116555430334807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066854608155407240446409 1550140956116555430334807)
        ·
          refine ⟨2325211434174833145502211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550140956116555430334807 2325211434174833145502211)
          ·
            refine ⟨3487817151262249718253317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325211434174833145502211 3487817151262249718253317)
            ·
              refine ⟨653965715861671822172497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3487817151262249718253317 653965715861671822172497)
              ·
                refine ⟨490474286896253866629373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653965715861671822172497 490474286896253866629373)
                ·
                  refine ⟨183927857586095199986015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490474286896253866629373 183927857586095199986015)
                  ·
                    rfl

theorem cell20_402973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_402973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402973 prefixEnd_402973 := by exact prefixLift 402973
  have htrace : WordTrace (prefixWord ++ tailWord_402973) baseStart_402973 baseEnd_402973 := by
    simpa [prefixWord, tailWord_402973, baseEnd_402973] using wordTrace_append hprefix tailTrace_402973
  have hstable : (prefixWord ++ tailWord_402973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402973).length < 2 ^ (prefixWord ++ tailWord_402973).sum := by decide
  have hdescent : baseEnd_402973 < baseStart_402973 := by decide
  rcases family_descends (prefixWord ++ tailWord_402973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402976 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_402976 : Nat := 118140960795 + 402976 * 2 ^ 59
def prefixEnd_402976 : Nat := 4983230072969 + 3 ^ 40 * 402976 * 2
def baseEnd_402976 : Nat := 183929226867840522886003

theorem tailTrace_402976 : CollatzResearch.WordTrace tailWord_402976 prefixEnd_402976 183929226867840522886003 := by
  unfold tailWord_402976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348871094047124833322391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9798494792062833111096521 7348871094047124833322391)
  ·
    refine ⟨11023306641070687249983587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348871094047124833322391 11023306641070687249983587)
    ·
      refine ⟨16534959961606030874975381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023306641070687249983587 16534959961606030874975381)
      ·
        refine ⟨775076248200282697264471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16534959961606030874975381 775076248200282697264471)
        ·
          refine ⟨1162614372300424045896707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775076248200282697264471 1162614372300424045896707)
          ·
            refine ⟨1743921558450636068845061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162614372300424045896707 1743921558450636068845061)
            ·
              refine ⟨326985292209494262908449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1743921558450636068845061 326985292209494262908449)
              ·
                refine ⟨245238969157120697181337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326985292209494262908449 245238969157120697181337)
                ·
                  refine ⟨183929226867840522886003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245238969157120697181337 183929226867840522886003)
                  ·
                    rfl

theorem cell20_402976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_402976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_402976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_402976 prefixEnd_402976 := by exact prefixLift 402976
  have htrace : WordTrace (prefixWord ++ tailWord_402976) baseStart_402976 baseEnd_402976 := by
    simpa [prefixWord, tailWord_402976, baseEnd_402976] using wordTrace_append hprefix tailTrace_402976
  have hstable : (prefixWord ++ tailWord_402976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402976).length < 2 ^ (prefixWord ++ tailWord_402976).sum := by decide
  have hdescent : baseEnd_402976 < baseStart_402976 := by decide
  rcases family_descends (prefixWord ++ tailWord_402976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403001 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_403001 : Nat := 118140960795 + 403001 * 2 ^ 59
def prefixEnd_403001 : Nat := 4983230072969 + 3 ^ 40 * 403001 * 2
def baseEnd_403001 : Nat := 183940637549051547052567

theorem tailTrace_403001 : CollatzResearch.WordTrace tailWord_403001 prefixEnd_403001 183940637549051547052567 := by
  unfold tailWord_403001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14698654013003678936304857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9799102675335785957536571 14698654013003678936304857)
  ·
    refine ⟨11023990509752759202228643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14698654013003678936304857 11023990509752759202228643)
    ·
      refine ⟨16535985764629138803342965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023990509752759202228643 16535985764629138803342965)
      ·
        refine ⟨1550248665433981762813403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16535985764629138803342965 1550248665433981762813403)
        ·
          refine ⟨2325372998150972644220105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550248665433981762813403 2325372998150972644220105)
          ·
            refine ⟨1744029748613229483165079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325372998150972644220105 1744029748613229483165079)
            ·
              refine ⟨2616044622919844224747619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744029748613229483165079 2616044622919844224747619)
              ·
                refine ⟨3924066934379766337121429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616044622919844224747619 3924066934379766337121429)
                ·
                  refine ⟨183940637549051547052567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3924066934379766337121429 183940637549051547052567)
                  ·
                    rfl

theorem cell20_403001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_403001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403001 prefixEnd_403001 := by exact prefixLift 403001
  have htrace : WordTrace (prefixWord ++ tailWord_403001) baseStart_403001 baseEnd_403001 := by
    simpa [prefixWord, tailWord_403001, baseEnd_403001] using wordTrace_append hprefix tailTrace_403001
  have hstable : (prefixWord ++ tailWord_403001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403001).length < 2 ^ (prefixWord ++ tailWord_403001).sum := by decide
  have hdescent : baseEnd_403001 < baseStart_403001 := by decide
  rcases family_descends (prefixWord ++ tailWord_403001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403004 : List Nat := [2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_403004 : Nat := 118140960795 + 403004 * 2 ^ 59
def prefixEnd_403004 : Nat := 4983230072969 + 3 ^ 40 * 403004 * 2
def baseEnd_403004 : Nat := 61314002276932289984185

theorem tailTrace_403004 : CollatzResearch.WordTrace tailWord_403004 prefixEnd_403004 61314002276932289984185 := by
  unfold tailWord_403004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349381715996405224332033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9799175621328540299109377 7349381715996405224332033)
  ·
    refine ⟨5512036286997303918249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7349381715996405224332033 5512036286997303918249025)
    ·
      refine ⟨4134027215247977938686769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5512036286997303918249025 4134027215247977938686769)
      ·
        refine ⟨3100520411435983454015077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4134027215247977938686769 3100520411435983454015077)
        ·
          refine ⟨581347577144246897627827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3100520411435983454015077 581347577144246897627827)
          ·
            refine ⟨872021365716370346441741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581347577144246897627827 872021365716370346441741)
            ·
              refine ⟨327008012143638879915653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872021365716370346441741 327008012143638879915653)
              ·
                refine ⟨61314002276932289984185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327008012143638879915653 61314002276932289984185)
                ·
                  rfl

theorem cell20_403004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_403004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403004 prefixEnd_403004 := by exact prefixLift 403004
  have htrace : WordTrace (prefixWord ++ tailWord_403004) baseStart_403004 baseEnd_403004 := by
    simpa [prefixWord, tailWord_403004, baseEnd_403004] using wordTrace_append hprefix tailTrace_403004
  have hstable : (prefixWord ++ tailWord_403004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403004).length < 2 ^ (prefixWord ++ tailWord_403004).sum := by decide
  have hdescent : baseEnd_403004 < baseStart_403004 := by decide
  rcases family_descends (prefixWord ++ tailWord_403004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403073 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 2]
def baseStart_403073 : Nat := 118140960795 + 403073 * 2 ^ 59
def prefixEnd_403073 : Nat := 4983230072969 + 3 ^ 40 * 403073 * 2
def baseEnd_403073 : Nat := 183973500310939296652273

theorem tailTrace_403073 : CollatzResearch.WordTrace tailWord_403073 prefixEnd_403073 183973500310939296652273 := by
  unfold tailWord_403073
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701280068742835232925873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9800853379161890155283915 14701280068742835232925873)
  ·
    refine ⟨11025960051557126424694405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14701280068742835232925873 11025960051557126424694405)
    ·
      refine ⟨2067367509666961204630201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11025960051557126424694405 2067367509666961204630201)
      ·
        refine ⟨1550525632250220903472651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067367509666961204630201 1550525632250220903472651)
        ·
          refine ⟨2325788448375331355208977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550525632250220903472651 2325788448375331355208977)
          ·
            refine ⟨1744341336281498516406733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325788448375331355208977 1744341336281498516406733)
            ·
              refine ⟨654128001105561943652525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1744341336281498516406733 654128001105561943652525)
              ·
                refine ⟨245298000414585728869697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654128001105561943652525 245298000414585728869697)
                ·
                  refine ⟨183973500310939296652273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245298000414585728869697 183973500310939296652273)
                  ·
                    rfl

theorem cell20_403073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_403073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403073 prefixEnd_403073 := by exact prefixLift 403073
  have htrace : WordTrace (prefixWord ++ tailWord_403073) baseStart_403073 baseEnd_403073 := by
    simpa [prefixWord, tailWord_403073, baseEnd_403073] using wordTrace_append hprefix tailTrace_403073
  have hstable : (prefixWord ++ tailWord_403073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403073).length < 2 ^ (prefixWord ++ tailWord_403073).sum := by decide
  have hdescent : baseEnd_403073 < baseStart_403073 := by decide
  rcases family_descends (prefixWord ++ tailWord_403073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403080 : List Nat := [2, 1, 3, 5, 1, 2, 6]
def baseStart_403080 : Nat := 118140960795 + 403080 * 2 ^ 59
def prefixEnd_403080 : Nat := 4983230072969 + 3 ^ 40 * 403080 * 2
def baseEnd_403080 : Nat := 20441855033519820379879

theorem tailTrace_403080 : CollatzResearch.WordTrace tailWord_403080 prefixEnd_403080 20441855033519820379879 := by
  unfold tailWord_403080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350767689858737714215347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9801023586478316952287129 7350767689858737714215347)
  ·
    refine ⟨11026151534788106571323021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350767689858737714215347 11026151534788106571323021)
    ·
      refine ⟨4134806825545539964246133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11026151534788106571323021 4134806825545539964246133)
      ·
        refine ⟨387638139894894371648075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4134806825545539964246133 387638139894894371648075)
        ·
          refine ⟨581457209842341557472113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387638139894894371648075 581457209842341557472113)
          ·
            refine ⟨436092907381756168104085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581457209842341557472113 436092907381756168104085)
            ·
              refine ⟨20441855033519820379879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 436092907381756168104085 20441855033519820379879)
              ·
                rfl

theorem cell20_403080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_403080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403080 prefixEnd_403080 := by exact prefixLift 403080
  have htrace : WordTrace (prefixWord ++ tailWord_403080) baseStart_403080 baseEnd_403080 := by
    simpa [prefixWord, tailWord_403080, baseEnd_403080] using wordTrace_append hprefix tailTrace_403080
  have hstable : (prefixWord ++ tailWord_403080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403080).length < 2 ^ (prefixWord ++ tailWord_403080).sum := by decide
  have hdescent : baseEnd_403080 < baseStart_403080 := by decide
  rcases family_descends (prefixWord ++ tailWord_403080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403090 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_403090 : Nat := 118140960795 + 403090 * 2 ^ 59
def prefixEnd_403090 : Nat := 4983230072969 + 3 ^ 40 * 403090 * 2
def baseEnd_403090 : Nat := 183981259574162793085537

theorem tailTrace_403090 : CollatzResearch.WordTrace tailWord_403090 prefixEnd_403090 183981259574162793085537 := by
  unfold tailWord_403090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675475027420311784073681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9801266739787498090863149 3675475027420311784073681)
  ·
    refine ⟨2756606270565233838055261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3675475027420311784073681 2756606270565233838055261)
    ·
      refine ⟨1033727351461962689270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2756606270565233838055261 1033727351461962689270723)
      ·
        refine ⟨1550591027192944033906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033727351461962689270723 1550591027192944033906085)
        ·
          refine ⟨290735817598677006357391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1550591027192944033906085 290735817598677006357391)
          ·
            refine ⟨436103726398015509536087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290735817598677006357391 436103726398015509536087)
            ·
              refine ⟨654155589597023264304131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436103726398015509536087 654155589597023264304131)
              ·
                refine ⟨981233384395534896456197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654155589597023264304131 981233384395534896456197)
                ·
                  refine ⟨183981259574162793085537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981233384395534896456197 183981259574162793085537)
                  ·
                    rfl

theorem cell20_403090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_403090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403090 prefixEnd_403090 := by exact prefixLift 403090
  have htrace : WordTrace (prefixWord ++ tailWord_403090) baseStart_403090 baseEnd_403090 := by
    simpa [prefixWord, tailWord_403090, baseEnd_403090] using wordTrace_append hprefix tailTrace_403090
  have hstable : (prefixWord ++ tailWord_403090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403090).length < 2 ^ (prefixWord ++ tailWord_403090).sum := by decide
  have hdescent : baseEnd_403090 < baseStart_403090 := by decide
  rcases family_descends (prefixWord ++ tailWord_403090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403104 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_403104 : Nat := 118140960795 + 403104 * 2 ^ 59
def prefixEnd_403104 : Nat := 4983230072969 + 3 ^ 40 * 403104 * 2
def baseEnd_403104 : Nat := 183987649555640966618813

theorem tailTrace_403104 : CollatzResearch.WordTrace tailWord_403104 prefixEnd_403104 183987649555640966618813 := by
  unfold tailWord_403104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351205365815263763652183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9801607154420351684869577 7351205365815263763652183)
  ·
    refine ⟨11026808048722895645478275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351205365815263763652183 11026808048722895645478275)
    ·
      refine ⟨16540212073084343468217413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11026808048722895645478275 16540212073084343468217413)
      ·
        refine ⟨3101289763703314400290765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16540212073084343468217413 3101289763703314400290765)
        ·
          refine ⟨1162983661388742900109037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3101289763703314400290765 1162983661388742900109037)
          ·
            refine ⟨436118873020778587540889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1162983661388742900109037 436118873020778587540889)
            ·
              refine ⟨327089154765583940655667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436118873020778587540889 327089154765583940655667)
              ·
                refine ⟨490633732148375910983501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327089154765583940655667 490633732148375910983501)
                ·
                  refine ⟨183987649555640966618813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490633732148375910983501 183987649555640966618813)
                  ·
                    rfl

theorem cell20_403104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_403104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403104 prefixEnd_403104 := by exact prefixLift 403104
  have htrace : WordTrace (prefixWord ++ tailWord_403104) baseStart_403104 baseEnd_403104 := by
    simpa [prefixWord, tailWord_403104, baseEnd_403104] using wordTrace_append hprefix tailTrace_403104
  have hstable : (prefixWord ++ tailWord_403104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403104).length < 2 ^ (prefixWord ++ tailWord_403104).sum := by decide
  have hdescent : baseEnd_403104 < baseStart_403104 := by decide
  rcases family_descends (prefixWord ++ tailWord_403104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403122 : List Nat := [3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_403122 : Nat := 118140960795 + 403122 * 2 ^ 59
def prefixEnd_403122 : Nat := 4983230072969 + 3 ^ 40 * 403122 * 2
def baseEnd_403122 : Nat := 61331955082037634672913

theorem tailTrace_403122 : CollatzResearch.WordTrace tailWord_403122 prefixEnd_403122 61331955082037634672913 := by
  unfold tailWord_403122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675766811391329150364905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9802044830376877734306413 3675766811391329150364905)
  ·
    refine ⟨2756825108543496862773679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3675766811391329150364905 2756825108543496862773679)
    ·
      refine ⟨4135237662815245294160519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2756825108543496862773679 4135237662815245294160519)
      ·
        refine ⟨6202856494222867941240779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135237662815245294160519 6202856494222867941240779)
        ·
          refine ⟨9304284741334301911861169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202856494222867941240779 9304284741334301911861169)
          ·
            refine ⟨6978213556000726433895877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9304284741334301911861169 6978213556000726433895877)
            ·
              refine ⟨1308415041750136206355477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6978213556000726433895877 1308415041750136206355477)
              ·
                refine ⟨61331955082037634672913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1308415041750136206355477 61331955082037634672913)
                ·
                  rfl

theorem cell20_403122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_403122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403122 prefixEnd_403122 := by exact prefixLift 403122
  have htrace : WordTrace (prefixWord ++ tailWord_403122) baseStart_403122 baseEnd_403122 := by
    simpa [prefixWord, tailWord_403122, baseEnd_403122] using wordTrace_append hprefix tailTrace_403122
  have hstable : (prefixWord ++ tailWord_403122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403122).length < 2 ^ (prefixWord ++ tailWord_403122).sum := by decide
  have hdescent : baseEnd_403122 < baseStart_403122 := by decide
  rcases family_descends (prefixWord ++ tailWord_403122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403129 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_403129 : Nat := 118140960795 + 403129 * 2 ^ 59
def prefixEnd_403129 : Nat := 4983230072969 + 3 ^ 40 * 403129 * 2
def baseEnd_403129 : Nat := 183999060236851990785377

theorem tailTrace_403129 : CollatzResearch.WordTrace tailWord_403129 prefixEnd_403129 183999060236851990785377 := by
  unfold tailWord_403129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703322556539956796964441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9802215037693304531309627 14703322556539956796964441)
  ·
    refine ⟨11027491917404967597723331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14703322556539956796964441 11027491917404967597723331)
    ·
      refine ⟨16541237876107451396584997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027491917404967597723331 16541237876107451396584997)
      ·
        refine ⟨3101482101770147136859687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16541237876107451396584997 3101482101770147136859687)
        ·
          refine ⟨4652223152655220705289531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101482101770147136859687 4652223152655220705289531)
          ·
            refine ⟨6978334728982831057934297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652223152655220705289531 6978334728982831057934297)
            ·
              refine ⟨5233751046737123293450723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6978334728982831057934297 5233751046737123293450723)
              ·
                refine ⟨7850626570105684940176085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233751046737123293450723 7850626570105684940176085)
                ·
                  refine ⟨183999060236851990785377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7850626570105684940176085 183999060236851990785377)
                  ·
                    rfl

theorem cell20_403129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_403129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403129 prefixEnd_403129 := by exact prefixLift 403129
  have htrace : WordTrace (prefixWord ++ tailWord_403129) baseStart_403129 baseEnd_403129 := by
    simpa [prefixWord, tailWord_403129, baseEnd_403129] using wordTrace_append hprefix tailTrace_403129
  have hstable : (prefixWord ++ tailWord_403129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403129).length < 2 ^ (prefixWord ++ tailWord_403129).sum := by decide
  have hdescent : baseEnd_403129 < baseStart_403129 := by decide
  rcases family_descends (prefixWord ++ tailWord_403129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403138 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_403138 : Nat := 118140960795 + 403138 * 2 ^ 59
def prefixEnd_403138 : Nat := 4983230072969 + 3 ^ 40 * 403138 * 2
def baseEnd_403138 : Nat := 184003168082087959485341

theorem tailTrace_403138 : CollatzResearch.WordTrace tailWord_403138 prefixEnd_403138 184003168082087959485341 := by
  unfold tailWord_403138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675912703376837833510517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9802433875671567556028045 3675912703376837833510517)
  ·
    refine ⟨344616815941578546891611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3675912703376837833510517 344616815941578546891611)
    ·
      refine ⟨516925223912367820337417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344616815941578546891611 516925223912367820337417)
      ·
        refine ⟨387693917934275865253063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516925223912367820337417 387693917934275865253063)
        ·
          refine ⟨581540876901413797879595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387693917934275865253063 581540876901413797879595)
          ·
            refine ⟨872311315352120696819393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581540876901413797879595 872311315352120696819393)
            ·
              refine ⟨654233486514090522614545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872311315352120696819393 654233486514090522614545)
              ·
                refine ⟨490675114885567891960909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654233486514090522614545 490675114885567891960909)
                ·
                  refine ⟨184003168082087959485341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490675114885567891960909 184003168082087959485341)
                  ·
                    rfl

theorem cell20_403138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_403138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403138 prefixEnd_403138 := by exact prefixLift 403138
  have htrace : WordTrace (prefixWord ++ tailWord_403138) baseStart_403138 baseEnd_403138 := by
    simpa [prefixWord, tailWord_403138, baseEnd_403138] using wordTrace_append hprefix tailTrace_403138
  have hstable : (prefixWord ++ tailWord_403138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403138).length < 2 ^ (prefixWord ++ tailWord_403138).sum := by decide
  have hdescent : baseEnd_403138 < baseStart_403138 := by decide
  rcases family_descends (prefixWord ++ tailWord_403138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403156 : List Nat := [2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_403156 : Nat := 118140960795 + 403156 * 2 ^ 59
def prefixEnd_403156 : Nat := 4983230072969 + 3 ^ 40 * 403156 * 2
def baseEnd_403156 : Nat := 61337127924186632295089

theorem tailTrace_403156 : CollatzResearch.WordTrace tailWord_403156 prefixEnd_403156 61337127924186632295089 := by
  unfold tailWord_403156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352153663721070204098661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9802871551628093605464881 7352153663721070204098661)
  ·
    refine ⟨1378528811947700663268499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7352153663721070204098661 1378528811947700663268499)
    ·
      refine ⟨2067793217921550994902749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378528811947700663268499 2067793217921550994902749)
      ·
        refine ⟨775422456720581623088531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2067793217921550994902749 775422456720581623088531)
        ·
          refine ⟨1163133685080872434632797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775422456720581623088531 1163133685080872434632797)
          ·
            refine ⟨436175131905327162987299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163133685080872434632797 436175131905327162987299)
            ·
              refine ⟨654262697857990744480949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436175131905327162987299 654262697857990744480949)
              ·
                refine ⟨61337127924186632295089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 654262697857990744480949 61337127924186632295089)
                ·
                  rfl

theorem cell20_403156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_403156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403156 prefixEnd_403156 := by exact prefixLift 403156
  have htrace : WordTrace (prefixWord ++ tailWord_403156) baseStart_403156 baseEnd_403156 := by
    simpa [prefixWord, tailWord_403156, baseEnd_403156] using wordTrace_append hprefix tailTrace_403156
  have hstable : (prefixWord ++ tailWord_403156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403156).length < 2 ^ (prefixWord ++ tailWord_403156).sum := by decide
  have hdescent : baseEnd_403156 < baseStart_403156 := by decide
  rcases family_descends (prefixWord ++ tailWord_403156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403208 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_403208 : Nat := 118140960795 + 403208 * 2 ^ 59
def prefixEnd_403208 : Nat := 4983230072969 + 3 ^ 40 * 403208 * 2
def baseEnd_403208 : Nat := 184035117989478827151721

theorem tailTrace_403208 : CollatzResearch.WordTrace tailWord_403208 prefixEnd_403208 184035117989478827151721 := by
  unfold tailWord_403208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353101961626876644545139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9804135948835835526060185 7353101961626876644545139)
  ·
    refine ⟨11029652942440314966817709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7353101961626876644545139 11029652942440314966817709)
    ·
      refine ⟨4136119853415118112556641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11029652942440314966817709 4136119853415118112556641)
      ·
        refine ⟨3102089890061338584417481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136119853415118112556641 3102089890061338584417481)
        ·
          refine ⟨2326567417546003938313111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102089890061338584417481 2326567417546003938313111)
          ·
            refine ⟨3489851126319005907469667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326567417546003938313111 3489851126319005907469667)
            ·
              refine ⟨5234776689478508861204501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489851126319005907469667 5234776689478508861204501)
              ·
                refine ⟨245380157319305102868961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5234776689478508861204501 245380157319305102868961)
                ·
                  refine ⟨184035117989478827151721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245380157319305102868961 184035117989478827151721)
                  ·
                    rfl

theorem cell20_403208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_403208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403208 prefixEnd_403208 := by exact prefixLift 403208
  have htrace : WordTrace (prefixWord ++ tailWord_403208) baseStart_403208 baseEnd_403208 := by
    simpa [prefixWord, tailWord_403208, baseEnd_403208] using wordTrace_append hprefix tailTrace_403208
  have hstable : (prefixWord ++ tailWord_403208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403208).length < 2 ^ (prefixWord ++ tailWord_403208).sum := by decide
  have hdescent : baseEnd_403208 < baseStart_403208 := by decide
  rcases family_descends (prefixWord ++ tailWord_403208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403253 : List Nat := [1, 3, 3, 1, 4, 2, 6]
def baseStart_403253 : Nat := 118140960795 + 403253 * 2 ^ 59
def prefixEnd_403253 : Nat := 4983230072969 + 3 ^ 40 * 403253 * 2
def baseEnd_403253 : Nat := 20450628579517630072393

theorem tailTrace_403253 : CollatzResearch.WordTrace tailWord_403253 prefixEnd_403253 20450628579517630072393 := by
  unfold tailWord_403253
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707845208090725974478413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9805230138727150649652275 14707845208090725974478413)
  ·
    refine ⟨5515441953034022240429405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14707845208090725974478413 5515441953034022240429405)
    ·
      refine ⟨2068290732387758340161027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5515441953034022240429405 2068290732387758340161027)
      ·
        refine ⟨3102436098581637510241541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068290732387758340161027 3102436098581637510241541)
        ·
          refine ⟨581706768484057033170289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3102436098581637510241541 581706768484057033170289)
          ·
            refine ⟨436280076363042774877717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581706768484057033170289 436280076363042774877717)
            ·
              refine ⟨20450628579517630072393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 436280076363042774877717 20450628579517630072393)
              ·
                rfl

theorem cell20_403253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_403253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403253 prefixEnd_403253 := by exact prefixLift 403253
  have htrace : WordTrace (prefixWord ++ tailWord_403253) baseStart_403253 baseEnd_403253 := by
    simpa [prefixWord, tailWord_403253, baseEnd_403253] using wordTrace_append hprefix tailTrace_403253
  have hstable : (prefixWord ++ tailWord_403253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403253).length < 2 ^ (prefixWord ++ tailWord_403253).sum := by decide
  have hdescent : baseEnd_403253 < baseStart_403253 := by decide
  rcases family_descends (prefixWord ++ tailWord_403253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403263 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 4]
def baseStart_403263 : Nat := 118140960795 + 403263 * 2 ^ 59
def prefixEnd_403263 : Nat := 4983230072969 + 3 ^ 40 * 403263 * 2
def baseEnd_403263 : Nat := 184060221488143080318163

theorem tailTrace_403263 : CollatzResearch.WordTrace tailWord_403263 prefixEnd_403263 184060221488143080318163 := by
  unfold tailWord_403263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708209938054497682342443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9805473292036331788228295 14708209938054497682342443)
  ·
    refine ⟨22062314907081746523513665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14708209938054497682342443 22062314907081746523513665)
    ·
      refine ⟨16546736180311309892635249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22062314907081746523513665 16546736180311309892635249)
      ·
        refine ⟨12410052135233482419476437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16546736180311309892635249 12410052135233482419476437)
        ·
          refine ⟨290860596919534744206479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12410052135233482419476437 290860596919534744206479)
          ·
            refine ⟨436290895379302116309719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290860596919534744206479 436290895379302116309719)
            ·
              refine ⟨654436343068953174464579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436290895379302116309719 654436343068953174464579)
              ·
                refine ⟨981654514603429761696869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654436343068953174464579 981654514603429761696869)
                ·
                  refine ⟨184060221488143080318163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981654514603429761696869 184060221488143080318163)
                  ·
                    rfl

theorem cell20_403263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4].length) (baseStart_403263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403263 prefixEnd_403263 := by exact prefixLift 403263
  have htrace : WordTrace (prefixWord ++ tailWord_403263) baseStart_403263 baseEnd_403263 := by
    simpa [prefixWord, tailWord_403263, baseEnd_403263] using wordTrace_append hprefix tailTrace_403263
  have hstable : (prefixWord ++ tailWord_403263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403263).length < 2 ^ (prefixWord ++ tailWord_403263).sum := by decide
  have hdescent : baseEnd_403263 < baseStart_403263 := by decide
  rcases family_descends (prefixWord ++ tailWord_403263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403267 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_403267 : Nat := 118140960795 + 403267 * 2 ^ 59
def prefixEnd_403267 : Nat := 4983230072969 + 3 ^ 40 * 403267 * 2
def baseEnd_403267 : Nat := 184062047197136844184813

theorem tailTrace_403267 : CollatzResearch.WordTrace tailWord_403267 prefixEnd_403267 184062047197136844184813 := by
  unfold tailWord_403267
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708355830040006365488055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9805570553360004243658703 14708355830040006365488055)
  ·
    refine ⟨22062533745060009548232083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14708355830040006365488055 22062533745060009548232083)
    ·
      refine ⟨33093800617590014322348125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22062533745060009548232083 33093800617590014322348125)
      ·
        refine ⟨12410175231596255370880547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33093800617590014322348125 12410175231596255370880547)
        ·
          refine ⟨18615262847394383056320821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410175231596255370880547 18615262847394383056320821)
          ·
            refine ⟨1745180891943223411530077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18615262847394383056320821 1745180891943223411530077)
            ·
              refine ⟨654442834478708779323779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1745180891943223411530077 654442834478708779323779)
              ·
                refine ⟨981664251718063168985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654442834478708779323779 981664251718063168985669)
                ·
                  refine ⟨184062047197136844184813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981664251718063168985669 184062047197136844184813)
                  ·
                    rfl

theorem cell20_403267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_403267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403267 prefixEnd_403267 := by exact prefixLift 403267
  have htrace : WordTrace (prefixWord ++ tailWord_403267) baseStart_403267 baseEnd_403267 := by
    simpa [prefixWord, tailWord_403267, baseEnd_403267] using wordTrace_append hprefix tailTrace_403267
  have hstable : (prefixWord ++ tailWord_403267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403267).length < 2 ^ (prefixWord ++ tailWord_403267).sum := by decide
  have hdescent : baseEnd_403267 < baseStart_403267 := by decide
  rcases family_descends (prefixWord ++ tailWord_403267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403270 : List Nat := [6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_403270 : Nat := 118140960795 + 403270 * 2 ^ 59
def prefixEnd_403270 : Nat := 4983230072969 + 3 ^ 40 * 403270 * 2
def baseEnd_403270 : Nat := 61354472159627389028267

theorem tailTrace_403270 : CollatzResearch.WordTrace tailWord_403270 prefixEnd_403270 61354472159627389028267 := by
  unfold tailWord_403270
  simp only [CollatzResearch.WordTrace]
  refine ⟨459639539032160558682727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9805643499352758585231509 459639539032160558682727)
  ·
    refine ⟨689459308548240838024091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459639539032160558682727 689459308548240838024091)
    ·
      refine ⟨1034188962822361257036137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689459308548240838024091 1034188962822361257036137)
      ·
        refine ⟨775641722116770942777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034188962822361257036137 775641722116770942777103)
        ·
          refine ⟨1163462583175156414165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775641722116770942777103 1163462583175156414165655)
          ·
            refine ⟨1745193874762734621248483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163462583175156414165655 1745193874762734621248483)
            ·
              refine ⟨2617790812144101931872725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745193874762734621248483 2617790812144101931872725)
              ·
                refine ⟨61354472159627389028267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2617790812144101931872725 61354472159627389028267)
                ·
                  rfl

theorem cell20_403270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_403270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403270 prefixEnd_403270 := by exact prefixLift 403270
  have htrace : WordTrace (prefixWord ++ tailWord_403270) baseStart_403270 baseEnd_403270 := by
    simpa [prefixWord, tailWord_403270, baseEnd_403270] using wordTrace_append hprefix tailTrace_403270
  have hstable : (prefixWord ++ tailWord_403270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403270).length < 2 ^ (prefixWord ++ tailWord_403270).sum := by decide
  have hdescent : baseEnd_403270 < baseStart_403270 := by decide
  rcases family_descends (prefixWord ++ tailWord_403270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403274 : List Nat := [3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_403274 : Nat := 118140960795 + 403274 * 2 ^ 59
def prefixEnd_403274 : Nat := 4983230072969 + 3 ^ 40 * 403274 * 2
def baseEnd_403274 : Nat := 61355080729291976983817

theorem tailTrace_403274 : CollatzResearch.WordTrace tailWord_403274 prefixEnd_403274 61355080729291976983817 := by
  unfold tailWord_403274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677152785253661640248219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9805740760676431040661917 3677152785253661640248219)
  ·
    refine ⟨5515729177880492460372329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677152785253661640248219 5515729177880492460372329)
    ·
      refine ⟨4136796883410369345279247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5515729177880492460372329 4136796883410369345279247)
      ·
        refine ⟨6205195325115554017918871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136796883410369345279247 6205195325115554017918871)
        ·
          refine ⟨9307792987673331026878307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205195325115554017918871 9307792987673331026878307)
          ·
            refine ⟨13961689481509996540317461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9307792987673331026878307 13961689481509996540317461)
            ·
              refine ⟨654454194445781087827381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13961689481509996540317461 654454194445781087827381)
              ·
                refine ⟨61355080729291976983817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 654454194445781087827381 61355080729291976983817)
                ·
                  rfl

theorem cell20_403274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_403274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403274 prefixEnd_403274 := by exact prefixLift 403274
  have htrace : WordTrace (prefixWord ++ tailWord_403274) baseStart_403274 baseEnd_403274 := by
    simpa [prefixWord, tailWord_403274, baseEnd_403274] using wordTrace_append hprefix tailTrace_403274
  have hstable : (prefixWord ++ tailWord_403274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403274).length < 2 ^ (prefixWord ++ tailWord_403274).sum := by decide
  have hdescent : baseEnd_403274 < baseStart_403274 := by decide
  rcases family_descends (prefixWord ++ tailWord_403274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403318 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_403318 : Nat := 118140960795 + 403318 * 2 ^ 59
def prefixEnd_403318 : Nat := 4983230072969 + 3 ^ 40 * 403318 * 2
def baseEnd_403318 : Nat := 184085324986807333484605

theorem tailTrace_403318 : CollatzResearch.WordTrace tailWord_403318 prefixEnd_403318 184085324986807333484605 := by
  unfold tailWord_403318
  simp only [CollatzResearch.WordTrace]
  refine ⟨919388497053452629724663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9806810635236828050396405 919388497053452629724663)
  ·
    refine ⟨1379082745580178944586995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919388497053452629724663 1379082745580178944586995)
    ·
      refine ⟨2068624118370268416880493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379082745580178944586995 2068624118370268416880493)
      ·
        refine ⟨775734044388850656330185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2068624118370268416880493 775734044388850656330185)
        ·
          refine ⟨581800533291637992247639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775734044388850656330185 581800533291637992247639)
          ·
            refine ⟨872700799937456988371459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581800533291637992247639 872700799937456988371459)
            ·
              refine ⟨1309051199906185482557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872700799937456988371459 1309051199906185482557189)
              ·
                refine ⟨245447099982409777979473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1309051199906185482557189 245447099982409777979473)
                ·
                  refine ⟨184085324986807333484605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245447099982409777979473 184085324986807333484605)
                  ·
                    rfl

theorem cell20_403318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_403318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403318 prefixEnd_403318 := by exact prefixLift 403318
  have htrace : WordTrace (prefixWord ++ tailWord_403318) baseStart_403318 baseEnd_403318 := by
    simpa [prefixWord, tailWord_403318, baseEnd_403318] using wordTrace_append hprefix tailTrace_403318
  have hstable : (prefixWord ++ tailWord_403318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403318).length < 2 ^ (prefixWord ++ tailWord_403318).sum := by decide
  have hdescent : baseEnd_403318 < baseStart_403318 := by decide
  rcases family_descends (prefixWord ++ tailWord_403318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403346 : List Nat := [3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_403346 : Nat := 118140960795 + 403346 * 2 ^ 59
def prefixEnd_403346 : Nat := 4983230072969 + 3 ^ 40 * 403346 * 2
def baseEnd_403346 : Nat := 61366034983254560183719

theorem tailTrace_403346 : CollatzResearch.WordTrace tailWord_403346 prefixEnd_403346 61366034983254560183719 := by
  unfold tailWord_403346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677809299188450714403473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9807491464502535238409261 3677809299188450714403473)
  ·
    refine ⟨2758356974391338035802605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3677809299188450714403473 2758356974391338035802605)
    ·
      refine ⟨1034383865396751763425977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2758356974391338035802605 1034383865396751763425977)
      ·
        refine ⟨775787899047563822569483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1034383865396751763425977 775787899047563822569483)
        ·
          refine ⟨1163681848571345733854225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775787899047563822569483 1163681848571345733854225)
          ·
            refine ⟨872761386428509300390669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163681848571345733854225 872761386428509300390669)
            ·
              refine ⟨327285519910690987646501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872761386428509300390669 327285519910690987646501)
              ·
                refine ⟨61366034983254560183719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327285519910690987646501 61366034983254560183719)
                ·
                  rfl

theorem cell20_403346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_403346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403346 prefixEnd_403346 := by exact prefixLift 403346
  have htrace : WordTrace (prefixWord ++ tailWord_403346) baseStart_403346 baseEnd_403346 := by
    simpa [prefixWord, tailWord_403346, baseEnd_403346] using wordTrace_append hprefix tailTrace_403346
  have hstable : (prefixWord ++ tailWord_403346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403346).length < 2 ^ (prefixWord ++ tailWord_403346).sum := by decide
  have hdescent : baseEnd_403346 < baseStart_403346 := by decide
  rcases family_descends (prefixWord ++ tailWord_403346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403381 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_403381 : Nat := 118140960795 + 403381 * 2 ^ 59
def prefixEnd_403381 : Nat := 4983230072969 + 3 ^ 40 * 403381 * 2
def baseEnd_403381 : Nat := 184114079903459114384347

theorem tailTrace_403381 : CollatzResearch.WordTrace tailWord_403381 prefixEnd_403381 184114079903459114384347 := by
  unfold tailWord_403381
  simp only [CollatzResearch.WordTrace]
  refine ⟨14712513751627003835137997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9808342501084669223425331 14712513751627003835137997)
  ·
    refine ⟨5517192656860126438176749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14712513751627003835137997 5517192656860126438176749)
    ·
      refine ⟨2068947246322547414316281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5517192656860126438176749 2068947246322547414316281)
      ·
        refine ⟨1551710434741910560737211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2068947246322547414316281 1551710434741910560737211)
        ·
          refine ⟨2327565652112865841105817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551710434741910560737211 2327565652112865841105817)
          ·
            refine ⟨1745674239084649380829363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327565652112865841105817 1745674239084649380829363)
            ·
              refine ⟨2618511358626974071244045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745674239084649380829363 2618511358626974071244045)
              ·
                refine ⟨981941759485115276716517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2618511358626974071244045 981941759485115276716517)
                ·
                  refine ⟨184114079903459114384347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981941759485115276716517 184114079903459114384347)
                  ·
                    rfl

theorem cell20_403381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_403381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403381 prefixEnd_403381 := by exact prefixLift 403381
  have htrace : WordTrace (prefixWord ++ tailWord_403381) baseStart_403381 baseEnd_403381 := by
    simpa [prefixWord, tailWord_403381, baseEnd_403381] using wordTrace_append hprefix tailTrace_403381
  have hstable : (prefixWord ++ tailWord_403381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403381).length < 2 ^ (prefixWord ++ tailWord_403381).sum := by decide
  have hdescent : baseEnd_403381 < baseStart_403381 := by decide
  rcases family_descends (prefixWord ++ tailWord_403381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403533 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_403533 : Nat := 118140960795 + 403533 * 2 ^ 59
def prefixEnd_403533 : Nat := 4983230072969 + 3 ^ 40 * 403533 * 2
def baseEnd_403533 : Nat := 184183456845222141317059

theorem tailTrace_403533 : CollatzResearch.WordTrace tailWord_403533 prefixEnd_403533 184183456845222141317059 := by
  unfold tailWord_403533
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718057647076333794671253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9812038431384222529780835 14718057647076333794671253)
  ·
    refine ⟨689908952206703146625215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14718057647076333794671253 689908952206703146625215)
    ·
      refine ⟨1034863428310054719937823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689908952206703146625215 1034863428310054719937823)
      ·
        refine ⟨1552295142465082079906735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034863428310054719937823 1552295142465082079906735)
        ·
          refine ⟨2328442713697623119860103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552295142465082079906735 2328442713697623119860103)
          ·
            refine ⟨3492664070546434679790155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328442713697623119860103 3492664070546434679790155)
            ·
              refine ⟨5238996105819652019685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492664070546434679790155 5238996105819652019685233)
              ·
                refine ⟨3929247079364739014763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238996105819652019685233 3929247079364739014763925)
                ·
                  refine ⟨184183456845222141317059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3929247079364739014763925 184183456845222141317059)
                  ·
                    rfl

theorem cell20_403533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_403533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403533 prefixEnd_403533 := by exact prefixLift 403533
  have htrace : WordTrace (prefixWord ++ tailWord_403533) baseStart_403533 baseEnd_403533 := by
    simpa [prefixWord, tailWord_403533, baseEnd_403533] using wordTrace_append hprefix tailTrace_403533
  have hstable : (prefixWord ++ tailWord_403533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403533).length < 2 ^ (prefixWord ++ tailWord_403533).sum := by decide
  have hdescent : baseEnd_403533 < baseStart_403533 := by decide
  rcases family_descends (prefixWord ++ tailWord_403533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403561 : List Nat := [1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_403561 : Nat := 118140960795 + 403561 * 2 ^ 59
def prefixEnd_403561 : Nat := 4983230072969 + 3 ^ 40 * 403561 * 2
def baseEnd_403561 : Nat := 61398745602726162794537

theorem tailTrace_403561 : CollatzResearch.WordTrace tailWord_403561 prefixEnd_403561 61398745602726162794537 := by
  unfold tailWord_403561
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719078890974894576690537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9812719260649929717793691 14719078890974894576690537)
  ·
    refine ⟨11039309168231170932517903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14719078890974894576690537 11039309168231170932517903)
    ·
      refine ⟨16558963752346756398776855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039309168231170932517903 16558963752346756398776855)
      ·
        refine ⟨24838445628520134598165283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558963752346756398776855 24838445628520134598165283)
        ·
          refine ⟨37257668442780201897247925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24838445628520134598165283 37257668442780201897247925)
          ·
            refine ⟨3492906416510643927866993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37257668442780201897247925 3492906416510643927866993)
            ·
              refine ⟨2619679812382982945900245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492906416510643927866993 2619679812382982945900245)
              ·
                refine ⟨61398745602726162794537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2619679812382982945900245 61398745602726162794537)
                ·
                  rfl

theorem cell20_403561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_403561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403561 prefixEnd_403561 := by exact prefixLift 403561
  have htrace : WordTrace (prefixWord ++ tailWord_403561) baseStart_403561 baseEnd_403561 := by
    simpa [prefixWord, tailWord_403561, baseEnd_403561] using wordTrace_append hprefix tailTrace_403561
  have hstable : (prefixWord ++ tailWord_403561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403561).length < 2 ^ (prefixWord ++ tailWord_403561).sum := by decide
  have hdescent : baseEnd_403561 < baseStart_403561 := by decide
  rcases family_descends (prefixWord ++ tailWord_403561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403574 : List Nat := [5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_403574 : Nat := 118140960795 + 403574 * 2 ^ 59
def prefixEnd_403574 : Nat := 4983230072969 + 3 ^ 40 * 403574 * 2
def baseEnd_403574 : Nat := 61400723454136073650075

theorem tailTrace_403574 : CollatzResearch.WordTrace tailWord_403574 prefixEnd_403574 61400723454136073650075 := by
  unfold tailWord_403574
  simp only [CollatzResearch.WordTrace]
  refine ⟨919972064995487362307111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9813035359951865197942517 919972064995487362307111)
  ·
    refine ⟨1379958097493231043460667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919972064995487362307111 1379958097493231043460667)
    ·
      refine ⟨2069937146239846565191001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379958097493231043460667 2069937146239846565191001)
      ·
        refine ⟨1552452859679884923893251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069937146239846565191001 1552452859679884923893251)
        ·
          refine ⟨2328679289519827385839877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552452859679884923893251 2328679289519827385839877)
          ·
            refine ⟨436627366784967634844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2328679289519827385839877 436627366784967634844977)
            ·
              refine ⟨327470525088725726133733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436627366784967634844977 327470525088725726133733)
              ·
                refine ⟨61400723454136073650075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327470525088725726133733 61400723454136073650075)
                ·
                  rfl

theorem cell20_403574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_403574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403574 prefixEnd_403574 := by exact prefixLift 403574
  have htrace : WordTrace (prefixWord ++ tailWord_403574) baseStart_403574 baseEnd_403574 := by
    simpa [prefixWord, tailWord_403574, baseEnd_403574] using wordTrace_append hprefix tailTrace_403574
  have hstable : (prefixWord ++ tailWord_403574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403574).length < 2 ^ (prefixWord ++ tailWord_403574).sum := by decide
  have hdescent : baseEnd_403574 < baseStart_403574 := by decide
  rcases family_descends (prefixWord ++ tailWord_403574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403602 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_403602 : Nat := 118140960795 + 403602 * 2 ^ 59
def prefixEnd_403602 : Nat := 4983230072969 + 3 ^ 40 * 403602 * 2
def baseEnd_403602 : Nat := 184214950325364568016777

theorem tailTrace_403602 : CollatzResearch.WordTrace tailWord_403602 prefixEnd_403602 184214950325364568016777 := by
  unfold tailWord_403602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680143570956589644733265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9813716189217572385955373 3680143570956589644733265)
  ·
    refine ⟨2760107678217442233549949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3680143570956589644733265 2760107678217442233549949)
    ·
      refine ⟨1035040379331540837581231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2760107678217442233549949 1035040379331540837581231)
      ·
        refine ⟨1552560568997311256371847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035040379331540837581231 1552560568997311256371847)
        ·
          refine ⟨2328840853495966884557771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552560568997311256371847 2328840853495966884557771)
          ·
            refine ⟨3493261280243950326836657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328840853495966884557771 3493261280243950326836657)
            ·
              refine ⟨2619945960182962745127493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3493261280243950326836657 2619945960182962745127493)
              ·
                refine ⟨491239867534305514711405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2619945960182962745127493 491239867534305514711405)
                ·
                  refine ⟨184214950325364568016777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491239867534305514711405 184214950325364568016777)
                  ·
                    rfl

theorem cell20_403602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_403602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403602 prefixEnd_403602 := by exact prefixLift 403602
  have htrace : WordTrace (prefixWord ++ tailWord_403602) baseStart_403602 baseEnd_403602 := by
    simpa [prefixWord, tailWord_403602, baseEnd_403602] using wordTrace_append hprefix tailTrace_403602
  have hstable : (prefixWord ++ tailWord_403602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403602).length < 2 ^ (prefixWord ++ tailWord_403602).sum := by decide
  have hdescent : baseEnd_403602 < baseStart_403602 := by decide
  rcases family_descends (prefixWord ++ tailWord_403602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403609 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 2]
def baseStart_403609 : Nat := 118140960795 + 403609 * 2 ^ 59
def prefixEnd_403609 : Nat := 4983230072969 + 3 ^ 40 * 403609 * 2
def baseEnd_403609 : Nat := 184218145316103654783415

theorem tailTrace_403609 : CollatzResearch.WordTrace tailWord_403609 prefixEnd_403609 184218145316103654783415 := by
  unfold tailWord_403609
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720829594800998774437881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9813886396533999182958587 14720829594800998774437881)
  ·
    refine ⟨11040622196100749080828411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14720829594800998774437881 11040622196100749080828411)
    ·
      refine ⟨16560933294151123621242617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040622196100749080828411 16560933294151123621242617)
      ·
        refine ⟨12420699970613342715931963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16560933294151123621242617 12420699970613342715931963)
        ·
          refine ⟨18631049955920014073897945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12420699970613342715931963 18631049955920014073897945)
          ·
            refine ⟨13973287466940010555423459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631049955920014073897945 13973287466940010555423459)
            ·
              refine ⟨20959931200410015833135189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973287466940010555423459 20959931200410015833135189)
              ·
                refine ⟨245624193754804873044553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20959931200410015833135189 245624193754804873044553)
                ·
                  refine ⟨184218145316103654783415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245624193754804873044553 184218145316103654783415)
                  ·
                    rfl

theorem cell20_403609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_403609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403609 prefixEnd_403609 := by exact prefixLift 403609
  have htrace : WordTrace (prefixWord ++ tailWord_403609) baseStart_403609 baseEnd_403609 := by
    simpa [prefixWord, tailWord_403609, baseEnd_403609] using wordTrace_append hprefix tailTrace_403609
  have hstable : (prefixWord ++ tailWord_403609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403609).length < 2 ^ (prefixWord ++ tailWord_403609).sum := by decide
  have hdescent : baseEnd_403609 < baseStart_403609 := by decide
  rcases family_descends (prefixWord ++ tailWord_403609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403616 : List Nat := [2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_403616 : Nat := 118140960795 + 403616 * 2 ^ 59
def prefixEnd_403616 : Nat := 4983230072969 + 3 ^ 40 * 403616 * 2
def baseEnd_403616 : Nat := 61407113435614247183351

theorem tailTrace_403616 : CollatzResearch.WordTrace tailWord_403616 prefixEnd_403616 61407113435614247183351 := by
  unfold tailWord_403616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360542452887819484971351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9814056603850425979961801 7360542452887819484971351)
  ·
    refine ⟨11040813679331729227457027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360542452887819484971351 11040813679331729227457027)
    ·
      refine ⟨16561220518997593841185541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040813679331729227457027 16561220518997593841185541)
      ·
        refine ⟨3105228847312048845222289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16561220518997593841185541 3105228847312048845222289)
        ·
          refine ⟨2328921635484036633916717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3105228847312048845222289 2328921635484036633916717)
          ·
            refine ⟨873345613306513737718769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2328921635484036633916717 873345613306513737718769)
            ·
              refine ⟨655009209979885303289077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873345613306513737718769 655009209979885303289077)
              ·
                refine ⟨61407113435614247183351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655009209979885303289077 61407113435614247183351)
                ·
                  rfl

theorem cell20_403616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_403616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403616 prefixEnd_403616 := by exact prefixLift 403616
  have htrace : WordTrace (prefixWord ++ tailWord_403616) baseStart_403616 baseEnd_403616 := by
    simpa [prefixWord, tailWord_403616, baseEnd_403616] using wordTrace_append hprefix tailTrace_403616
  have hstable : (prefixWord ++ tailWord_403616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403616).length < 2 ^ (prefixWord ++ tailWord_403616).sum := by decide
  have hdescent : baseEnd_403616 < baseStart_403616 := by decide
  rcases family_descends (prefixWord ++ tailWord_403616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403647 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 2]
def baseStart_403647 : Nat := 118140960795 + 403647 * 2 ^ 59
def prefixEnd_403647 : Nat := 4983230072969 + 3 ^ 40 * 403647 * 2
def baseEnd_403647 : Nat := 184235489551544411516593

theorem tailTrace_403647 : CollatzResearch.WordTrace tailWord_403647 prefixEnd_403647 184235489551544411516593 := by
  unfold tailWord_403647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722215568663331264321195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9814810379108887509547463 14722215568663331264321195)
  ·
    refine ⟨22083323352994996896481793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722215568663331264321195 22083323352994996896481793)
    ·
      refine ⟨16562492514746247672361345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22083323352994996896481793 16562492514746247672361345)
      ·
        refine ⟨12421869386059685754271009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16562492514746247672361345 12421869386059685754271009)
        ·
          refine ⟨9316402039544764315703257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12421869386059685754271009 9316402039544764315703257)
          ·
            refine ⟨6987301529658573236777443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9316402039544764315703257 6987301529658573236777443)
            ·
              refine ⟨10480952294487859855166165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987301529658573236777443 10480952294487859855166165)
              ·
                refine ⟨245647319402059215355457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10480952294487859855166165 245647319402059215355457)
                ·
                  refine ⟨184235489551544411516593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245647319402059215355457 184235489551544411516593)
                  ·
                    rfl

theorem cell20_403647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2].length) (baseStart_403647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403647 prefixEnd_403647 := by exact prefixLift 403647
  have htrace : WordTrace (prefixWord ++ tailWord_403647) baseStart_403647 baseEnd_403647 := by
    simpa [prefixWord, tailWord_403647, baseEnd_403647] using wordTrace_append hprefix tailTrace_403647
  have hstable : (prefixWord ++ tailWord_403647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403647).length < 2 ^ (prefixWord ++ tailWord_403647).sum := by decide
  have hdescent : baseEnd_403647 < baseStart_403647 := by decide
  rcases family_descends (prefixWord ++ tailWord_403647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403685 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_403685 : Nat := 118140960795 + 403685 * 2 ^ 59
def prefixEnd_403685 : Nat := 4983230072969 + 3 ^ 40 * 403685 * 2
def baseEnd_403685 : Nat := 184252833786985168249771

theorem tailTrace_403685 : CollatzResearch.WordTrace tailWord_403685 prefixEnd_403685 184252833786985168249771 := by
  unfold tailWord_403685
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723601542525663754204509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815734361683775836136339 14723601542525663754204509)
  ·
    refine ⟨5521350578447123907826691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14723601542525663754204509 5521350578447123907826691)
    ·
      refine ⟨8282025867670685861740037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521350578447123907826691 8282025867670685861740037)
      ·
        refine ⟨1552879850188253599076257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8282025867670685861740037 1552879850188253599076257)
        ·
          refine ⟨1164659887641190199307193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552879850188253599076257 1164659887641190199307193)
          ·
            refine ⟨873494915730892649480395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164659887641190199307193 873494915730892649480395)
            ·
              refine ⟨1310242373596338974220593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873494915730892649480395 1310242373596338974220593)
              ·
                refine ⟨982681780197254230665445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310242373596338974220593 982681780197254230665445)
                ·
                  refine ⟨184252833786985168249771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982681780197254230665445 184252833786985168249771)
                  ·
                    rfl

theorem cell20_403685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_403685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403685 prefixEnd_403685 := by exact prefixLift 403685
  have htrace : WordTrace (prefixWord ++ tailWord_403685) baseStart_403685 baseEnd_403685 := by
    simpa [prefixWord, tailWord_403685, baseEnd_403685] using wordTrace_append hprefix tailTrace_403685
  have hstable : (prefixWord ++ tailWord_403685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403685).length < 2 ^ (prefixWord ++ tailWord_403685).sum := by decide
  have hdescent : baseEnd_403685 < baseStart_403685 := by decide
  rcases family_descends (prefixWord ++ tailWord_403685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403692 : List Nat := [2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_403692 : Nat := 118140960795 + 403692 * 2 ^ 59
def prefixEnd_403692 : Nat := 4983230072969 + 3 ^ 40 * 403692 * 2
def baseEnd_403692 : Nat := 61418676259241418338803

theorem tailTrace_403692 : CollatzResearch.WordTrace tailWord_403692 prefixEnd_403692 61418676259241418338803 := by
  unfold tailWord_403692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361928426750151974854665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9815904569000202633139553 7361928426750151974854665)
  ·
    refine ⟨5521446320062613981140999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7361928426750151974854665 5521446320062613981140999)
    ·
      refine ⟨8282169480093920971711499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521446320062613981140999 8282169480093920971711499)
      ·
        refine ⟨12423254220140881457567249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8282169480093920971711499 12423254220140881457567249)
        ·
          refine ⟨9317440665105661093175437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12423254220140881457567249 9317440665105661093175437)
          ·
            refine ⟨3494040249414622909940789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317440665105661093175437 3494040249414622909940789)
            ·
              refine ⟨327566273382620897806949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3494040249414622909940789 327566273382620897806949)
              ·
                refine ⟨61418676259241418338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327566273382620897806949 61418676259241418338803)
                ·
                  rfl

theorem cell20_403692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_403692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403692 prefixEnd_403692 := by exact prefixLift 403692
  have htrace : WordTrace (prefixWord ++ tailWord_403692) baseStart_403692 baseEnd_403692 := by
    simpa [prefixWord, tailWord_403692, baseEnd_403692] using wordTrace_append hprefix tailTrace_403692
  have hstable : (prefixWord ++ tailWord_403692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403692).length < 2 ^ (prefixWord ++ tailWord_403692).sum := by decide
  have hdescent : baseEnd_403692 < baseStart_403692 := by decide
  rcases family_descends (prefixWord ++ tailWord_403692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403702 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_403702 : Nat := 118140960795 + 403702 * 2 ^ 59
def prefixEnd_403702 : Nat := 4983230072969 + 3 ^ 40 * 403702 * 2
def baseEnd_403702 : Nat := 184260593050208664683035

theorem tailTrace_403702 : CollatzResearch.WordTrace tailWord_403702 prefixEnd_403702 184260593050208664683035 := by
  unfold tailWord_403702
  simp only [CollatzResearch.WordTrace]
  refine ⟨920263848966504728598335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9816147722309383771715573 920263848966504728598335)
  ·
    refine ⟨1380395773449757092897503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920263848966504728598335 1380395773449757092897503)
    ·
      refine ⟨2070593660174635639346255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380395773449757092897503 2070593660174635639346255)
      ·
        refine ⟨3105890490261953459019383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070593660174635639346255 3105890490261953459019383)
        ·
          refine ⟨4658835735392930188529075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105890490261953459019383 4658835735392930188529075)
          ·
            refine ⟨6988253603089395282793613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658835735392930188529075 6988253603089395282793613)
            ·
              refine ⟨2620595101158523231047605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988253603089395282793613 2620595101158523231047605)
              ·
                refine ⟨245680790733611552910713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2620595101158523231047605 245680790733611552910713)
                ·
                  refine ⟨184260593050208664683035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245680790733611552910713 184260593050208664683035)
                  ·
                    rfl

theorem cell20_403702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_403702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403702 prefixEnd_403702 := by exact prefixLift 403702
  have htrace : WordTrace (prefixWord ++ tailWord_403702) baseStart_403702 baseEnd_403702 := by
    simpa [prefixWord, tailWord_403702, baseEnd_403702] using wordTrace_append hprefix tailTrace_403702
  have hstable : (prefixWord ++ tailWord_403702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403702).length < 2 ^ (prefixWord ++ tailWord_403702).sum := by decide
  have hdescent : baseEnd_403702 < baseStart_403702 := by decide
  rcases family_descends (prefixWord ++ tailWord_403702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403713 : List Nat := [1, 2, 4, 1, 1, 2, 9]
def baseStart_403713 : Nat := 118140960795 + 403713 * 2 ^ 59
def prefixEnd_403713 : Nat := 4983230072969 + 3 ^ 40 * 403713 * 2
def baseEnd_403713 : Nat := 20473957083326835035147

theorem tailTrace_403713 : CollatzResearch.WordTrace tailWord_403713 prefixEnd_403713 20473957083326835035147 := by
  unfold tailWord_403713
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724622786424224536223793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9816415190949483024149195 14724622786424224536223793)
  ·
    refine ⟨11043467089818168402167845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14724622786424224536223793 11043467089818168402167845)
    ·
      refine ⟨2070650079340906575406471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11043467089818168402167845 2070650079340906575406471)
      ·
        refine ⟨3105975119011359863109707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070650079340906575406471 3105975119011359863109707)
        ·
          refine ⟨4658962678517039794664561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105975119011359863109707 4658962678517039794664561)
          ·
            refine ⟨3494222008887779845998421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4658962678517039794664561 3494222008887779845998421)
            ·
              refine ⟨20473957083326835035147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3494222008887779845998421 20473957083326835035147)
              ·
                rfl

theorem cell20_403713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_403713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403713 prefixEnd_403713 := by exact prefixLift 403713
  have htrace : WordTrace (prefixWord ++ tailWord_403713) baseStart_403713 baseEnd_403713 := by
    simpa [prefixWord, tailWord_403713, baseEnd_403713] using wordTrace_append hprefix tailTrace_403713
  have hstable : (prefixWord ++ tailWord_403713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403713).length < 2 ^ (prefixWord ++ tailWord_403713).sum := by decide
  have hdescent : baseEnd_403713 < baseStart_403713 := by decide
  rcases family_descends (prefixWord ++ tailWord_403713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403716 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_403716 : Nat := 118140960795 + 403716 * 2 ^ 59
def prefixEnd_403716 : Nat := 4983230072969 + 3 ^ 40 * 403716 * 2
def baseEnd_403716 : Nat := 184266983031686838216311

theorem tailTrace_403716 : CollatzResearch.WordTrace tailWord_403716 prefixEnd_403716 184266983031686838216311 := by
  unfold tailWord_403716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362366102706678024291501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9816488136942237365722001 7362366102706678024291501)
  ·
    refine ⟨2760887288515004259109313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7362366102706678024291501 2760887288515004259109313)
    ·
      refine ⟨2070665466386253194331985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2760887288515004259109313 2070665466386253194331985)
      ·
        refine ⟨1552999099789689895748989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070665466386253194331985 1552999099789689895748989)
        ·
          refine ⟨582374662421133710905871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552999099789689895748989 582374662421133710905871)
          ·
            refine ⟨873561993631700566358807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582374662421133710905871 873561993631700566358807)
            ·
              refine ⟨1310342990447550849538211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873561993631700566358807 1310342990447550849538211)
              ·
                refine ⟨1965514485671326274307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310342990447550849538211 1965514485671326274307317)
                ·
                  refine ⟨184266983031686838216311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1965514485671326274307317 184266983031686838216311)
                  ·
                    rfl

theorem cell20_403716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_403716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403716 prefixEnd_403716 := by exact prefixLift 403716
  have htrace : WordTrace (prefixWord ++ tailWord_403716) baseStart_403716 baseEnd_403716 := by
    simpa [prefixWord, tailWord_403716, baseEnd_403716] using wordTrace_append hprefix tailTrace_403716
  have hstable : (prefixWord ++ tailWord_403716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403716).length < 2 ^ (prefixWord ++ tailWord_403716).sum := by decide
  have hdescent : baseEnd_403716 < baseStart_403716 := by decide
  rcases family_descends (prefixWord ++ tailWord_403716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403723 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 2]
def baseStart_403723 : Nat := 118140960795 + 403723 * 2 ^ 59
def prefixEnd_403723 : Nat := 4983230072969 + 3 ^ 40 * 403723 * 2
def baseEnd_403723 : Nat := 184270178022425924982949

theorem tailTrace_403723 : CollatzResearch.WordTrace tailWord_403723 prefixEnd_403723 184270178022425924982949 := by
  unfold tailWord_403723
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724987516387996244087823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9816658344258664162725215 14724987516387996244087823)
  ·
    refine ⟨22087481274581994366131735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14724987516387996244087823 22087481274581994366131735)
    ·
      refine ⟨33131221911872991549197603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22087481274581994366131735 33131221911872991549197603)
      ·
        refine ⟨49696832867809487323796405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33131221911872991549197603 49696832867809487323796405)
        ·
          refine ⟨4659078081357139436605913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49696832867809487323796405 4659078081357139436605913)
          ·
            refine ⟨3494308561017854577454435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659078081357139436605913 3494308561017854577454435)
            ·
              refine ⟨5241462841526781866181653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494308561017854577454435 5241462841526781866181653)
              ·
                refine ⟨245693570696567899977265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5241462841526781866181653 245693570696567899977265)
                ·
                  refine ⟨184270178022425924982949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245693570696567899977265 184270178022425924982949)
                  ·
                    rfl

theorem cell20_403723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2].length) (baseStart_403723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403723 prefixEnd_403723 := by exact prefixLift 403723
  have htrace : WordTrace (prefixWord ++ tailWord_403723) baseStart_403723 baseEnd_403723 := by
    simpa [prefixWord, tailWord_403723, baseEnd_403723] using wordTrace_append hprefix tailTrace_403723
  have hstable : (prefixWord ++ tailWord_403723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403723).length < 2 ^ (prefixWord ++ tailWord_403723).sum := by decide
  have hdescent : baseEnd_403723 < baseStart_403723 := by decide
  rcases family_descends (prefixWord ++ tailWord_403723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403775 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_403775 : Nat := 118140960795 + 403775 * 2 ^ 59
def prefixEnd_403775 : Nat := 4983230072969 + 3 ^ 40 * 403775 * 2
def baseEnd_403775 : Nat := 184293912239344855249403

theorem tailTrace_403775 : CollatzResearch.WordTrace tailWord_403775 prefixEnd_403775 184293912239344855249403 := by
  unfold tailWord_403775
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726884112199609124980779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817922741466406083320519 14726884112199609124980779)
  ·
    refine ⟨22090326168299413687471169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14726884112199609124980779 22090326168299413687471169)
    ·
      refine ⟨16567744626224560265603377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22090326168299413687471169 16567744626224560265603377)
      ·
        refine ⟨12425808469668420199202533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16567744626224560265603377 12425808469668420199202533)
        ·
          refine ⟨2329839088062828787350475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12425808469668420199202533 2329839088062828787350475)
          ·
            refine ⟨3494758632094243181025713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329839088062828787350475 3494758632094243181025713)
            ·
              refine ⟨2621068974070682385769285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494758632094243181025713 2621068974070682385769285)
              ·
                refine ⟨491450432638252947331741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2621068974070682385769285 491450432638252947331741)
                ·
                  refine ⟨184293912239344855249403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491450432638252947331741 184293912239344855249403)
                  ·
                    rfl

theorem cell20_403775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_403775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403775 prefixEnd_403775 := by exact prefixLift 403775
  have htrace : WordTrace (prefixWord ++ tailWord_403775) baseStart_403775 baseEnd_403775 := by
    simpa [prefixWord, tailWord_403775, baseEnd_403775] using wordTrace_append hprefix tailTrace_403775
  have hstable : (prefixWord ++ tailWord_403775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403775).length < 2 ^ (prefixWord ++ tailWord_403775).sum := by decide
  have hdescent : baseEnd_403775 < baseStart_403775 := by decide
  rcases family_descends (prefixWord ++ tailWord_403775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403792 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_403792 : Nat := 118140960795 + 403792 * 2 ^ 59
def prefixEnd_403792 : Nat := 4983230072969 + 3 ^ 40 * 403792 * 2
def baseEnd_403792 : Nat := 184301671502568351682667

theorem tailTrace_403792 : CollatzResearch.WordTrace tailWord_403792 prefixEnd_403792 184301671502568351682667 := by
  unfold tailWord_403792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363752076569010514174815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9818336102092014018899753 7363752076569010514174815)
  ·
    refine ⟨11045628114853515771262223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7363752076569010514174815 11045628114853515771262223)
    ·
      refine ⟨16568442172280273656893335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11045628114853515771262223 16568442172280273656893335)
      ·
        refine ⟨24852663258420410485340003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16568442172280273656893335 24852663258420410485340003)
        ·
          refine ⟨37278994887630615728010005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24852663258420410485340003 37278994887630615728010005)
          ·
            refine ⟨1747452885357685112250469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37278994887630615728010005 1747452885357685112250469)
            ·
              refine ⟨327647416004565958546963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1747452885357685112250469 327647416004565958546963)
              ·
                refine ⟨491471124006848937820445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327647416004565958546963 491471124006848937820445)
                ·
                  refine ⟨184301671502568351682667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491471124006848937820445 184301671502568351682667)
                  ·
                    rfl

theorem cell20_403792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_403792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403792 prefixEnd_403792 := by exact prefixLift 403792
  have htrace : WordTrace (prefixWord ++ tailWord_403792) baseStart_403792 baseEnd_403792 := by
    simpa [prefixWord, tailWord_403792, baseEnd_403792] using wordTrace_append hprefix tailTrace_403792
  have hstable : (prefixWord ++ tailWord_403792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403792).length < 2 ^ (prefixWord ++ tailWord_403792).sum := by decide
  have hdescent : baseEnd_403792 < baseStart_403792 := by decide
  rcases family_descends (prefixWord ++ tailWord_403792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403851 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_403851 : Nat := 118140960795 + 403851 * 2 ^ 59
def prefixEnd_403851 : Nat := 4983230072969 + 3 ^ 40 * 403851 * 2
def baseEnd_403851 : Nat := 184328600710226368715759

theorem tailTrace_403851 : CollatzResearch.WordTrace tailWord_403851 prefixEnd_403851 184328600710226368715759 := by
  unfold tailWord_403851
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729656059924274104747407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819770706616182736498271 14729656059924274104747407)
  ·
    refine ⟨22094484089886411157121111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14729656059924274104747407 22094484089886411157121111)
    ·
      refine ⟨33141726134829616735681667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22094484089886411157121111 33141726134829616735681667)
      ·
        refine ⟨49712589202244425103522501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33141726134829616735681667 49712589202244425103522501)
        ·
          refine ⟨9321110475420829706910469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49712589202244425103522501 9321110475420829706910469)
          ·
            refine ⟨1747708214141405570045713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9321110475420829706910469 1747708214141405570045713)
            ·
              refine ⟨1310781160606054177534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747708214141405570045713 1310781160606054177534285)
              ·
                refine ⟨491542935227270316575357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310781160606054177534285 491542935227270316575357)
                ·
                  refine ⟨184328600710226368715759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491542935227270316575357 184328600710226368715759)
                  ·
                    rfl

theorem cell20_403851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_403851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403851 prefixEnd_403851 := by exact prefixLift 403851
  have htrace : WordTrace (prefixWord ++ tailWord_403851) baseStart_403851 baseEnd_403851 := by
    simpa [prefixWord, tailWord_403851, baseEnd_403851] using wordTrace_append hprefix tailTrace_403851
  have hstable : (prefixWord ++ tailWord_403851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403851).length < 2 ^ (prefixWord ++ tailWord_403851).sum := by decide
  have hdescent : baseEnd_403851 < baseStart_403851 := by decide
  rcases family_descends (prefixWord ++ tailWord_403851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403875 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 2]
def baseStart_403875 : Nat := 118140960795 + 403875 * 2 ^ 59
def prefixEnd_403875 : Nat := 4983230072969 + 3 ^ 40 * 403875 * 2
def baseEnd_403875 : Nat := 184339554964188951915661

theorem tailTrace_403875 : CollatzResearch.WordTrace tailWord_403875 prefixEnd_403875 184339554964188951915661 := by
  unfold tailWord_403875
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730531411837326203621079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9820354274558217469080719 14730531411837326203621079)
  ·
    refine ⟨22095797117755989305431619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14730531411837326203621079 22095797117755989305431619)
    ·
      refine ⟨33143695676633983958147429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22095797117755989305431619 33143695676633983958147429)
      ·
        refine ⟨6214442939368871992152643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33143695676633983958147429 6214442939368871992152643)
        ·
          refine ⟨9321664409053307988228965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214442939368871992152643 9321664409053307988228965)
          ·
            refine ⟨1747812076697495247792931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9321664409053307988228965 1747812076697495247792931)
            ·
              refine ⟨2621718115046242871689397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747812076697495247792931 2621718115046242871689397)
              ·
                refine ⟨245786073285585269220881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2621718115046242871689397 245786073285585269220881)
                ·
                  refine ⟨184339554964188951915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245786073285585269220881 184339554964188951915661)
                  ·
                    rfl

theorem cell20_403875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2].length) (baseStart_403875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403875 prefixEnd_403875 := by exact prefixLift 403875
  have htrace : WordTrace (prefixWord ++ tailWord_403875) baseStart_403875 baseEnd_403875 := by
    simpa [prefixWord, tailWord_403875, baseEnd_403875] using wordTrace_append hprefix tailTrace_403875
  have hstable : (prefixWord ++ tailWord_403875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403875).length < 2 ^ (prefixWord ++ tailWord_403875).sum := by decide
  have hdescent : baseEnd_403875 < baseStart_403875 := by decide
  rcases family_descends (prefixWord ++ tailWord_403875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403889 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_403889 : Nat := 118140960795 + 403889 * 2 ^ 59
def prefixEnd_403889 : Nat := 4983230072969 + 3 ^ 40 * 403889 * 2
def baseEnd_403889 : Nat := 184345944945667125448937

theorem tailTrace_403889 : CollatzResearch.WordTrace tailWord_403889 prefixEnd_403889 184345944945667125448937 := by
  unfold tailWord_403889
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731042033786606594630721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9820694689191071063087147 14731042033786606594630721)
  ·
    refine ⟨11048281525339954945973041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14731042033786606594630721 11048281525339954945973041)
    ·
      refine ⟨8286211144004966209479781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11048281525339954945973041 8286211144004966209479781)
      ·
        refine ⟨1553664589500931164277459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8286211144004966209479781 1553664589500931164277459)
        ·
          refine ⟨2330496884251396746416189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553664589500931164277459 2330496884251396746416189)
          ·
            refine ⟨873936331594273779906071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2330496884251396746416189 873936331594273779906071)
            ·
              refine ⟨1310904497391410669859107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873936331594273779906071 1310904497391410669859107)
              ·
                refine ⟨1966356746087116004788661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310904497391410669859107 1966356746087116004788661)
                ·
                  refine ⟨184345944945667125448937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966356746087116004788661 184345944945667125448937)
                  ·
                    rfl

theorem cell20_403889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_403889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403889 prefixEnd_403889 := by exact prefixLift 403889
  have htrace : WordTrace (prefixWord ++ tailWord_403889) baseStart_403889 baseEnd_403889 := by
    simpa [prefixWord, tailWord_403889, baseEnd_403889] using wordTrace_append hprefix tailTrace_403889
  have hstable : (prefixWord ++ tailWord_403889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403889).length < 2 ^ (prefixWord ++ tailWord_403889).sum := by decide
  have hdescent : baseEnd_403889 < baseStart_403889 := by decide
  rcases family_descends (prefixWord ++ tailWord_403889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403916 : List Nat := [2, 2, 1, 4, 4, 1, 2, 4]
def baseStart_403916 : Nat := 118140960795 + 403916 * 2 ^ 59
def prefixEnd_403916 : Nat := 4983230072969 + 3 ^ 40 * 403916 * 2
def baseEnd_403916 : Nat := 61452756160458343849609

theorem tailTrace_403916 : CollatzResearch.WordTrace tailWord_403916 prefixEnd_403916 61452756160458343849609 := by
  unfold tailWord_403916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366013402344395102931801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9821351203125860137242401 7366013402344395102931801)
  ·
    refine ⟨5524510051758296327198851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7366013402344395102931801 5524510051758296327198851)
    ·
      refine ⟨8286765077637444490798277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524510051758296327198851 8286765077637444490798277)
      ·
        refine ⟨1553768452057020842024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8286765077637444490798277 1553768452057020842024677)
        ·
          refine ⟨291331584760691407879627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1553768452057020842024677 291331584760691407879627)
          ·
            refine ⟨436997377141037111819441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291331584760691407879627 436997377141037111819441)
            ·
              refine ⟨327748032855777833864581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436997377141037111819441 327748032855777833864581)
              ·
                refine ⟨61452756160458343849609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327748032855777833864581 61452756160458343849609)
                ·
                  rfl

theorem cell20_403916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_403916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403916 prefixEnd_403916 := by exact prefixLift 403916
  have htrace : WordTrace (prefixWord ++ tailWord_403916) baseStart_403916 baseEnd_403916 := by
    simpa [prefixWord, tailWord_403916, baseEnd_403916] using wordTrace_append hprefix tailTrace_403916
  have hstable : (prefixWord ++ tailWord_403916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403916).length < 2 ^ (prefixWord ++ tailWord_403916).sum := by decide
  have hdescent : baseEnd_403916 < baseStart_403916 := by decide
  rcases family_descends (prefixWord ++ tailWord_403916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403948 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_403948 : Nat := 118140960795 + 403948 * 2 ^ 59
def prefixEnd_403948 : Nat := 4983230072969 + 3 ^ 40 * 403948 * 2
def baseEnd_403948 : Nat := 184372874153325142482029

theorem tailTrace_403948 : CollatzResearch.WordTrace tailWord_403948 prefixEnd_403948 184372874153325142482029 := by
  unfold tailWord_403948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7366596970286429835514249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9822129293715239780685665 7366596970286429835514249)
  ·
    refine ⟨5524947727714822376635687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7366596970286429835514249 5524947727714822376635687)
    ·
      refine ⟨8287421591572233564953531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5524947727714822376635687 8287421591572233564953531)
      ·
        refine ⟨12431132387358350347430297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8287421591572233564953531 12431132387358350347430297)
        ·
          refine ⟨9323349290518762760572723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12431132387358350347430297 9323349290518762760572723)
          ·
            refine ⟨13985023935778144140859085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9323349290518762760572723 13985023935778144140859085)
            ·
              refine ⟨5244383975916804052822157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13985023935778144140859085 5244383975916804052822157)
              ·
                refine ⟨1966643990968801519808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5244383975916804052822157 1966643990968801519808309)
                ·
                  refine ⟨184372874153325142482029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966643990968801519808309 184372874153325142482029)
                  ·
                    rfl

theorem cell20_403948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_403948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403948 prefixEnd_403948 := by exact prefixLift 403948
  have htrace : WordTrace (prefixWord ++ tailWord_403948) baseStart_403948 baseEnd_403948 := by
    simpa [prefixWord, tailWord_403948, baseEnd_403948] using wordTrace_append hprefix tailTrace_403948
  have hstable : (prefixWord ++ tailWord_403948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403948).length < 2 ^ (prefixWord ++ tailWord_403948).sum := by decide
  have hdescent : baseEnd_403948 < baseStart_403948 := by decide
  rcases family_descends (prefixWord ++ tailWord_403948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403957 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 3]
def baseStart_403957 : Nat := 118140960795 + 403957 * 2 ^ 59
def prefixEnd_403957 : Nat := 4983230072969 + 3 ^ 40 * 403957 * 2
def baseEnd_403957 : Nat := 184376981998561111181993

theorem tailTrace_403957 : CollatzResearch.WordTrace tailWord_403957 prefixEnd_403957 184376981998561111181993 := by
  unfold tailWord_403957
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733522197540254208106125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822348131693502805404083 14733522197540254208106125)
  ·
    refine ⟨5525070824077595328039797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14733522197540254208106125 5525070824077595328039797)
    ·
      refine ⟨517975389757274562003731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5525070824077595328039797 517975389757274562003731)
      ·
        refine ⟨776963084635911843005597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517975389757274562003731 776963084635911843005597)
        ·
          refine ⟨291361156738466941127099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776963084635911843005597 291361156738466941127099)
          ·
            refine ⟨437041735107700411690649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291361156738466941127099 437041735107700411690649)
            ·
              refine ⟨327781301330775308767987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437041735107700411690649 327781301330775308767987)
              ·
                refine ⟨491671951996162963151981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327781301330775308767987 491671951996162963151981)
                ·
                  refine ⟨184376981998561111181993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491671951996162963151981 184376981998561111181993)
                  ·
                    rfl

theorem cell20_403957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_403957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403957 prefixEnd_403957 := by exact prefixLift 403957
  have htrace : WordTrace (prefixWord ++ tailWord_403957) baseStart_403957 baseEnd_403957 := by
    simpa [prefixWord, tailWord_403957, baseEnd_403957] using wordTrace_append hprefix tailTrace_403957
  have hstable : (prefixWord ++ tailWord_403957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403957).length < 2 ^ (prefixWord ++ tailWord_403957).sum := by decide
  have hdescent : baseEnd_403957 < baseStart_403957 := by decide
  rcases family_descends (prefixWord ++ tailWord_403957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403958 : List Nat := [5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_403958 : Nat := 118140960795 + 403958 * 2 ^ 59
def prefixEnd_403958 : Nat := 4983230072969 + 3 ^ 40 * 403958 * 2
def baseEnd_403958 : Nat := 61459146141936517382885

theorem tailTrace_403958 : CollatzResearch.WordTrace tailWord_403958 prefixEnd_403958 61459146141936517382885 := by
  unfold tailWord_403958
  simp only [CollatzResearch.WordTrace]
  refine ⟨920847416908539461180783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9822372447024420919261685 920847416908539461180783)
  ·
    refine ⟨1381271125362809191771175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 920847416908539461180783 1381271125362809191771175)
    ·
      refine ⟨2071906688044213787656763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381271125362809191771175 2071906688044213787656763)
      ·
        refine ⟨3107860032066320681485145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2071906688044213787656763 3107860032066320681485145)
        ·
          refine ⟨2330895024049740511113859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107860032066320681485145 2330895024049740511113859)
          ·
            refine ⟨3496342536074610766670789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330895024049740511113859 3496342536074610766670789)
            ·
              refine ⟨655564225513989518750773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3496342536074610766670789 655564225513989518750773)
              ·
                refine ⟨61459146141936517382885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655564225513989518750773 61459146141936517382885)
                ·
                  rfl

theorem cell20_403958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_403958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403958 prefixEnd_403958 := by exact prefixLift 403958
  have htrace : WordTrace (prefixWord ++ tailWord_403958) baseStart_403958 baseEnd_403958 := by
    simpa [prefixWord, tailWord_403958, baseEnd_403958] using wordTrace_append hprefix tailTrace_403958
  have hstable : (prefixWord ++ tailWord_403958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403958).length < 2 ^ (prefixWord ++ tailWord_403958).sum := by decide
  have hdescent : baseEnd_403958 < baseStart_403958 := by decide
  rcases family_descends (prefixWord ++ tailWord_403958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403965 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_403965 : Nat := 118140960795 + 403965 * 2 ^ 59
def prefixEnd_403965 : Nat := 4983230072969 + 3 ^ 40 * 403965 * 2
def baseEnd_403965 : Nat := 184380633416548638915293

theorem tailTrace_403965 : CollatzResearch.WordTrace tailWord_403965 prefixEnd_403965 184380633416548638915293 := by
  unfold tailWord_403965
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733813981511271574397349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822542654340847716264899 14733813981511271574397349)
  ·
    refine ⟨2762590121533363420199503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14733813981511271574397349 2762590121533363420199503)
    ·
      refine ⟨4143885182300045130299255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762590121533363420199503 4143885182300045130299255)
      ·
        refine ⟨6215827773450067695448883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143885182300045130299255 6215827773450067695448883)
        ·
          refine ⟨9323741660175101543173325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215827773450067695448883 9323741660175101543173325)
          ·
            refine ⟨3496403122565663078689997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9323741660175101543173325 3496403122565663078689997)
            ·
              refine ⟨1311151170962123654508749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3496403122565663078689997 1311151170962123654508749)
              ·
                refine ⟨491681689110796370440781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1311151170962123654508749 491681689110796370440781)
                ·
                  refine ⟨184380633416548638915293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491681689110796370440781 184380633416548638915293)
                  ·
                    rfl

theorem cell20_403965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_403965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403965 prefixEnd_403965 := by exact prefixLift 403965
  have htrace : WordTrace (prefixWord ++ tailWord_403965) baseStart_403965 baseEnd_403965 := by
    simpa [prefixWord, tailWord_403965, baseEnd_403965] using wordTrace_append hprefix tailTrace_403965
  have hstable : (prefixWord ++ tailWord_403965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403965).length < 2 ^ (prefixWord ++ tailWord_403965).sum := by decide
  have hdescent : baseEnd_403965 < baseStart_403965 := by decide
  rcases family_descends (prefixWord ++ tailWord_403965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403979 : List Nat := [1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_403979 : Nat := 118140960795 + 403979 * 2 ^ 59
def prefixEnd_403979 : Nat := 4983230072969 + 3 ^ 40 * 403979 * 2
def baseEnd_403979 : Nat := 61462341132675604149523

theorem tailTrace_403979 : CollatzResearch.WordTrace tailWord_403979 prefixEnd_403979 61462341132675604149523 := by
  unfold tailWord_403979
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734324603460551965406991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822883068973701310271327 14734324603460551965406991)
  ·
    refine ⟨22101486905190827948110487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14734324603460551965406991 22101486905190827948110487)
    ·
      refine ⟨33152230357786241922165731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22101486905190827948110487 33152230357786241922165731)
      ·
        refine ⟨49728345536679362883248597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33152230357786241922165731 49728345536679362883248597)
        ·
          refine ⟨1165508098515922567576139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49728345536679362883248597 1165508098515922567576139)
          ·
            refine ⟨1748262147773883851364209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165508098515922567576139 1748262147773883851364209)
            ·
              refine ⟨1311196610830412888523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748262147773883851364209 1311196610830412888523157)
              ·
                refine ⟨61462341132675604149523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1311196610830412888523157 61462341132675604149523)
                ·
                  rfl

theorem cell20_403979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_403979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403979 prefixEnd_403979 := by exact prefixLift 403979
  have htrace : WordTrace (prefixWord ++ tailWord_403979) baseStart_403979 baseEnd_403979 := by
    simpa [prefixWord, tailWord_403979, baseEnd_403979] using wordTrace_append hprefix tailTrace_403979
  have hstable : (prefixWord ++ tailWord_403979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403979).length < 2 ^ (prefixWord ++ tailWord_403979).sum := by decide
  have hdescent : baseEnd_403979 < baseStart_403979 := by decide
  rcases family_descends (prefixWord ++ tailWord_403979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403989 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 2]
def baseStart_403989 : Nat := 118140960795 + 403989 * 2 ^ 59
def prefixEnd_403989 : Nat := 4983230072969 + 3 ^ 40 * 403989 * 2
def baseEnd_403989 : Nat := 184391587670511222115195

theorem tailTrace_403989 : CollatzResearch.WordTrace tailWord_403989 prefixEnd_403989 184391587670511222115195 := by
  unfold tailWord_403989
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734689333424323673271021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823126222282882448847347 14734689333424323673271021)
  ·
    refine ⟨5525508500034121377476633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14734689333424323673271021 5525508500034121377476633)
    ·
      refine ⟨4144131375025591033107475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5525508500034121377476633 4144131375025591033107475)
      ·
        refine ⟨6216197062538386549661213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144131375025591033107475 6216197062538386549661213)
        ·
          refine ⟨2331073898451894956122955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6216197062538386549661213 2331073898451894956122955)
          ·
            refine ⟨3496610847677842434184433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331073898451894956122955 3496610847677842434184433)
            ·
              refine ⟨2622458135758381825638325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496610847677842434184433 2622458135758381825638325)
              ·
                refine ⟨245855450227348296153593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2622458135758381825638325 245855450227348296153593)
                ·
                  refine ⟨184391587670511222115195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245855450227348296153593 184391587670511222115195)
                  ·
                    rfl

theorem cell20_403989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_403989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403989 prefixEnd_403989 := by exact prefixLift 403989
  have htrace : WordTrace (prefixWord ++ tailWord_403989) baseStart_403989 baseEnd_403989 := by
    simpa [prefixWord, tailWord_403989, baseEnd_403989] using wordTrace_append hprefix tailTrace_403989
  have hstable : (prefixWord ++ tailWord_403989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403989).length < 2 ^ (prefixWord ++ tailWord_403989).sum := by decide
  have hdescent : baseEnd_403989 < baseStart_403989 := by decide
  rcases family_descends (prefixWord ++ tailWord_403989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403993 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_403993 : Nat := 118140960795 + 403993 * 2 ^ 59
def prefixEnd_403993 : Nat := 4983230072969 + 3 ^ 40 * 403993 * 2
def baseEnd_403993 : Nat := 184393413379504985981845

theorem tailTrace_403993 : CollatzResearch.WordTrace tailWord_403993 prefixEnd_403993 184393413379504985981845 := by
  unfold tailWord_403993
  simp only [CollatzResearch.WordTrace]
  refine ⟨14734835225409832356416633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823223483606554904277755 14734835225409832356416633)
  ·
    refine ⟨11051126419057374267312475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14734835225409832356416633 11051126419057374267312475)
    ·
      refine ⟨16576689628586061400968713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11051126419057374267312475 16576689628586061400968713)
      ·
        refine ⟨12432517221439546050726535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16576689628586061400968713 12432517221439546050726535)
        ·
          refine ⟨18648775832159319076089803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432517221439546050726535 18648775832159319076089803)
          ·
            refine ⟨27973163748238978614134705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18648775832159319076089803 27973163748238978614134705)
            ·
              refine ⟨20979872811179233960601029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27973163748238978614134705 20979872811179233960601029)
              ·
                refine ⟨3933726152096106367612693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20979872811179233960601029 3933726152096106367612693)
                ·
                  refine ⟨184393413379504985981845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3933726152096106367612693 184393413379504985981845)
                  ·
                    rfl

theorem cell20_403993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_403993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_403993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_403993 prefixEnd_403993 := by exact prefixLift 403993
  have htrace : WordTrace (prefixWord ++ tailWord_403993) baseStart_403993 baseEnd_403993 := by
    simpa [prefixWord, tailWord_403993, baseEnd_403993] using wordTrace_append hprefix tailTrace_403993
  have hstable : (prefixWord ++ tailWord_403993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403993).length < 2 ^ (prefixWord ++ tailWord_403993).sum := by decide
  have hdescent : baseEnd_403993 < baseStart_403993 := by decide
  rcases family_descends (prefixWord ++ tailWord_403993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404003 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_404003 : Nat := 118140960795 + 404003 * 2 ^ 59
def prefixEnd_404003 : Nat := 4983230072969 + 3 ^ 40 * 404003 * 2
def baseEnd_404003 : Nat := 184397977651989395648471

theorem tailTrace_404003 : CollatzResearch.WordTrace tailWord_404003 prefixEnd_404003 184397977651989395648471 := by
  unfold tailWord_404003
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735199955373604064280663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823466636915736042853775 14735199955373604064280663)
  ·
    refine ⟨22102799933060406096420995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14735199955373604064280663 22102799933060406096420995)
    ·
      refine ⟨33154199899590609144631493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22102799933060406096420995 33154199899590609144631493)
      ·
        refine ⟨6216412481173239214618405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33154199899590609144631493 6216412481173239214618405)
        ·
          refine ⟨1165577340219982352740951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6216412481173239214618405 1165577340219982352740951)
          ·
            refine ⟨1748366010329973529111427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165577340219982352740951 1748366010329973529111427)
            ·
              refine ⟨2622549015494960293667141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748366010329973529111427 2622549015494960293667141)
              ·
                refine ⟨491727940405305055062589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2622549015494960293667141 491727940405305055062589)
                ·
                  refine ⟨184397977651989395648471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491727940405305055062589 184397977651989395648471)
                  ·
                    rfl

theorem cell20_404003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_404003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404003 prefixEnd_404003 := by exact prefixLift 404003
  have htrace : WordTrace (prefixWord ++ tailWord_404003) baseStart_404003 baseEnd_404003 := by
    simpa [prefixWord, tailWord_404003, baseEnd_404003] using wordTrace_append hprefix tailTrace_404003
  have hstable : (prefixWord ++ tailWord_404003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404003).length < 2 ^ (prefixWord ++ tailWord_404003).sum := by decide
  have hdescent : baseEnd_404003 < baseStart_404003 := by decide
  rcases family_descends (prefixWord ++ tailWord_404003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404017 : List Nat := [1, 2, 2, 3, 1, 1, 5, 5]
def baseStart_404017 : Nat := 118140960795 + 404017 * 2 ^ 59
def prefixEnd_404017 : Nat := 4983230072969 + 3 ^ 40 * 404017 * 2
def baseEnd_404017 : Nat := 61468122544489189727249

theorem tailTrace_404017 : CollatzResearch.WordTrace tailWord_404017 prefixEnd_404017 61468122544489189727249 := by
  unfold tailWord_404017
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735710577322884455290305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823807051548589636860203 14735710577322884455290305)
  ·
    refine ⟨11051782932992163341467729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14735710577322884455290305 11051782932992163341467729)
    ·
      refine ⟨8288837199744122506100797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11051782932992163341467729 8288837199744122506100797)
      ·
        refine ⟨3108313949904045939787799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8288837199744122506100797 3108313949904045939787799)
        ·
          refine ⟨4662470924856068909681699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108313949904045939787799 4662470924856068909681699)
          ·
            refine ⟨6993706387284103364522549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4662470924856068909681699 6993706387284103364522549)
            ·
              refine ⟨655659973807884690423989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6993706387284103364522549 655659973807884690423989)
              ·
                refine ⟨61468122544489189727249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 655659973807884690423989 61468122544489189727249)
                ·
                  rfl

theorem cell20_404017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_404017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404017 prefixEnd_404017 := by exact prefixLift 404017
  have htrace : WordTrace (prefixWord ++ tailWord_404017) baseStart_404017 baseEnd_404017 := by
    simpa [prefixWord, tailWord_404017, baseEnd_404017] using wordTrace_append hprefix tailTrace_404017
  have hstable : (prefixWord ++ tailWord_404017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404017).length < 2 ^ (prefixWord ++ tailWord_404017).sum := by decide
  have hdescent : baseEnd_404017 < baseStart_404017 := by decide
  rcases family_descends (prefixWord ++ tailWord_404017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404030 : List Nat := [4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_404030 : Nat := 118140960795 + 404030 * 2 ^ 59
def prefixEnd_404030 : Nat := 4983230072969 + 3 ^ 40 * 404030 * 2
def baseEnd_404030 : Nat := 61470100395899100582787

theorem tailTrace_404030 : CollatzResearch.WordTrace tailWord_404030 prefixEnd_404030 61470100395899100582787 := by
  unfold tailWord_404030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842023090784473459439193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9824123150850525117009029 1842023090784473459439193)
  ·
    refine ⟨1381517318088355094579395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1842023090784473459439193 1381517318088355094579395)
    ·
      refine ⟨2072275977132532641869093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381517318088355094579395 2072275977132532641869093)
      ·
        refine ⟨388551745712349870350455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2072275977132532641869093 388551745712349870350455)
        ·
          refine ⟨582827618568524805525683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388551745712349870350455 582827618568524805525683)
          ·
            refine ⟨874241427852787208288525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582827618568524805525683 874241427852787208288525)
            ·
              refine ⟨327840535444795203108197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874241427852787208288525 327840535444795203108197)
              ·
                refine ⟨61470100395899100582787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327840535444795203108197 61470100395899100582787)
                ·
                  rfl

theorem cell20_404030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_404030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404030 prefixEnd_404030 := by exact prefixLift 404030
  have htrace : WordTrace (prefixWord ++ tailWord_404030) baseStart_404030 baseEnd_404030 := by
    simpa [prefixWord, tailWord_404030, baseEnd_404030] using wordTrace_append hprefix tailTrace_404030
  have hstable : (prefixWord ++ tailWord_404030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404030).length < 2 ^ (prefixWord ++ tailWord_404030).sum := by decide
  have hdescent : baseEnd_404030 < baseStart_404030 := by decide
  rcases family_descends (prefixWord ++ tailWord_404030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404065 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 2]
def baseStart_404065 : Nat := 118140960795 + 404065 * 2 ^ 59
def prefixEnd_404065 : Nat := 4983230072969 + 3 ^ 40 * 404065 * 2
def baseEnd_404065 : Nat := 184426276141392735581551

theorem tailTrace_404065 : CollatzResearch.WordTrace tailWord_404065 prefixEnd_404065 184426276141392735581551 := by
  unfold tailWord_404065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737461281148988653037649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9824974187432659102025099 14737461281148988653037649)
  ·
    refine ⟨11053095960861741489778237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14737461281148988653037649 11053095960861741489778237)
    ·
      refine ⟨4144910985323153058666839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11053095960861741489778237 4144910985323153058666839)
      ·
        refine ⟨6217366477984729588000259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144910985323153058666839 6217366477984729588000259)
        ·
          refine ⟨9326049716977094382000389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217366477984729588000259 9326049716977094382000389)
          ·
            refine ⟨1748634321933205196625073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9326049716977094382000389 1748634321933205196625073)
            ·
              refine ⟨1311475741449903897468805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748634321933205196625073 1311475741449903897468805)
              ·
                refine ⟨245901701521856980775401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1311475741449903897468805 245901701521856980775401)
                ·
                  refine ⟨184426276141392735581551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245901701521856980775401 184426276141392735581551)
                  ·
                    rfl

theorem cell20_404065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_404065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404065 prefixEnd_404065 := by exact prefixLift 404065
  have htrace : WordTrace (prefixWord ++ tailWord_404065) baseStart_404065 baseEnd_404065 := by
    simpa [prefixWord, tailWord_404065, baseEnd_404065] using wordTrace_append hprefix tailTrace_404065
  have hstable : (prefixWord ++ tailWord_404065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404065).length < 2 ^ (prefixWord ++ tailWord_404065).sum := by decide
  have hdescent : baseEnd_404065 < baseStart_404065 := by decide
  rcases family_descends (prefixWord ++ tailWord_404065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404120 : List Nat := [2, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_404120 : Nat := 118140960795 + 404120 * 2 ^ 59
def prefixEnd_404120 : Nat := 4983230072969 + 3 ^ 40 * 404120 * 2
def baseEnd_404120 : Nat := 184451379640056988747993

theorem tailTrace_404120 : CollatzResearch.WordTrace tailWord_404120 prefixEnd_404120 184451379640056988747993 := by
  unfold tailWord_404120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369733647974866523144907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9826311530633155364193209 7369733647974866523144907)
  ·
    refine ⟨11054600471962299784717361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7369733647974866523144907 11054600471962299784717361)
    ·
      refine ⟨8290950353971724838538021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11054600471962299784717361 8290950353971724838538021)
      ·
        refine ⟨1554553191369698407225879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8290950353971724838538021 1554553191369698407225879)
        ·
          refine ⟨2331829787054547610838819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554553191369698407225879 2331829787054547610838819)
          ·
            refine ⟨3497744680581821416258229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331829787054547610838819 3497744680581821416258229)
            ·
              refine ⟨327913563804545757774209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3497744680581821416258229 327913563804545757774209)
              ·
                refine ⟨245935172853409318330657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327913563804545757774209 245935172853409318330657)
                ·
                  refine ⟨184451379640056988747993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245935172853409318330657 184451379640056988747993)
                  ·
                    rfl

theorem cell20_404120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_404120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404120 prefixEnd_404120 := by exact prefixLift 404120
  have htrace : WordTrace (prefixWord ++ tailWord_404120) baseStart_404120 baseEnd_404120 := by
    simpa [prefixWord, tailWord_404120, baseEnd_404120] using wordTrace_append hprefix tailTrace_404120
  have hstable : (prefixWord ++ tailWord_404120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404120).length < 2 ^ (prefixWord ++ tailWord_404120).sum := by decide
  have hdescent : baseEnd_404120 < baseStart_404120 := by decide
  rcases family_descends (prefixWord ++ tailWord_404120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404172 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_404172 : Nat := 118140960795 + 404172 * 2 ^ 59
def prefixEnd_404172 : Nat := 4983230072969 + 3 ^ 40 * 404172 * 2
def baseEnd_404172 : Nat := 184475113856975919014447

theorem tailTrace_404172 : CollatzResearch.WordTrace tailWord_404172 prefixEnd_404172 184475113856975919014447 := by
  unfold tailWord_404172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7370681945880672963591385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9827575927840897284788513 7370681945880672963591385)
  ·
    refine ⟨5528011459410504722693539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7370681945880672963591385 5528011459410504722693539)
    ·
      refine ⟨8292017189115757084040309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5528011459410504722693539 8292017189115757084040309)
      ·
        refine ⟨777376611479602226628779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8292017189115757084040309 777376611479602226628779)
        ·
          refine ⟨1166064917219403339943169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777376611479602226628779 1166064917219403339943169)
          ·
            refine ⟨874548687914552504957377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166064917219403339943169 874548687914552504957377)
            ·
              refine ⟨655911515935914378718033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874548687914552504957377 655911515935914378718033)
              ·
                refine ⟨491933636951935784038525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655911515935914378718033 491933636951935784038525)
                ·
                  refine ⟨184475113856975919014447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491933636951935784038525 184475113856975919014447)
                  ·
                    rfl

theorem cell20_404172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_404172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404172 prefixEnd_404172 := by exact prefixLift 404172
  have htrace : WordTrace (prefixWord ++ tailWord_404172) baseStart_404172 baseEnd_404172 := by
    simpa [prefixWord, tailWord_404172, baseEnd_404172] using wordTrace_append hprefix tailTrace_404172
  have hstable : (prefixWord ++ tailWord_404172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404172).length < 2 ^ (prefixWord ++ tailWord_404172).sum := by decide
  have hdescent : baseEnd_404172 < baseStart_404172 := by decide
  rcases family_descends (prefixWord ++ tailWord_404172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404193 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_404193 : Nat := 118140960795 + 404193 * 2 ^ 59
def prefixEnd_404193 : Nat := 4983230072969 + 3 ^ 40 * 404193 * 2
def baseEnd_404193 : Nat := 184484698829193179314361

theorem tailTrace_404193 : CollatzResearch.WordTrace tailWord_404193 prefixEnd_404193 184484698829193179314361 := by
  unfold tailWord_404193
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742129824685266513697233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828086549790177675798155 14742129824685266513697233)
  ·
    refine ⟨11056597368513949885272925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14742129824685266513697233 11056597368513949885272925)
    ·
      refine ⟨4146224013192731206977347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11056597368513949885272925 4146224013192731206977347)
      ·
        refine ⟨6219336019789096810466021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146224013192731206977347 6219336019789096810466021)
        ·
          refine ⟨1166125503710455651962379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6219336019789096810466021 1166125503710455651962379)
          ·
            refine ⟨1749188255565683477943569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166125503710455651962379 1749188255565683477943569)
            ·
              refine ⟨1311891191674262608457677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749188255565683477943569 1311891191674262608457677)
              ·
                refine ⟨491959196877848478171629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1311891191674262608457677 491959196877848478171629)
                ·
                  refine ⟨184484698829193179314361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491959196877848478171629 184484698829193179314361)
                  ·
                    rfl

theorem cell20_404193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_404193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404193 prefixEnd_404193 := by exact prefixLift 404193
  have htrace : WordTrace (prefixWord ++ tailWord_404193) baseStart_404193 baseEnd_404193 := by
    simpa [prefixWord, tailWord_404193, baseEnd_404193] using wordTrace_append hprefix tailTrace_404193
  have hstable : (prefixWord ++ tailWord_404193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404193).length < 2 ^ (prefixWord ++ tailWord_404193).sum := by decide
  have hdescent : baseEnd_404193 < baseStart_404193 := by decide
  rcases family_descends (prefixWord ++ tailWord_404193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404221 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_404221 : Nat := 118140960795 + 404221 * 2 ^ 59
def prefixEnd_404221 : Nat := 4983230072969 + 3 ^ 40 * 404221 * 2
def baseEnd_404221 : Nat := 184497478792149526380913

theorem tailTrace_404221 : CollatzResearch.WordTrace tailWord_404221 prefixEnd_404221 184497478792149526380913 := by
  unfold tailWord_404221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14743151068583827295716517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828767379055884863811011 14743151068583827295716517)
  ·
    refine ⟨2764340825359467617946847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14743151068583827295716517 2764340825359467617946847)
    ·
      refine ⟨4146511238039201426920271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764340825359467617946847 4146511238039201426920271)
      ·
        refine ⟨6219766857058802140380407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146511238039201426920271 6219766857058802140380407)
        ·
          refine ⟨9329650285588203210570611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219766857058802140380407 9329650285588203210570611)
          ·
            refine ⟨13994475428382304815855917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329650285588203210570611 13994475428382304815855917)
            ·
              refine ⟨5247928285643364305945969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13994475428382304815855917 5247928285643364305945969)
              ·
                refine ⟨3935946214232523229459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247928285643364305945969 3935946214232523229459477)
                ·
                  refine ⟨184497478792149526380913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3935946214232523229459477 184497478792149526380913)
                  ·
                    rfl

theorem cell20_404221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_404221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404221 prefixEnd_404221 := by exact prefixLift 404221
  have htrace : WordTrace (prefixWord ++ tailWord_404221) baseStart_404221 baseEnd_404221 := by
    simpa [prefixWord, tailWord_404221, baseEnd_404221] using wordTrace_append hprefix tailTrace_404221
  have hstable : (prefixWord ++ tailWord_404221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404221).length < 2 ^ (prefixWord ++ tailWord_404221).sum := by decide
  have hdescent : baseEnd_404221 < baseStart_404221 := by decide
  rcases family_descends (prefixWord ++ tailWord_404221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404231 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_404231 : Nat := 118140960795 + 404231 * 2 ^ 59
def prefixEnd_404231 : Nat := 4983230072969 + 3 ^ 40 * 404231 * 2
def baseEnd_404231 : Nat := 184502043064633936047539

theorem tailTrace_404231 : CollatzResearch.WordTrace tailWord_404231 prefixEnd_404231 184502043064633936047539 := by
  unfold tailWord_404231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14743515798547599003580547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9829010532365066002387031 14743515798547599003580547)
  ·
    refine ⟨22115273697821398505370821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14743515798547599003580547 22115273697821398505370821)
    ·
      refine ⟨4146613818341512219757029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22115273697821398505370821 4146613818341512219757029)
      ·
        refine ⟨777490090939033541204443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4146613818341512219757029 777490090939033541204443)
        ·
          refine ⟨1166235136408550311806665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777490090939033541204443 1166235136408550311806665)
          ·
            refine ⟨874676352306412733854999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166235136408550311806665 874676352306412733854999)
            ·
              refine ⟨1312014528459619100782499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874676352306412733854999 1312014528459619100782499)
              ·
                refine ⟨1968021792689428651173749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312014528459619100782499 1968021792689428651173749)
                ·
                  refine ⟨184502043064633936047539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1968021792689428651173749 184502043064633936047539)
                  ·
                    rfl

theorem cell20_404231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_404231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404231 prefixEnd_404231 := by exact prefixLift 404231
  have htrace : WordTrace (prefixWord ++ tailWord_404231) baseStart_404231 baseEnd_404231 := by
    simpa [prefixWord, tailWord_404231, baseEnd_404231] using wordTrace_append hprefix tailTrace_404231
  have hstable : (prefixWord ++ tailWord_404231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404231).length < 2 ^ (prefixWord ++ tailWord_404231).sum := by decide
  have hdescent : baseEnd_404231 < baseStart_404231 := by decide
  rcases family_descends (prefixWord ++ tailWord_404231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404289 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 4]
def baseStart_404289 : Nat := 118140960795 + 404289 * 2 ^ 59
def prefixEnd_404289 : Nat := 4983230072969 + 3 ^ 40 * 404289 * 2
def baseEnd_404289 : Nat := 184528515845043512113969

theorem tailTrace_404289 : CollatzResearch.WordTrace tailWord_404289 prefixEnd_404289 184528515845043512113969 := by
  unfold tailWord_404289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745631232337474909191921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9830420821558316606127947 14745631232337474909191921)
  ·
    refine ⟨11059223424253106181893941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14745631232337474909191921 11059223424253106181893941)
    ·
      refine ⟨1036802196023728704552557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11059223424253106181893941 1036802196023728704552557)
      ·
        refine ⟨388800823508898264207209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1036802196023728704552557 388800823508898264207209)
        ·
          refine ⟨291600617631673698155407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388800823508898264207209 291600617631673698155407)
          ·
            refine ⟨437400926447510547233111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291600617631673698155407 437400926447510547233111)
            ·
              refine ⟨656101389671265820849667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437400926447510547233111 656101389671265820849667)
              ·
                refine ⟨984152084506898731274501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656101389671265820849667 984152084506898731274501)
                ·
                  refine ⟨184528515845043512113969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 984152084506898731274501 184528515845043512113969)
                  ·
                    rfl

theorem cell20_404289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_404289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404289 prefixEnd_404289 := by exact prefixLift 404289
  have htrace : WordTrace (prefixWord ++ tailWord_404289) baseStart_404289 baseEnd_404289 := by
    simpa [prefixWord, tailWord_404289, baseEnd_404289] using wordTrace_append hprefix tailTrace_404289
  have hstable : (prefixWord ++ tailWord_404289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404289).length < 2 ^ (prefixWord ++ tailWord_404289).sum := by decide
  have hdescent : baseEnd_404289 < baseStart_404289 := by decide
  rcases family_descends (prefixWord ++ tailWord_404289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404304 : List Nat := [2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_404304 : Nat := 118140960795 + 404304 * 2 ^ 59
def prefixEnd_404304 : Nat := 4983230072969 + 3 ^ 40 * 404304 * 2
def baseEnd_404304 : Nat := 61511787417923375537969

theorem tailTrace_404304 : CollatzResearch.WordTrace tailWord_404304 prefixEnd_404304 61511787417923375537969 := by
  unfold tailWord_404304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373089163641566235493983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9830785551522088313991977 7373089163641566235493983)
  ·
    refine ⟨11059633745462349353240975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7373089163641566235493983 11059633745462349353240975)
    ·
      refine ⟨16589450618193524029861463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11059633745462349353240975 16589450618193524029861463)
      ·
        refine ⟨24884175927290286044792195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16589450618193524029861463 24884175927290286044792195)
        ·
          refine ⟨37326263890935429067188293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24884175927290286044792195 37326263890935429067188293)
          ·
            refine ⟨6998674479550392950097805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37326263890935429067188293 6998674479550392950097805)
            ·
              refine ⟨2624502929831397356286677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6998674479550392950097805 2624502929831397356286677)
              ·
                refine ⟨61511787417923375537969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2624502929831397356286677 61511787417923375537969)
                ·
                  rfl

theorem cell20_404304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_404304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404304 prefixEnd_404304 := by exact prefixLift 404304
  have htrace : WordTrace (prefixWord ++ tailWord_404304) baseStart_404304 baseEnd_404304 := by
    simpa [prefixWord, tailWord_404304, baseEnd_404304] using wordTrace_append hprefix tailTrace_404304
  have hstable : (prefixWord ++ tailWord_404304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404304).length < 2 ^ (prefixWord ++ tailWord_404304).sum := by decide
  have hdescent : baseEnd_404304 < baseStart_404304 := by decide
  rcases family_descends (prefixWord ++ tailWord_404304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404345 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_404345 : Nat := 118140960795 + 404345 * 2 ^ 59
def prefixEnd_404345 : Nat := 4983230072969 + 3 ^ 40 * 404345 * 2
def baseEnd_404345 : Nat := 184554075770956206247073

theorem tailTrace_404345 : CollatzResearch.WordTrace tailWord_404345 prefixEnd_404345 184554075770956206247073 := by
  unfold tailWord_404345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747673720134596473230489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9831782480089730982153659 14747673720134596473230489)
  ·
    refine ⟨11060755290100947354922867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14747673720134596473230489 11060755290100947354922867)
    ·
      refine ⟨16591132935151421032384301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060755290100947354922867 16591132935151421032384301)
      ·
        refine ⟨6221674850681782887144113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16591132935151421032384301 6221674850681782887144113)
        ·
          refine ⟨4666256138011337165358085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221674850681782887144113 4666256138011337165358085)
          ·
            refine ⟨874923025877125718504641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4666256138011337165358085 874923025877125718504641)
            ·
              refine ⟨656192269407844288878481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 874923025877125718504641 656192269407844288878481)
              ·
                refine ⟨492144202055883216658861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656192269407844288878481 492144202055883216658861)
                ·
                  refine ⟨184554075770956206247073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492144202055883216658861 184554075770956206247073)
                  ·
                    rfl

theorem cell20_404345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_404345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404345 prefixEnd_404345 := by exact prefixLift 404345
  have htrace : WordTrace (prefixWord ++ tailWord_404345) baseStart_404345 baseEnd_404345 := by
    simpa [prefixWord, tailWord_404345, baseEnd_404345] using wordTrace_append hprefix tailTrace_404345
  have hstable : (prefixWord ++ tailWord_404345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404345).length < 2 ^ (prefixWord ++ tailWord_404345).sum := by decide
  have hdescent : baseEnd_404345 < baseStart_404345 := by decide
  rcases family_descends (prefixWord ++ tailWord_404345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404359 : List Nat := [1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_404359 : Nat := 118140960795 + 404359 * 2 ^ 59
def prefixEnd_404359 : Nat := 4983230072969 + 3 ^ 40 * 404359 * 2
def baseEnd_404359 : Nat := 61520155250811459926783

theorem tailTrace_404359 : CollatzResearch.WordTrace tailWord_404359 prefixEnd_404359 61520155250811459926783 := by
  unfold tailWord_404359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748184342083876864240131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9832122894722584576160087 14748184342083876864240131)
  ·
    refine ⟨22122276513125815296360197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14748184342083876864240131 22122276513125815296360197)
    ·
      refine ⟨4147926846211090368067537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22122276513125815296360197 4147926846211090368067537)
      ·
        refine ⟨3110945134658317776050653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4147926846211090368067537 3110945134658317776050653)
        ·
          refine ⟨1166604425496869166018995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3110945134658317776050653 1166604425496869166018995)
          ·
            refine ⟨1749906638245303749028493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166604425496869166018995 1749906638245303749028493)
            ·
              refine ⟨656214989341988905885685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1749906638245303749028493 656214989341988905885685)
              ·
                refine ⟨61520155250811459926783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 656214989341988905885685 61520155250811459926783)
                ·
                  rfl

theorem cell20_404359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_404359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404359 prefixEnd_404359 := by exact prefixLift 404359
  have htrace : WordTrace (prefixWord ++ tailWord_404359) baseStart_404359 baseEnd_404359 := by
    simpa [prefixWord, tailWord_404359, baseEnd_404359] using wordTrace_append hprefix tailTrace_404359
  have hstable : (prefixWord ++ tailWord_404359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404359).length < 2 ^ (prefixWord ++ tailWord_404359).sum := by decide
  have hdescent : baseEnd_404359 < baseStart_404359 := by decide
  rcases family_descends (prefixWord ++ tailWord_404359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404373 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_404373 : Nat := 118140960795 + 404373 * 2 ^ 59
def prefixEnd_404373 : Nat := 4983230072969 + 3 ^ 40 * 404373 * 2
def baseEnd_404373 : Nat := 184566855733912553313625

theorem tailTrace_404373 : CollatzResearch.WordTrace tailWord_404373 prefixEnd_404373 184566855733912553313625 := by
  unfold tailWord_404373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748694964033157255249773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9832463309355438170166515 14748694964033157255249773)
  ·
    refine ⟨5530760611512433970718665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14748694964033157255249773 5530760611512433970718665)
    ·
      refine ⟨4148070458634325478038999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5530760611512433970718665 4148070458634325478038999)
      ·
        refine ⟨6222105687951488217058499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148070458634325478038999 6222105687951488217058499)
        ·
          refine ⟨9333158531927232325587749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222105687951488217058499 9333158531927232325587749)
          ·
            refine ⟨1749967224736356061047703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9333158531927232325587749 1749967224736356061047703)
            ·
              refine ⟨2624950837104534091571555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749967224736356061047703 2624950837104534091571555)
              ·
                refine ⟨3937426255656801137357333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624950837104534091571555 3937426255656801137357333)
                ·
                  refine ⟨184566855733912553313625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3937426255656801137357333 184566855733912553313625)
                  ·
                    rfl

theorem cell20_404373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_404373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404373 prefixEnd_404373 := by exact prefixLift 404373
  have htrace : WordTrace (prefixWord ++ tailWord_404373) baseStart_404373 baseEnd_404373 := by
    simpa [prefixWord, tailWord_404373, baseEnd_404373] using wordTrace_append hprefix tailTrace_404373
  have hstable : (prefixWord ++ tailWord_404373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404373).length < 2 ^ (prefixWord ++ tailWord_404373).sum := by decide
  have hdescent : baseEnd_404373 < baseStart_404373 := by decide
  rcases family_descends (prefixWord ++ tailWord_404373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404386 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_404386 : Nat := 118140960795 + 404386 * 2 ^ 59
def prefixEnd_404386 : Nat := 4983230072969 + 3 ^ 40 * 404386 * 2
def baseEnd_404386 : Nat := 184572789288142285880239

theorem tailTrace_404386 : CollatzResearch.WordTrace tailWord_404386 prefixEnd_404386 184572789288142285880239 := by
  unfold tailWord_404386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687292278246515118868253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9832779408657373650315341 3687292278246515118868253)
  ·
    refine ⟨1382734604342443169575595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3687292278246515118868253 1382734604342443169575595)
    ·
      refine ⟨2074101906513664754363393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382734604342443169575595 2074101906513664754363393)
      ·
        refine ⟨1555576429885248565772545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074101906513664754363393 1555576429885248565772545)
        ·
          refine ⟨1166682322413936424329409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555576429885248565772545 1166682322413936424329409)
          ·
            refine ⟨875011741810452318247057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166682322413936424329409 875011741810452318247057)
            ·
              refine ⟨656258806357839238685293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875011741810452318247057 656258806357839238685293)
              ·
                refine ⟨246097052384189714506985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656258806357839238685293 246097052384189714506985)
                ·
                  refine ⟨184572789288142285880239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246097052384189714506985 184572789288142285880239)
                  ·
                    rfl

theorem cell20_404386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_404386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404386 prefixEnd_404386 := by exact prefixLift 404386
  have htrace : WordTrace (prefixWord ++ tailWord_404386) baseStart_404386 baseEnd_404386 := by
    simpa [prefixWord, tailWord_404386, baseEnd_404386] using wordTrace_append hprefix tailTrace_404386
  have hstable : (prefixWord ++ tailWord_404386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404386).length < 2 ^ (prefixWord ++ tailWord_404386).sum := by decide
  have hdescent : baseEnd_404386 < baseStart_404386 := by decide
  rcases family_descends (prefixWord ++ tailWord_404386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404425 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_404425 : Nat := 118140960795 + 404425 * 2 ^ 59
def prefixEnd_404425 : Nat := 4983230072969 + 3 ^ 40 * 404425 * 2
def baseEnd_404425 : Nat := 184590589950831483580079

theorem tailTrace_404425 : CollatzResearch.WordTrace tailWord_404425 prefixEnd_404425 184590589950831483580079 := by
  unfold tailWord_404425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750591559844770136142729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833727706563180090761819 14750591559844770136142729)
  ·
    refine ⟨11062943669883577602107047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14750591559844770136142729 11062943669883577602107047)
    ·
      refine ⟨16594415504825366403160571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11062943669883577602107047 16594415504825366403160571)
      ·
        refine ⟨24891623257238049604740857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594415504825366403160571 24891623257238049604740857)
        ·
          refine ⟨18668717442928537203555643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24891623257238049604740857 18668717442928537203555643)
          ·
            refine ⟨28003076164392805805333465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18668717442928537203555643 28003076164392805805333465)
            ·
              refine ⟨21002307123294604354000099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28003076164392805805333465 21002307123294604354000099)
              ·
                refine ⟨31503460684941906531000149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21002307123294604354000099 31503460684941906531000149)
                ·
                  refine ⟨184590589950831483580079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31503460684941906531000149 184590589950831483580079)
                  ·
                    rfl

theorem cell20_404425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_404425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404425 prefixEnd_404425 := by exact prefixLift 404425
  have htrace : WordTrace (prefixWord ++ tailWord_404425) baseStart_404425 baseEnd_404425 := by
    simpa [prefixWord, tailWord_404425, baseEnd_404425] using wordTrace_append hprefix tailTrace_404425
  have hstable : (prefixWord ++ tailWord_404425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404425).length < 2 ^ (prefixWord ++ tailWord_404425).sum := by decide
  have hdescent : baseEnd_404425 < baseStart_404425 := by decide
  rcases family_descends (prefixWord ++ tailWord_404425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404442 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_404442 : Nat := 118140960795 + 404442 * 2 ^ 59
def prefixEnd_404442 : Nat := 4983230072969 + 3 ^ 40 * 404442 * 2
def baseEnd_404442 : Nat := 184598349214054980013343

theorem tailTrace_404442 : CollatzResearch.WordTrace tailWord_404442 prefixEnd_404442 184598349214054980013343 := by
  unfold tailWord_404442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687802900195795509877895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9834141067188788026341053 3687802900195795509877895)
  ·
    refine ⟨5531704350293693264816843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3687802900195795509877895 5531704350293693264816843)
    ·
      refine ⟨8297556525440539897225265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5531704350293693264816843 8297556525440539897225265)
      ·
        refine ⟨6223167394080404922918949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8297556525440539897225265 6223167394080404922918949)
        ·
          refine ⟨1166843886390075923047303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6223167394080404922918949 1166843886390075923047303)
          ·
            refine ⟨1750265829585113884570955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166843886390075923047303 1750265829585113884570955)
            ·
              refine ⟨2625398744377670826856433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750265829585113884570955 2625398744377670826856433)
              ·
                refine ⟨1969049058283253120142325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625398744377670826856433 1969049058283253120142325)
                ·
                  refine ⟨184598349214054980013343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969049058283253120142325 184598349214054980013343)
                  ·
                    rfl

theorem cell20_404442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_404442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404442 prefixEnd_404442 := by exact prefixLift 404442
  have htrace : WordTrace (prefixWord ++ tailWord_404442) baseStart_404442 baseEnd_404442 := by
    simpa [prefixWord, tailWord_404442, baseEnd_404442] using wordTrace_append hprefix tailTrace_404442
  have hstable : (prefixWord ++ tailWord_404442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404442).length < 2 ^ (prefixWord ++ tailWord_404442).sum := by decide
  have hdescent : baseEnd_404442 < baseStart_404442 := by decide
  rcases family_descends (prefixWord ++ tailWord_404442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404456 : List Nat := [2, 1, 4, 1, 1, 1, 10]
def baseStart_404456 : Nat := 118140960795 + 404456 * 2 ^ 59
def prefixEnd_404456 : Nat := 4983230072969 + 3 ^ 40 * 404456 * 2
def baseEnd_404456 : Nat := 20511637688392572616291

theorem tailTrace_404456 : CollatzResearch.WordTrace tailWord_404456 prefixEnd_404456 20511637688392572616291 := by
  unfold tailWord_404456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375861111366231215260611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9834481481821641620347481 7375861111366231215260611)
  ·
    refine ⟨11063791667049346822890917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375861111366231215260611 11063791667049346822890917)
    ·
      refine ⟨2074460937571752529292047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11063791667049346822890917 2074460937571752529292047)
      ·
        refine ⟨3111691406357628793938071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074460937571752529292047 3111691406357628793938071)
        ·
          refine ⟨4667537109536443190907107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111691406357628793938071 4667537109536443190907107)
          ·
            refine ⟨7001305664304664786360661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4667537109536443190907107 7001305664304664786360661)
            ·
              refine ⟨20511637688392572616291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7001305664304664786360661 20511637688392572616291)
              ·
                rfl

theorem cell20_404456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_404456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404456 prefixEnd_404456 := by exact prefixLift 404456
  have htrace : WordTrace (prefixWord ++ tailWord_404456) baseStart_404456 baseEnd_404456 := by
    simpa [prefixWord, tailWord_404456, baseEnd_404456] using wordTrace_append hprefix tailTrace_404456
  have hstable : (prefixWord ++ tailWord_404456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404456).length < 2 ^ (prefixWord ++ tailWord_404456).sum := by decide
  have hdescent : baseEnd_404456 < baseStart_404456 := by decide
  rcases family_descends (prefixWord ++ tailWord_404456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404462 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_404462 : Nat := 118140960795 + 404462 * 2 ^ 59
def prefixEnd_404462 : Nat := 4983230072969 + 3 ^ 40 * 404462 * 2
def baseEnd_404462 : Nat := 184607477759023799346595

theorem tailTrace_404462 : CollatzResearch.WordTrace tailWord_404462 prefixEnd_404462 184607477759023799346595 := by
  unfold tailWord_404462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843992632588840681904955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9834627373807150303493093 1843992632588840681904955)
  ·
    refine ⟨2765988948883261022857433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1843992632588840681904955 2765988948883261022857433)
    ·
      refine ⟨2074491711662445767143075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765988948883261022857433 2074491711662445767143075)
      ·
        refine ⟨3111737567493668650714613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074491711662445767143075 3111737567493668650714613)
        ·
          refine ⟨291725396952531436004495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3111737567493668650714613 291725396952531436004495)
          ·
            refine ⟨437588095428797154006743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291725396952531436004495 437588095428797154006743)
            ·
              refine ⟨656382143143195731010115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437588095428797154006743 656382143143195731010115)
              ·
                refine ⟨984573214714793596515173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656382143143195731010115 984573214714793596515173)
                ·
                  refine ⟨184607477759023799346595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 984573214714793596515173 184607477759023799346595)
                  ·
                    rfl

theorem cell20_404462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_404462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404462 prefixEnd_404462 := by exact prefixLift 404462
  have htrace : WordTrace (prefixWord ++ tailWord_404462) baseStart_404462 baseEnd_404462 := by
    simpa [prefixWord, tailWord_404462, baseEnd_404462] using wordTrace_append hprefix tailTrace_404462
  have hstable : (prefixWord ++ tailWord_404462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404462).length < 2 ^ (prefixWord ++ tailWord_404462).sum := by decide
  have hdescent : baseEnd_404462 < baseStart_404462 := by decide
  rcases family_descends (prefixWord ++ tailWord_404462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404468 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_404468 : Nat := 118140960795 + 404468 * 2 ^ 59
def prefixEnd_404468 : Nat := 4983230072969 + 3 ^ 40 * 404468 * 2
def baseEnd_404468 : Nat := 184610216322514445146571

theorem tailTrace_404468 : CollatzResearch.WordTrace tailWord_404468 prefixEnd_404468 184610216322514445146571 := by
  unfold tailWord_404468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376079949344494239979029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9834773265792658986638705 7376079949344494239979029)
  ·
    refine ⟨345753747625523167499017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7376079949344494239979029 345753747625523167499017)
    ·
      refine ⟨259315310719142375624263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345753747625523167499017 259315310719142375624263)
      ·
        refine ⟨388972966078713563436395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259315310719142375624263 388972966078713563436395)
        ·
          refine ⟨583459449118070345154593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388972966078713563436395 583459449118070345154593)
          ·
            refine ⟨437594586838552758865945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583459449118070345154593 437594586838552758865945)
            ·
              refine ⟨328195940128914569149459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437594586838552758865945 328195940128914569149459)
              ·
                refine ⟨492293910193371853724189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328195940128914569149459 492293910193371853724189)
                ·
                  refine ⟨184610216322514445146571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492293910193371853724189 184610216322514445146571)
                  ·
                    rfl

theorem cell20_404468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_404468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404468 prefixEnd_404468 := by exact prefixLift 404468
  have htrace : WordTrace (prefixWord ++ tailWord_404468) baseStart_404468 baseEnd_404468 := by
    simpa [prefixWord, tailWord_404468, baseEnd_404468] using wordTrace_append hprefix tailTrace_404468
  have hstable : (prefixWord ++ tailWord_404468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404468).length < 2 ^ (prefixWord ++ tailWord_404468).sum := by decide
  have hdescent : baseEnd_404468 < baseStart_404468 := by decide
  rcases family_descends (prefixWord ++ tailWord_404468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404469 : List Nat := [1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_404469 : Nat := 118140960795 + 404469 * 2 ^ 59
def prefixEnd_404469 : Nat := 4983230072969 + 3 ^ 40 * 404469 * 2
def baseEnd_404469 : Nat := 61536890916587628704411

theorem tailTrace_404469 : CollatzResearch.WordTrace tailWord_404469 prefixEnd_404469 61536890916587628704411 := by
  unfold tailWord_404469
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752196371685365650744461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9834797581123577100496307 14752196371685365650744461)
  ·
    refine ⟨5532073639382012119029173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14752196371685365650744461 5532073639382012119029173)
    ·
      refine ⟨518631903692063636158985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5532073639382012119029173 518631903692063636158985)
      ·
        refine ⟨388973927769047727119239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518631903692063636158985 388973927769047727119239)
        ·
          refine ⟨583460891653571590678859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388973927769047727119239 583460891653571590678859)
          ·
            refine ⟨875191337480357386018289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583460891653571590678859 875191337480357386018289)
            ·
              refine ⟨656393503110268039513717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875191337480357386018289 656393503110268039513717)
              ·
                refine ⟨61536890916587628704411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 656393503110268039513717 61536890916587628704411)
                ·
                  rfl

theorem cell20_404469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_404469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404469 prefixEnd_404469 := by exact prefixLift 404469
  have htrace : WordTrace (prefixWord ++ tailWord_404469) baseStart_404469 baseEnd_404469 := by
    simpa [prefixWord, tailWord_404469, baseEnd_404469] using wordTrace_append hprefix tailTrace_404469
  have hstable : (prefixWord ++ tailWord_404469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404469).length < 2 ^ (prefixWord ++ tailWord_404469).sum := by decide
  have hdescent : baseEnd_404469 < baseStart_404469 := by decide
  rcases family_descends (prefixWord ++ tailWord_404469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404476 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_404476 : Nat := 118140960795 + 404476 * 2 ^ 59
def prefixEnd_404476 : Nat := 4983230072969 + 3 ^ 40 * 404476 * 2
def baseEnd_404476 : Nat := 184613867740501972879871

theorem tailTrace_404476 : CollatzResearch.WordTrace tailWord_404476 prefixEnd_404476 184613867740501972879871 := by
  unfold tailWord_404476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376225841330002923124641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9834967788440003897499521 7376225841330002923124641)
  ·
    refine ⟨5532169380997502192343481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7376225841330002923124641 5532169380997502192343481)
    ·
      refine ⟨4149127035748126644257611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5532169380997502192343481 4149127035748126644257611)
      ·
        refine ⟨6223690553622189966386417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149127035748126644257611 6223690553622189966386417)
        ·
          refine ⟨4667767915216642474789813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6223690553622189966386417 4667767915216642474789813)
          ·
            refine ⟨437603242051560232011545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4667767915216642474789813 437603242051560232011545)
            ·
              refine ⟨328202431538670174008659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437603242051560232011545 328202431538670174008659)
              ·
                refine ⟨492303647308005261012989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328202431538670174008659 492303647308005261012989)
                ·
                  refine ⟨184613867740501972879871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492303647308005261012989 184613867740501972879871)
                  ·
                    rfl

theorem cell20_404476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_404476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404476 prefixEnd_404476 := by exact prefixLift 404476
  have htrace : WordTrace (prefixWord ++ tailWord_404476) baseStart_404476 baseEnd_404476 := by
    simpa [prefixWord, tailWord_404476, baseEnd_404476] using wordTrace_append hprefix tailTrace_404476
  have hstable : (prefixWord ++ tailWord_404476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404476).length < 2 ^ (prefixWord ++ tailWord_404476).sum := by decide
  have hdescent : baseEnd_404476 < baseStart_404476 := by decide
  rcases family_descends (prefixWord ++ tailWord_404476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404487 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_404487 : Nat := 118140960795 + 404487 * 2 ^ 59
def prefixEnd_404487 : Nat := 4983230072969 + 3 ^ 40 * 404487 * 2
def baseEnd_404487 : Nat := 184618888440234823513159

theorem tailTrace_404487 : CollatzResearch.WordTrace tailWord_404487 prefixEnd_404487 184618888440234823513159 := by
  unfold tailWord_404487
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752852885620154724899715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9835235257080103149933143 14752852885620154724899715)
  ·
    refine ⟨22129279328430232087349573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14752852885620154724899715 22129279328430232087349573)
    ·
      refine ⟨4149239874080668516378045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22129279328430232087349573 4149239874080668516378045)
      ·
        refine ⟨1555964952780250693641767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4149239874080668516378045 1555964952780250693641767)
        ·
          refine ⟨2333947429170376040462651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555964952780250693641767 2333947429170376040462651)
          ·
            refine ⟨3500921143755564060693977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333947429170376040462651 3500921143755564060693977)
            ·
              refine ⟨2625690857816673045520483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500921143755564060693977 2625690857816673045520483)
              ·
                refine ⟨3938536286725009568280725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625690857816673045520483 3938536286725009568280725)
                ·
                  refine ⟨184618888440234823513159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3938536286725009568280725 184618888440234823513159)
                  ·
                    rfl

theorem cell20_404487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_404487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404487 prefixEnd_404487 := by exact prefixLift 404487
  have htrace : WordTrace (prefixWord ++ tailWord_404487) baseStart_404487 baseEnd_404487 := by
    simpa [prefixWord, tailWord_404487, baseEnd_404487] using wordTrace_append hprefix tailTrace_404487
  have hstable : (prefixWord ++ tailWord_404487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404487).length < 2 ^ (prefixWord ++ tailWord_404487).sum := by decide
  have hdescent : baseEnd_404487 < baseStart_404487 := by decide
  rcases family_descends (prefixWord ++ tailWord_404487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404542 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_404542 : Nat := 118140960795 + 404542 * 2 ^ 59
def prefixEnd_404542 : Nat := 4983230072969 + 3 ^ 40 * 404542 * 2
def baseEnd_404542 : Nat := 184643991938899076679601

theorem tailTrace_404542 : CollatzResearch.WordTrace tailWord_404542 prefixEnd_404542 184643991938899076679601 := by
  unfold tailWord_404542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844357362552612389768985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9836572600280599412101253 1844357362552612389768985)
  ·
    refine ⟨1383268021914459292326739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1844357362552612389768985 1383268021914459292326739)
    ·
      refine ⟨2074902032871688938490109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383268021914459292326739 2074902032871688938490109)
      ·
        refine ⟨778088262326883351933791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2074902032871688938490109 778088262326883351933791)
        ·
          refine ⟨1167132393490325027900687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778088262326883351933791 1167132393490325027900687)
          ·
            refine ⟨1750698590235487541851031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167132393490325027900687 1750698590235487541851031)
            ·
              refine ⟨2626047885353231312776547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750698590235487541851031 2626047885353231312776547)
              ·
                refine ⟨3939071828029846969164821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626047885353231312776547 3939071828029846969164821)
                ·
                  refine ⟨184643991938899076679601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3939071828029846969164821 184643991938899076679601)
                  ·
                    rfl

theorem cell20_404542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_404542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404542 prefixEnd_404542 := by exact prefixLift 404542
  have htrace : WordTrace (prefixWord ++ tailWord_404542) baseStart_404542 baseEnd_404542 := by
    simpa [prefixWord, tailWord_404542, baseEnd_404542] using wordTrace_append hprefix tailTrace_404542
  have hstable : (prefixWord ++ tailWord_404542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404542).length < 2 ^ (prefixWord ++ tailWord_404542).sum := by decide
  have hdescent : baseEnd_404542 < baseStart_404542 := by decide
  rcases family_descends (prefixWord ++ tailWord_404542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404590 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_404590 : Nat := 118140960795 + 404590 * 2 ^ 59
def prefixEnd_404590 : Nat := 4983230072969 + 3 ^ 40 * 404590 * 2
def baseEnd_404590 : Nat := 184665900446824243079405

theorem tailTrace_404590 : CollatzResearch.WordTrace tailWord_404590 prefixEnd_404590 184665900446824243079405 := by
  unfold tailWord_404590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844576200530875414487403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9837739736164668877266149 1844576200530875414487403)
  ·
    refine ⟨2766864300796313121731105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844576200530875414487403 2766864300796313121731105)
    ·
      refine ⟨2075148225597234841298329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2766864300796313121731105 2075148225597234841298329)
      ·
        refine ⟨1556361169197926130973747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075148225597234841298329 1556361169197926130973747)
        ·
          refine ⟨2334541753796889196460621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556361169197926130973747 2334541753796889196460621)
          ·
            refine ⟨875453157673833448672733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2334541753796889196460621 875453157673833448672733)
            ·
              refine ⟨328294934127687543252275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 875453157673833448672733 328294934127687543252275)
              ·
                refine ⟨492442401191531314878413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328294934127687543252275 492442401191531314878413)
                ·
                  refine ⟨184665900446824243079405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492442401191531314878413 184665900446824243079405)
                  ·
                    rfl

theorem cell20_404590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_404590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404590 prefixEnd_404590 := by exact prefixLift 404590
  have htrace : WordTrace (prefixWord ++ tailWord_404590) baseStart_404590 baseEnd_404590 := by
    simpa [prefixWord, tailWord_404590, baseEnd_404590] using wordTrace_append hprefix tailTrace_404590
  have hstable : (prefixWord ++ tailWord_404590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404590).length < 2 ^ (prefixWord ++ tailWord_404590).sum := by decide
  have hdescent : baseEnd_404590 < baseStart_404590 := by decide
  rcases family_descends (prefixWord ++ tailWord_404590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404632 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_404632 : Nat := 118140960795 + 404632 * 2 ^ 59
def prefixEnd_404632 : Nat := 4983230072969 + 3 ^ 40 * 404632 * 2
def baseEnd_404632 : Nat := 184685070391258763679233

theorem tailTrace_404632 : CollatzResearch.WordTrace tailWord_404632 prefixEnd_404632 184685070391258763679233 := by
  unfold tailWord_404632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379070735047422244464075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9838760980063229659285433 7379070735047422244464075)
  ·
    refine ⟨11068606102571133366696113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7379070735047422244464075 11068606102571133366696113)
    ·
      refine ⟨8301454576928350025022085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11068606102571133366696113 8301454576928350025022085)
      ·
        refine ⟨1556522733174065629691641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8301454576928350025022085 1556522733174065629691641)
        ·
          refine ⟨1167392049880549222268731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556522733174065629691641 1167392049880549222268731)
          ·
            refine ⟨1751088074820823833403097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167392049880549222268731 1751088074820823833403097)
            ·
              refine ⟨1313316056115617875052323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751088074820823833403097 1313316056115617875052323)
              ·
                refine ⟨1969974084173426812578485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313316056115617875052323 1969974084173426812578485)
                ·
                  refine ⟨184685070391258763679233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969974084173426812578485 184685070391258763679233)
                  ·
                    rfl

theorem cell20_404632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_404632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404632 prefixEnd_404632 := by exact prefixLift 404632
  have htrace : WordTrace (prefixWord ++ tailWord_404632) baseStart_404632 baseEnd_404632 := by
    simpa [prefixWord, tailWord_404632, baseEnd_404632] using wordTrace_append hprefix tailTrace_404632
  have hstable : (prefixWord ++ tailWord_404632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404632).length < 2 ^ (prefixWord ++ tailWord_404632).sum := by decide
  have hdescent : baseEnd_404632 < baseStart_404632 := by decide
  rcases family_descends (prefixWord ++ tailWord_404632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404642 : List Nat := [3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_404642 : Nat := 118140960795 + 404642 * 2 ^ 59
def prefixEnd_404642 : Nat := 4983230072969 + 3 ^ 40 * 404642 * 2
def baseEnd_404642 : Nat := 61563211554581057781953

theorem tailTrace_404642 : CollatzResearch.WordTrace tailWord_404642 prefixEnd_404642 61563211554581057781953 := by
  unfold tailWord_404642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689626550014654049198045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9839004133372410797861453 3689626550014654049198045)
  ·
    refine ⟨1383609956255495268449267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3689626550014654049198045 1383609956255495268449267)
    ·
      refine ⟨2075414934383242902673901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383609956255495268449267 2075414934383242902673901)
      ·
        refine ⟨778280600393716088502713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2075414934383242902673901 778280600393716088502713)
        ·
          refine ⟨583710450295287066377035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778280600393716088502713 583710450295287066377035)
          ·
            refine ⟨875565675442930599565553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583710450295287066377035 875565675442930599565553)
            ·
              refine ⟨656674256582197949674165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875565675442930599565553 656674256582197949674165)
              ·
                refine ⟨61563211554581057781953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 656674256582197949674165 61563211554581057781953)
                ·
                  rfl

theorem cell20_404642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_404642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404642 prefixEnd_404642 := by exact prefixLift 404642
  have htrace : WordTrace (prefixWord ++ tailWord_404642) baseStart_404642 baseEnd_404642 := by
    simpa [prefixWord, tailWord_404642, baseEnd_404642] using wordTrace_append hprefix tailTrace_404642
  have hstable : (prefixWord ++ tailWord_404642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404642).length < 2 ^ (prefixWord ++ tailWord_404642).sum := by decide
  have hdescent : baseEnd_404642 < baseStart_404642 := by decide
  rcases family_descends (prefixWord ++ tailWord_404642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404708 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_404708 : Nat := 118140960795 + 404708 * 2 ^ 59
def prefixEnd_404708 : Nat := 4983230072969 + 3 ^ 40 * 404708 * 2
def baseEnd_404708 : Nat := 184719758862140277145589

theorem tailTrace_404708 : CollatzResearch.WordTrace tailWord_404708 prefixEnd_404708 184719758862140277145589 := by
  unfold tailWord_404708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380456708909754734347389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9840608945213006312463185 7380456708909754734347389)
  ·
    refine ⟨2767671265841158025380271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7380456708909754734347389 2767671265841158025380271)
    ·
      refine ⟨4151506898761737038070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767671265841158025380271 4151506898761737038070407)
      ·
        refine ⟨6227260348142605557105611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151506898761737038070407 6227260348142605557105611)
        ·
          refine ⟨9340890522213908335658417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227260348142605557105611 9340890522213908335658417)
          ·
            refine ⟨7005667891660431251743813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340890522213908335658417 7005667891660431251743813)
            ·
              refine ⟨1313562729686330859701965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7005667891660431251743813 1313562729686330859701965)
              ·
                refine ⟨492586023632374072388237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313562729686330859701965 492586023632374072388237)
                ·
                  refine ⟨184719758862140277145589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492586023632374072388237 184719758862140277145589)
                  ·
                    rfl

theorem cell20_404708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_404708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404708 prefixEnd_404708 := by exact prefixLift 404708
  have htrace : WordTrace (prefixWord ++ tailWord_404708) baseStart_404708 baseEnd_404708 := by
    simpa [prefixWord, tailWord_404708, baseEnd_404708] using wordTrace_append hprefix tailTrace_404708
  have hstable : (prefixWord ++ tailWord_404708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404708).length < 2 ^ (prefixWord ++ tailWord_404708).sum := by decide
  have hdescent : baseEnd_404708 < baseStart_404708 := by decide
  rcases family_descends (prefixWord ++ tailWord_404708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404715 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_404715 : Nat := 118140960795 + 404715 * 2 ^ 59
def prefixEnd_404715 : Nat := 4983230072969 + 3 ^ 40 * 404715 * 2
def baseEnd_404715 : Nat := 184722953852879363912227

theorem tailTrace_404715 : CollatzResearch.WordTrace tailWord_404715 prefixEnd_404715 184722953852879363912227 := by
  unfold tailWord_404715
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761168728794149664199599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9840779152529433109466399 14761168728794149664199599)
  ·
    refine ⟨22141753093191224496299399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761168728794149664199599 22141753093191224496299399)
    ·
      refine ⟨33212629639786836744449099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141753093191224496299399 33212629639786836744449099)
      ·
        refine ⟨49818944459680255116673649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33212629639786836744449099 49818944459680255116673649)
        ·
          refine ⟨37364208344760191337505237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49818944459680255116673649 37364208344760191337505237)
          ·
            refine ⟨875723633080316984472779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37364208344760191337505237 875723633080316984472779)
            ·
              refine ⟨1313585449620475476709169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875723633080316984472779 1313585449620475476709169)
              ·
                refine ⟨985189087215356607531877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313585449620475476709169 985189087215356607531877)
                ·
                  refine ⟨184722953852879363912227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985189087215356607531877 184722953852879363912227)
                  ·
                    rfl

theorem cell20_404715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_404715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404715 prefixEnd_404715 := by exact prefixLift 404715
  have htrace : WordTrace (prefixWord ++ tailWord_404715) baseStart_404715 baseEnd_404715 := by
    simpa [prefixWord, tailWord_404715, baseEnd_404715] using wordTrace_append hprefix tailTrace_404715
  have hstable : (prefixWord ++ tailWord_404715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404715).length < 2 ^ (prefixWord ++ tailWord_404715).sum := by decide
  have hdescent : baseEnd_404715 < baseStart_404715 := by decide
  rcases family_descends (prefixWord ++ tailWord_404715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404724 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_404724 : Nat := 118140960795 + 404724 * 2 ^ 59
def prefixEnd_404724 : Nat := 4983230072969 + 3 ^ 40 * 404724 * 2
def baseEnd_404724 : Nat := 184727061698115332612191

theorem tailTrace_404724 : CollatzResearch.WordTrace tailWord_404724 prefixEnd_404724 184727061698115332612191 := by
  unfold tailWord_404724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380748492880772100638613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9840997990507696134184817 7380748492880772100638613)
  ·
    refine ⟨345972585603786192217435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7380748492880772100638613 345972585603786192217435)
    ·
      refine ⟨518958878405679288326153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345972585603786192217435 518958878405679288326153)
      ·
        refine ⟨389219158804259466244615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518958878405679288326153 389219158804259466244615)
        ·
          refine ⟨583828738206389199366923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389219158804259466244615 583828738206389199366923)
          ·
            refine ⟨875743107309583799050385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583828738206389199366923 875743107309583799050385)
            ·
              refine ⟨656807330482187849287789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875743107309583799050385 656807330482187849287789)
              ·
                refine ⟨246302748930820443482921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656807330482187849287789 246302748930820443482921)
                ·
                  refine ⟨184727061698115332612191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246302748930820443482921 184727061698115332612191)
                  ·
                    rfl

theorem cell20_404724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_404724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404724 prefixEnd_404724 := by exact prefixLift 404724
  have htrace : WordTrace (prefixWord ++ tailWord_404724) baseStart_404724 baseEnd_404724 := by
    simpa [prefixWord, tailWord_404724, baseEnd_404724] using wordTrace_append hprefix tailTrace_404724
  have hstable : (prefixWord ++ tailWord_404724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404724).length < 2 ^ (prefixWord ++ tailWord_404724).sum := by decide
  have hdescent : baseEnd_404724 < baseStart_404724 := by decide
  rcases family_descends (prefixWord ++ tailWord_404724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404729 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_404729 : Nat := 118140960795 + 404729 * 2 ^ 59
def prefixEnd_404729 : Nat := 4983230072969 + 3 ^ 40 * 404729 * 2
def baseEnd_404729 : Nat := 184729343834357537445503

theorem tailTrace_404729 : CollatzResearch.WordTrace tailWord_404729 prefixEnd_404729 184729343834357537445503 := by
  unfold tailWord_404729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761679350743430055209241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9841119567162286703472827 14761679350743430055209241)
  ·
    refine ⟨11071259513057572541406931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14761679350743430055209241 11071259513057572541406931)
    ·
      refine ⟨16606889269586358812110397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071259513057572541406931 16606889269586358812110397)
      ·
        refine ⟨6227583476094884554541399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16606889269586358812110397 6227583476094884554541399)
        ·
          refine ⟨9341375214142326831812099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227583476094884554541399 9341375214142326831812099)
          ·
            refine ⟨14012062821213490247718149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9341375214142326831812099 14012062821213490247718149)
            ·
              refine ⟨2627261778977529421447153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14012062821213490247718149 2627261778977529421447153)
              ·
                refine ⟨1970446334233147066085365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627261778977529421447153 1970446334233147066085365)
                ·
                  refine ⟨184729343834357537445503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970446334233147066085365 184729343834357537445503)
                  ·
                    rfl

theorem cell20_404729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_404729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404729 prefixEnd_404729 := by exact prefixLift 404729
  have htrace : WordTrace (prefixWord ++ tailWord_404729) baseStart_404729 baseEnd_404729 := by
    simpa [prefixWord, tailWord_404729, baseEnd_404729] using wordTrace_append hprefix tailTrace_404729
  have hstable : (prefixWord ++ tailWord_404729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404729).length < 2 ^ (prefixWord ++ tailWord_404729).sum := by decide
  have hdescent : baseEnd_404729 < baseStart_404729 := by decide
  rcases family_descends (prefixWord ++ tailWord_404729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404736 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_404736 : Nat := 118140960795 + 404736 * 2 ^ 59
def prefixEnd_404736 : Nat := 4983230072969 + 3 ^ 40 * 404736 * 2
def baseEnd_404736 : Nat := 184732538825096624212141

theorem tailTrace_404736 : CollatzResearch.WordTrace tailWord_404736 prefixEnd_404736 184732538825096624212141 := by
  unfold tailWord_404736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380967330859035125357031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9841289774478713500476041 7380967330859035125357031)
  ·
    refine ⟨11071450996288552688035547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7380967330859035125357031 11071450996288552688035547)
    ·
      refine ⟨16607176494432829032053321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071450996288552688035547 16607176494432829032053321)
      ·
        refine ⟨12455382370824621774039991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16607176494432829032053321 12455382370824621774039991)
        ·
          refine ⟨18683073556236932661059987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12455382370824621774039991 18683073556236932661059987)
          ·
            refine ⟨28024610334355398991589981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18683073556236932661059987 28024610334355398991589981)
            ·
              refine ⟨10509228875383274621846243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28024610334355398991589981 10509228875383274621846243)
              ·
                refine ⟨15763843313074911932769365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10509228875383274621846243 15763843313074911932769365)
                ·
                  refine ⟨184732538825096624212141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15763843313074911932769365 184732538825096624212141)
                  ·
                    rfl

theorem cell20_404736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_404736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404736 prefixEnd_404736 := by exact prefixLift 404736
  have htrace : WordTrace (prefixWord ++ tailWord_404736) baseStart_404736 baseEnd_404736 := by
    simpa [prefixWord, tailWord_404736, baseEnd_404736] using wordTrace_append hprefix tailTrace_404736
  have hstable : (prefixWord ++ tailWord_404736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404736).length < 2 ^ (prefixWord ++ tailWord_404736).sum := by decide
  have hdescent : baseEnd_404736 < baseStart_404736 := by decide
  rcases family_descends (prefixWord ++ tailWord_404736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404753 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_404753 : Nat := 118140960795 + 404753 * 2 ^ 59
def prefixEnd_404753 : Nat := 4983230072969 + 3 ^ 40 * 404753 * 2
def baseEnd_404753 : Nat := 184740298088320120645405

theorem tailTrace_404753 : CollatzResearch.WordTrace tailWord_404753 prefixEnd_404753 184740298088320120645405 := by
  unfold tailWord_404753
  simp only [CollatzResearch.WordTrace]
  refine ⟨14762554702656482154082913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9841703135104321436055275 14762554702656482154082913)
  ·
    refine ⟨11071916026992361615562185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14762554702656482154082913 11071916026992361615562185)
    ·
      refine ⟨8303937020244271211671639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11071916026992361615562185 8303937020244271211671639)
      ·
        refine ⟨12455905530366406817507459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303937020244271211671639 12455905530366406817507459)
        ·
          refine ⟨18683858295549610226261189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12455905530366406817507459 18683858295549610226261189)
          ·
            refine ⟨3503223430415551917423973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18683858295549610226261189 3503223430415551917423973)
            ·
              refine ⟨656854393202915984516995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3503223430415551917423973 656854393202915984516995)
              ·
                refine ⟨985281589804373976775493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656854393202915984516995 985281589804373976775493)
                ·
                  refine ⟨184740298088320120645405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985281589804373976775493 184740298088320120645405)
                  ·
                    rfl

theorem cell20_404753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_404753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404753 prefixEnd_404753 := by exact prefixLift 404753
  have htrace : WordTrace (prefixWord ++ tailWord_404753) baseStart_404753 baseEnd_404753 := by
    simpa [prefixWord, tailWord_404753, baseEnd_404753] using wordTrace_append hprefix tailTrace_404753
  have hstable : (prefixWord ++ tailWord_404753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404753).length < 2 ^ (prefixWord ++ tailWord_404753).sum := by decide
  have hdescent : baseEnd_404753 < baseStart_404753 := by decide
  rcases family_descends (prefixWord ++ tailWord_404753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404787 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 2]
def baseStart_404787 : Nat := 118140960795 + 404787 * 2 ^ 59
def prefixEnd_404787 : Nat := 4983230072969 + 3 ^ 40 * 404787 * 2
def baseEnd_404787 : Nat := 184755816614767113511933

theorem tailTrace_404787 : CollatzResearch.WordTrace tailWord_404787 prefixEnd_404787 184755816614767113511933 := by
  unfold tailWord_404787
  simp only [CollatzResearch.WordTrace]
  refine ⟨14763794784533305960820615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9842529856355537307213743 14763794784533305960820615)
  ·
    refine ⟨22145692176799958941230923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14763794784533305960820615 22145692176799958941230923)
    ·
      refine ⟨33218538265199938411846385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22145692176799958941230923 33218538265199938411846385)
      ·
        refine ⟨24913903698899953808884789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33218538265199938411846385 24913903698899953808884789)
        ·
          refine ⟨2335678471771870669582949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24913903698899953808884789 2335678471771870669582949)
          ·
            refine ⟨437939713457225750546803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2335678471771870669582949 437939713457225750546803)
            ·
              refine ⟨656909570185838625820205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437939713457225750546803 656909570185838625820205)
              ·
                refine ⟨246341088819689484682577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656909570185838625820205 246341088819689484682577)
                ·
                  refine ⟨184755816614767113511933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246341088819689484682577 184755816614767113511933)
                  ·
                    rfl

theorem cell20_404787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 2].length) (baseStart_404787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404787 prefixEnd_404787 := by exact prefixLift 404787
  have htrace : WordTrace (prefixWord ++ tailWord_404787) baseStart_404787 baseEnd_404787 := by
    simpa [prefixWord, tailWord_404787, baseEnd_404787] using wordTrace_append hprefix tailTrace_404787
  have hstable : (prefixWord ++ tailWord_404787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404787).length < 2 ^ (prefixWord ++ tailWord_404787).sum := by decide
  have hdescent : baseEnd_404787 < baseStart_404787 := by decide
  rcases family_descends (prefixWord ++ tailWord_404787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404836 : List Nat := [2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_404836 : Nat := 118140960795 + 404836 * 2 ^ 59
def prefixEnd_404836 : Nat := 4983230072969 + 3 ^ 40 * 404836 * 2
def baseEnd_404836 : Nat := 61592727183313573626133

theorem tailTrace_404836 : CollatzResearch.WordTrace tailWord_404836 prefixEnd_404836 61592727183313573626133 := by
  unfold tailWord_404836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7382790980677893664677181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9843721307570524886236241 7382790980677893664677181)
  ·
    refine ⟨2768546617754210124253943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7382790980677893664677181 2768546617754210124253943)
    ·
      refine ⟨4152819926631315186380915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2768546617754210124253943 4152819926631315186380915)
      ·
        refine ⟨6229229889946972779571373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152819926631315186380915 6229229889946972779571373)
        ·
          refine ⟨2335961208730114792339265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6229229889946972779571373 2335961208730114792339265)
          ·
            refine ⟨1751970906547586094254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335961208730114792339265 1751970906547586094254449)
            ·
              refine ⟨1313978179910689570690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751970906547586094254449 1313978179910689570690837)
              ·
                refine ⟨61592727183313573626133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1313978179910689570690837 61592727183313573626133)
                ·
                  rfl

theorem cell20_404836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_404836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404836 prefixEnd_404836 := by exact prefixLift 404836
  have htrace : WordTrace (prefixWord ++ tailWord_404836) baseStart_404836 baseEnd_404836 := by
    simpa [prefixWord, tailWord_404836, baseEnd_404836] using wordTrace_append hprefix tailTrace_404836
  have hstable : (prefixWord ++ tailWord_404836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404836).length < 2 ^ (prefixWord ++ tailWord_404836).sum := by decide
  have hdescent : baseEnd_404836 < baseStart_404836 := by decide
  rcases family_descends (prefixWord ++ tailWord_404836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404853 : List Nat := [1, 3, 4, 1, 4, 7]
def baseStart_404853 : Nat := 118140960795 + 404853 * 2 ^ 59
def prefixEnd_404853 : Nat := 4983230072969 + 3 ^ 40 * 404853 * 2
def baseEnd_404853 : Nat := 6843923733820896937469

theorem tailTrace_404853 : CollatzResearch.WordTrace tailWord_404853 prefixEnd_404853 6843923733820896937469 := by
  unfold tailWord_404853
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766202002294199232723213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9844134668196132821815475 14766202002294199232723213)
  ·
    refine ⟨5537325750860324712271205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14766202002294199232723213 5537325750860324712271205)
    ·
      refine ⟨1038248578286310883550851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5537325750860324712271205 1038248578286310883550851)
      ·
        refine ⟨1557372867429466325326277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038248578286310883550851 1557372867429466325326277)
        ·
          refine ⟨292007412643024935998677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1557372867429466325326277 292007412643024935998677)
          ·
            refine ⟨6843923733820896937469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 292007412643024935998677 6843923733820896937469)
            ·
              rfl

theorem cell20_404853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 7].length) (baseStart_404853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404853 prefixEnd_404853 := by exact prefixLift 404853
  have htrace : WordTrace (prefixWord ++ tailWord_404853) baseStart_404853 baseEnd_404853 := by
    simpa [prefixWord, tailWord_404853, baseEnd_404853] using wordTrace_append hprefix tailTrace_404853
  have hstable : (prefixWord ++ tailWord_404853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404853).length < 2 ^ (prefixWord ++ tailWord_404853).sum := by decide
  have hdescent : baseEnd_404853 < baseStart_404853 := by decide
  rcases family_descends (prefixWord ++ tailWord_404853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404860 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_404860 : Nat := 118140960795 + 404860 * 2 ^ 59
def prefixEnd_404860 : Nat := 4983230072969 + 3 ^ 40 * 404860 * 2
def baseEnd_404860 : Nat := 184789135803903304078301

theorem tailTrace_404860 : CollatzResearch.WordTrace tailWord_404860 prefixEnd_404860 184789135803903304078301 := by
  unfold tailWord_404860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383228656634419714114017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9844304875512559618818689 7383228656634419714114017)
  ·
    refine ⟨5537421492475814785585513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7383228656634419714114017 5537421492475814785585513)
    ·
      refine ⟨4153066119356861089189135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5537421492475814785585513 4153066119356861089189135)
      ·
        refine ⟨6229599179035291633783703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153066119356861089189135 6229599179035291633783703)
        ·
          refine ⟨9344398768552937450675555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229599179035291633783703 9344398768552937450675555)
          ·
            refine ⟨14016598152829406176013333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344398768552937450675555 14016598152829406176013333)
            ·
              refine ⟨657028038413878414500625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14016598152829406176013333 657028038413878414500625)
              ·
                refine ⟨492771028810408810875469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657028038413878414500625 492771028810408810875469)
                ·
                  refine ⟨184789135803903304078301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492771028810408810875469 184789135803903304078301)
                  ·
                    rfl

theorem cell20_404860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_404860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404860 prefixEnd_404860 := by exact prefixLift 404860
  have htrace : WordTrace (prefixWord ++ tailWord_404860) baseStart_404860 baseEnd_404860 := by
    simpa [prefixWord, tailWord_404860, baseEnd_404860] using wordTrace_append hprefix tailTrace_404860
  have hstable : (prefixWord ++ tailWord_404860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404860).length < 2 ^ (prefixWord ++ tailWord_404860).sum := by decide
  have hdescent : baseEnd_404860 < baseStart_404860 := by decide
  rcases family_descends (prefixWord ++ tailWord_404860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404884 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_404884 : Nat := 118140960795 + 404884 * 2 ^ 59
def prefixEnd_404884 : Nat := 4983230072969 + 3 ^ 40 * 404884 * 2
def baseEnd_404884 : Nat := 184800090057865887278203

theorem tailTrace_404884 : CollatzResearch.WordTrace tailWord_404884 prefixEnd_404884 184800090057865887278203 := by
  unfold tailWord_404884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383666332590945763550853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9844888443454594351401137 7383666332590945763550853)
  ·
    refine ⟨1384437437360802330665785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7383666332590945763550853 1384437437360802330665785)
    ·
      refine ⟨1038328078020601747999339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1384437437360802330665785 1038328078020601747999339)
      ·
        refine ⟨1557492117030902621999009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038328078020601747999339 1557492117030902621999009)
        ·
          refine ⟨1168119087773176966499257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557492117030902621999009 1168119087773176966499257)
          ·
            refine ⟨876089315829882724874443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168119087773176966499257 876089315829882724874443)
            ·
              refine ⟨1314133973744824087311665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876089315829882724874443 1314133973744824087311665)
              ·
                refine ⟨985600480308618065483749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314133973744824087311665 985600480308618065483749)
                ·
                  refine ⟨184800090057865887278203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985600480308618065483749 184800090057865887278203)
                  ·
                    rfl

theorem cell20_404884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_404884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404884 prefixEnd_404884 := by exact prefixLift 404884
  have htrace : WordTrace (prefixWord ++ tailWord_404884) baseStart_404884 baseEnd_404884 := by
    simpa [prefixWord, tailWord_404884, baseEnd_404884] using wordTrace_append hprefix tailTrace_404884
  have hstable : (prefixWord ++ tailWord_404884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404884).length < 2 ^ (prefixWord ++ tailWord_404884).sum := by decide
  have hdescent : baseEnd_404884 < baseStart_404884 := by decide
  rcases family_descends (prefixWord ++ tailWord_404884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404919 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_404919 : Nat := 118140960795 + 404919 * 2 ^ 59
def prefixEnd_404919 : Nat := 4983230072969 + 3 ^ 40 * 404919 * 2
def baseEnd_404919 : Nat := 184816065011561321111393

theorem tailTrace_404919 : CollatzResearch.WordTrace tailWord_404919 prefixEnd_404919 184816065011561321111393 := by
  unfold tailWord_404919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768609220055092504625811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9845739480036728336417207 14768609220055092504625811)
  ·
    refine ⟨22152913830082638756938717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14768609220055092504625811 22152913830082638756938717)
    ·
      refine ⟨8307342686280989533852019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22152913830082638756938717 8307342686280989533852019)
      ·
        refine ⟨12461014029421484300778029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307342686280989533852019 12461014029421484300778029)
        ·
          refine ⟨4672880261033056612791761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12461014029421484300778029 4672880261033056612791761)
          ·
            refine ⟨3504660195774792459593821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672880261033056612791761 3504660195774792459593821)
            ·
              refine ⟨1314247573415547172347683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3504660195774792459593821 1314247573415547172347683)
              ·
                refine ⟨1971371360123320758521525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314247573415547172347683 1971371360123320758521525)
                ·
                  refine ⟨184816065011561321111393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971371360123320758521525 184816065011561321111393)
                  ·
                    rfl

theorem cell20_404919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_404919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404919 prefixEnd_404919 := by exact prefixLift 404919
  have htrace : WordTrace (prefixWord ++ tailWord_404919) baseStart_404919 baseEnd_404919 := by
    simpa [prefixWord, tailWord_404919, baseEnd_404919] using wordTrace_append hprefix tailTrace_404919
  have hstable : (prefixWord ++ tailWord_404919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404919).length < 2 ^ (prefixWord ++ tailWord_404919).sum := by decide
  have hdescent : baseEnd_404919 < baseStart_404919 := by decide
  rcases family_descends (prefixWord ++ tailWord_404919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404932 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_404932 : Nat := 118140960795 + 404932 * 2 ^ 59
def prefixEnd_404932 : Nat := 4983230072969 + 3 ^ 40 * 404932 * 2
def baseEnd_404932 : Nat := 184821998565791053678007

theorem tailTrace_404932 : CollatzResearch.WordTrace tailWord_404932 prefixEnd_404932 184821998565791053678007 := by
  unfold tailWord_404932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384541684503997862424525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9846055579338663816566033 7384541684503997862424525)
  ·
    refine ⟨2769203131688999198409197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7384541684503997862424525 2769203131688999198409197)
    ·
      refine ⟨1038451174383374699403449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2769203131688999198409197 1038451174383374699403449)
      ·
        refine ⟨778838380787531024552587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1038451174383374699403449 778838380787531024552587)
        ·
          refine ⟨1168257571181296536828881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778838380787531024552587 1168257571181296536828881)
          ·
            refine ⟨876193178385972402621661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1168257571181296536828881 876193178385972402621661)
            ·
              refine ⟨328572441894739650983123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876193178385972402621661 328572441894739650983123)
              ·
                refine ⟨492858662842109476474685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328572441894739650983123 492858662842109476474685)
                ·
                  refine ⟨184821998565791053678007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492858662842109476474685 184821998565791053678007)
                  ·
                    rfl

theorem cell20_404932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_404932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404932 prefixEnd_404932 := by exact prefixLift 404932
  have htrace : WordTrace (prefixWord ++ tailWord_404932) baseStart_404932 baseEnd_404932 := by
    simpa [prefixWord, tailWord_404932, baseEnd_404932] using wordTrace_append hprefix tailTrace_404932
  have hstable : (prefixWord ++ tailWord_404932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404932).length < 2 ^ (prefixWord ++ tailWord_404932).sum := by decide
  have hdescent : baseEnd_404932 < baseStart_404932 := by decide
  rcases family_descends (prefixWord ++ tailWord_404932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404964 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_404964 : Nat := 118140960795 + 404964 * 2 ^ 59
def prefixEnd_404964 : Nat := 4983230072969 + 3 ^ 40 * 404964 * 2
def baseEnd_404964 : Nat := 184836604237741164611209

theorem tailTrace_404964 : CollatzResearch.WordTrace tailWord_404964 prefixEnd_404964 184836604237741164611209 := by
  unfold tailWord_404964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385125252446032595006973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9846833669928043460009297 7385125252446032595006973)
  ·
    refine ⟨2769421969667262223127615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7385125252446032595006973 2769421969667262223127615)
    ·
      refine ⟨4154132954500893334691423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769421969667262223127615 4154132954500893334691423)
      ·
        refine ⟨6231199431751340002037135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154132954500893334691423 6231199431751340002037135)
        ·
          refine ⟨9346799147627010003055703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231199431751340002037135 9346799147627010003055703)
          ·
            refine ⟨14020198721440515004583555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346799147627010003055703 14020198721440515004583555)
            ·
              refine ⟨21030298082160772506875333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14020198721440515004583555 21030298082160772506875333)
              ·
                refine ⟨3943180890405144845039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21030298082160772506875333 3943180890405144845039125)
                ·
                  refine ⟨184836604237741164611209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3943180890405144845039125 184836604237741164611209)
                  ·
                    rfl

theorem cell20_404964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_404964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404964 prefixEnd_404964 := by exact prefixLift 404964
  have htrace : WordTrace (prefixWord ++ tailWord_404964) baseStart_404964 baseEnd_404964 := by
    simpa [prefixWord, tailWord_404964, baseEnd_404964] using wordTrace_append hprefix tailTrace_404964
  have hstable : (prefixWord ++ tailWord_404964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404964).length < 2 ^ (prefixWord ++ tailWord_404964).sum := by decide
  have hdescent : baseEnd_404964 < baseStart_404964 := by decide
  rcases family_descends (prefixWord ++ tailWord_404964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404974 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_404974 : Nat := 118140960795 + 404974 * 2 ^ 59
def prefixEnd_404974 : Nat := 4983230072969 + 3 ^ 40 * 404974 * 2
def baseEnd_404974 : Nat := 184841168510225574277835

theorem tailTrace_404974 : CollatzResearch.WordTrace tailWord_404974 prefixEnd_404974 184841168510225574277835 := by
  unfold tailWord_404974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846326904356979612234747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9847076823237224598585317 1846326904356979612234747)
  ·
    refine ⟨2769490356535469418352121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846326904356979612234747 2769490356535469418352121)
    ·
      refine ⟨2077117767401602063764091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2769490356535469418352121 2077117767401602063764091)
      ·
        refine ⟨3115676651102403095646137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077117767401602063764091 3115676651102403095646137)
        ·
          refine ⟨2336757488326802321734603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115676651102403095646137 2336757488326802321734603)
          ·
            refine ⟨3505136232490203482601905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336757488326802321734603 3505136232490203482601905)
            ·
              refine ⟨2628852174367652611951429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505136232490203482601905 2628852174367652611951429)
              ·
                refine ⟨492909782693934864740893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2628852174367652611951429 492909782693934864740893)
                ·
                  refine ⟨184841168510225574277835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 492909782693934864740893 184841168510225574277835)
                  ·
                    rfl

theorem cell20_404974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_404974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404974 prefixEnd_404974 := by exact prefixLift 404974
  have htrace : WordTrace (prefixWord ++ tailWord_404974) baseStart_404974 baseEnd_404974 := by
    simpa [prefixWord, tailWord_404974, baseEnd_404974] using wordTrace_append hprefix tailTrace_404974
  have hstable : (prefixWord ++ tailWord_404974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404974).length < 2 ^ (prefixWord ++ tailWord_404974).sum := by decide
  have hdescent : baseEnd_404974 < baseStart_404974 := by decide
  rcases family_descends (prefixWord ++ tailWord_404974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404977 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 2]
def baseStart_404977 : Nat := 118140960795 + 404977 * 2 ^ 59
def prefixEnd_404977 : Nat := 4983230072969 + 3 ^ 40 * 404977 * 2
def baseEnd_404977 : Nat := 184842537791970897177823

theorem tailTrace_404977 : CollatzResearch.WordTrace tailWord_404977 prefixEnd_404977 184842537791970897177823 := by
  unfold tailWord_404977
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770724653844968410237185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9847149769229978940158123 14770724653844968410237185)
  ·
    refine ⟨11078043490383726307677889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14770724653844968410237185 11078043490383726307677889)
    ·
      refine ⟨8308532617787794730758417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11078043490383726307677889 8308532617787794730758417)
      ·
        refine ⟨6231399463340846048068813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8308532617787794730758417 6231399463340846048068813)
        ·
          refine ⟨2336774798752817268025805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6231399463340846048068813 2336774798752817268025805)
          ·
            refine ⟨876290549532306475509677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336774798752817268025805 876290549532306475509677)
            ·
              refine ⟨328608956074614928316129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 876290549532306475509677 328608956074614928316129)
              ·
                refine ⟨246456717055961196237097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328608956074614928316129 246456717055961196237097)
                ·
                  refine ⟨184842537791970897177823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246456717055961196237097 184842537791970897177823)
                  ·
                    rfl

theorem cell20_404977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_404977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_404977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_404977 prefixEnd_404977 := by exact prefixLift 404977
  have htrace : WordTrace (prefixWord ++ tailWord_404977) baseStart_404977 baseEnd_404977 := by
    simpa [prefixWord, tailWord_404977, baseEnd_404977] using wordTrace_append hprefix tailTrace_404977
  have hstable : (prefixWord ++ tailWord_404977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404977).length < 2 ^ (prefixWord ++ tailWord_404977).sum := by decide
  have hdescent : baseEnd_404977 < baseStart_404977 := by decide
  rcases family_descends (prefixWord ++ tailWord_404977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405009 : List Nat := [1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_405009 : Nat := 118140960795 + 405009 * 2 ^ 59
def prefixEnd_405009 : Nat := 4983230072969 + 3 ^ 40 * 405009 * 2
def baseEnd_405009 : Nat := 61619047821307002703675

theorem tailTrace_405009 : CollatzResearch.WordTrace tailWord_405009 prefixEnd_405009 61619047821307002703675 := by
  unfold tailWord_405009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771891789729037875402081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9847927859819358583601387 14771891789729037875402081)
  ·
    refine ⟨11078918842296778406551561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14771891789729037875402081 11078918842296778406551561)
    ·
      refine ⟨8309189131722583804913671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11078918842296778406551561 8309189131722583804913671)
      ·
        refine ⟨12463783697583875707370507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309189131722583804913671 12463783697583875707370507)
        ·
          refine ⟨18695675546375813561055761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12463783697583875707370507 18695675546375813561055761)
          ·
            refine ⟨14021756659781860170791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18695675546375813561055761 14021756659781860170791821)
            ·
              refine ⟨5258158747418197564046933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14021756659781860170791821 5258158747418197564046933)
              ·
                refine ⟨61619047821307002703675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5258158747418197564046933 61619047821307002703675)
                ·
                  rfl

theorem cell20_405009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_405009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405009 prefixEnd_405009 := by exact prefixLift 405009
  have htrace : WordTrace (prefixWord ++ tailWord_405009) baseStart_405009 baseEnd_405009 := by
    simpa [prefixWord, tailWord_405009, baseEnd_405009] using wordTrace_append hprefix tailTrace_405009
  have hstable : (prefixWord ++ tailWord_405009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405009).length < 2 ^ (prefixWord ++ tailWord_405009).sum := by decide
  have hdescent : baseEnd_405009 < baseStart_405009 := by decide
  rcases family_descends (prefixWord ++ tailWord_405009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405022 : List Nat := [4, 3, 3, 1, 9]
def baseStart_405022 : Nat := 118140960795 + 405022 * 2 ^ 59
def prefixEnd_405022 : Nat := 4983230072969 + 3 ^ 40 * 405022 * 2
def baseEnd_405022 : Nat := 2282260210100626428119

theorem tailTrace_405022 : CollatzResearch.WordTrace tailWord_405022 prefixEnd_405022 2282260210100626428119 := by
  unfold tailWord_405022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846545742335242636953165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9848243959121294063750213 1846545742335242636953165)
  ·
    refine ⟨692454653375715988857437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1846545742335242636953165 692454653375715988857437)
    ·
      refine ⟨259670495015893495821539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 692454653375715988857437 259670495015893495821539)
      ·
        refine ⟨389505742523840243732309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259670495015893495821539 389505742523840243732309)
        ·
          refine ⟨2282260210100626428119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 389505742523840243732309 2282260210100626428119)
          ·
            rfl

theorem cell20_405022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 9].length) (baseStart_405022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405022 prefixEnd_405022 := by exact prefixLift 405022
  have htrace : WordTrace (prefixWord ++ tailWord_405022) baseStart_405022 baseEnd_405022 := by
    simpa [prefixWord, tailWord_405022, baseEnd_405022] using wordTrace_append hprefix tailTrace_405022
  have hstable : (prefixWord ++ tailWord_405022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405022).length < 2 ^ (prefixWord ++ tailWord_405022).sum := by decide
  have hdescent : baseEnd_405022 < baseStart_405022 := by decide
  rcases family_descends (prefixWord ++ tailWord_405022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405040 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_405040 : Nat := 118140960795 + 405040 * 2 ^ 59
def prefixEnd_405040 : Nat := 4983230072969 + 3 ^ 40 * 405040 * 2
def baseEnd_405040 : Nat := 184871292708622678077565

theorem tailTrace_405040 : CollatzResearch.WordTrace tailWord_405040 prefixEnd_405040 184871292708622678077565 := by
  unfold tailWord_405040
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386511226308365084890287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9848681635077820113187049 7386511226308365084890287)
  ·
    refine ⟨11079766839462547627335431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7386511226308365084890287 11079766839462547627335431)
    ·
      refine ⟨16619650259193821441003147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11079766839462547627335431 16619650259193821441003147)
      ·
        refine ⟨24929475388790732161504721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16619650259193821441003147 24929475388790732161504721)
        ·
          refine ⟨18697106541593049121128541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24929475388790732161504721 18697106541593049121128541)
          ·
            refine ⟨7011414953097393420423203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18697106541593049121128541 7011414953097393420423203)
            ·
              refine ⟨10517122429646090130634805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011414953097393420423203 10517122429646090130634805)
              ·
                refine ⟨985980227779320949747013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10517122429646090130634805 985980227779320949747013)
                ·
                  refine ⟨184871292708622678077565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985980227779320949747013 184871292708622678077565)
                  ·
                    rfl

theorem cell20_405040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_405040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405040 prefixEnd_405040 := by exact prefixLift 405040
  have htrace : WordTrace (prefixWord ++ tailWord_405040) baseStart_405040 baseEnd_405040 := by
    simpa [prefixWord, tailWord_405040, baseEnd_405040] using wordTrace_append hprefix tailTrace_405040
  have hstable : (prefixWord ++ tailWord_405040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405040).length < 2 ^ (prefixWord ++ tailWord_405040).sum := by decide
  have hdescent : baseEnd_405040 < baseStart_405040 := by decide
  rcases family_descends (prefixWord ++ tailWord_405040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405057 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_405057 : Nat := 118140960795 + 405057 * 2 ^ 59
def prefixEnd_405057 : Nat := 4983230072969 + 3 ^ 40 * 405057 * 2
def baseEnd_405057 : Nat := 184879051971846174510829

theorem tailTrace_405057 : CollatzResearch.WordTrace tailWord_405057 prefixEnd_405057 184879051971846174510829 := by
  unfold tailWord_405057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773642493555142073149425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9849094995703428048766283 14773642493555142073149425)
  ·
    refine ⟨11080231870166356554862069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14773642493555142073149425 11080231870166356554862069)
    ·
      refine ⟨1038771737828095927018319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11080231870166356554862069 1038771737828095927018319)
      ·
        refine ⟨1558157606742143890527479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038771737828095927018319 1558157606742143890527479)
        ·
          refine ⟨2337236410113215835791219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558157606742143890527479 2337236410113215835791219)
          ·
            refine ⟨3505854615169823753686829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337236410113215835791219 3505854615169823753686829)
            ·
              refine ⟨1314695480688683907632561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3505854615169823753686829 1314695480688683907632561)
              ·
                refine ⟨986021610516512930724421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314695480688683907632561 986021610516512930724421)
                ·
                  refine ⟨184879051971846174510829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986021610516512930724421 184879051971846174510829)
                  ·
                    rfl

theorem cell20_405057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_405057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405057 prefixEnd_405057 := by exact prefixLift 405057
  have htrace : WordTrace (prefixWord ++ tailWord_405057) baseStart_405057 baseEnd_405057 := by
    simpa [prefixWord, tailWord_405057, baseEnd_405057] using wordTrace_append hprefix tailTrace_405057
  have hstable : (prefixWord ++ tailWord_405057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405057).length < 2 ^ (prefixWord ++ tailWord_405057).sum := by decide
  have hdescent : baseEnd_405057 < baseStart_405057 := by decide
  rcases family_descends (prefixWord ++ tailWord_405057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405074 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_405074 : Nat := 118140960795 + 405074 * 2 ^ 59
def prefixEnd_405074 : Nat := 4983230072969 + 3 ^ 40 * 405074 * 2
def baseEnd_405074 : Nat := 184886811235069670944093

theorem tailTrace_405074 : CollatzResearch.WordTrace tailWord_405074 prefixEnd_405074 184886811235069670944093 := by
  unfold tailWord_405074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693565633623388494129569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9849508356329035984345517 3693565633623388494129569)
  ·
    refine ⟨2770174225217541370597177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3693565633623388494129569 2770174225217541370597177)
    ·
      refine ⟨2077630668913156027947883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2770174225217541370597177 2077630668913156027947883)
      ·
        refine ⟨3116446003369734041921825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077630668913156027947883 3116446003369734041921825)
        ·
          refine ⟨2337334502527300531441369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116446003369734041921825 2337334502527300531441369)
          ·
            refine ⟨1753000876895475398581027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337334502527300531441369 1753000876895475398581027)
            ·
              refine ⟨2629501315343213097871541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753000876895475398581027 2629501315343213097871541)
              ·
                refine ⟨246515748313426227925457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2629501315343213097871541 246515748313426227925457)
                ·
                  refine ⟨184886811235069670944093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246515748313426227925457 184886811235069670944093)
                  ·
                    rfl

theorem cell20_405074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_405074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405074 prefixEnd_405074 := by exact prefixLift 405074
  have htrace : WordTrace (prefixWord ++ tailWord_405074) baseStart_405074 baseEnd_405074 := by
    simpa [prefixWord, tailWord_405074, baseEnd_405074] using wordTrace_append hprefix tailTrace_405074
  have hstable : (prefixWord ++ tailWord_405074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405074).length < 2 ^ (prefixWord ++ tailWord_405074).sum := by decide
  have hdescent : baseEnd_405074 < baseStart_405074 := by decide
  rcases family_descends (prefixWord ++ tailWord_405074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405150 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_405150 : Nat := 118140960795 + 405150 * 2 ^ 59
def prefixEnd_405150 : Nat := 4983230072969 + 3 ^ 40 * 405150 * 2
def baseEnd_405150 : Nat := 184921499705951184410449

theorem tailTrace_405150 : CollatzResearch.WordTrace tailWord_405150 prefixEnd_405150 184921499705951184410449 := by
  unfold tailWord_405150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847129310277277369535613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9851356321478812637523269 1847129310277277369535613)
  ·
    refine ⟨692673491353979013575855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1847129310277277369535613 692673491353979013575855)
    ·
      refine ⟨1039010237030968520363783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692673491353979013575855 1039010237030968520363783)
      ·
        refine ⟨1558515355546452780545675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039010237030968520363783 1558515355546452780545675)
        ·
          refine ⟨2337773033319679170818513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558515355546452780545675 2337773033319679170818513)
          ·
            refine ⟨1753329774989759378113885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337773033319679170818513 1753329774989759378113885)
            ·
              refine ⟨657498665621159766792707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753329774989759378113885 657498665621159766792707)
              ·
                refine ⟨986247998431739650189061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657498665621159766792707 986247998431739650189061)
                ·
                  refine ⟨184921499705951184410449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986247998431739650189061 184921499705951184410449)
                  ·
                    rfl

theorem cell20_405150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_405150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405150 prefixEnd_405150 := by exact prefixLift 405150
  have htrace : WordTrace (prefixWord ++ tailWord_405150) baseStart_405150 baseEnd_405150 := by
    simpa [prefixWord, tailWord_405150, baseEnd_405150] using wordTrace_append hprefix tailTrace_405150
  have hstable : (prefixWord ++ tailWord_405150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405150).length < 2 ^ (prefixWord ++ tailWord_405150).sum := by decide
  have hdescent : baseEnd_405150 < baseStart_405150 := by decide
  rcases family_descends (prefixWord ++ tailWord_405150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405188 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_405188 : Nat := 118140960795 + 405188 * 2 ^ 59
def prefixEnd_405188 : Nat := 4983230072969 + 3 ^ 40 * 405188 * 2
def baseEnd_405188 : Nat := 184938843941391941143627

theorem tailTrace_405188 : CollatzResearch.WordTrace tailWord_405188 prefixEnd_405188 184938843941391941143627 := by
  unfold tailWord_405188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389210228040275723084109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9852280304053700964112145 7389210228040275723084109)
  ·
    refine ⟨2770953835515103396156541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7389210228040275723084109 2770953835515103396156541)
    ·
      refine ⟨1039107688318163773558703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2770953835515103396156541 1039107688318163773558703)
      ·
        refine ⟨1558661532477245660338055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039107688318163773558703 1558661532477245660338055)
        ·
          refine ⟨2337992298715868490507083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558661532477245660338055 2337992298715868490507083)
          ·
            refine ⟨3506988448073802735760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337992298715868490507083 3506988448073802735760625)
            ·
              refine ⟨2630241336055352051820469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506988448073802735760625 2630241336055352051820469)
              ·
                refine ⟨246585125255189254858169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2630241336055352051820469 246585125255189254858169)
                ·
                  refine ⟨184938843941391941143627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246585125255189254858169 184938843941391941143627)
                  ·
                    rfl

theorem cell20_405188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_405188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405188 prefixEnd_405188 := by exact prefixLift 405188
  have htrace : WordTrace (prefixWord ++ tailWord_405188) baseStart_405188 baseEnd_405188 := by
    simpa [prefixWord, tailWord_405188, baseEnd_405188] using wordTrace_append hprefix tailTrace_405188
  have hstable : (prefixWord ++ tailWord_405188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405188).length < 2 ^ (prefixWord ++ tailWord_405188).sum := by decide
  have hdescent : baseEnd_405188 < baseStart_405188 := by decide
  rcases family_descends (prefixWord ++ tailWord_405188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405202 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_405202 : Nat := 118140960795 + 405202 * 2 ^ 59
def prefixEnd_405202 : Nat := 4983230072969 + 3 ^ 40 * 405202 * 2
def baseEnd_405202 : Nat := 184945233922870114676903

theorem tailTrace_405202 : CollatzResearch.WordTrace tailWord_405202 prefixEnd_405202 184945233922870114676903 := by
  unfold tailWord_405202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694732769507457959294465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9852620718686554558118573 3694732769507457959294465)
  ·
    refine ⟨2771049577130593469470849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3694732769507457959294465 2771049577130593469470849)
    ·
      refine ⟨2078287182847945102103137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2771049577130593469470849 2078287182847945102103137)
      ·
        refine ⟨1558715387135958826577353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078287182847945102103137 1558715387135958826577353)
        ·
          refine ⟨1169036540351969119933015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1558715387135958826577353 1169036540351969119933015)
          ·
            refine ⟨1753554810527953679899523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169036540351969119933015 1753554810527953679899523)
            ·
              refine ⟨2630332215791930519849285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753554810527953679899523 2630332215791930519849285)
              ·
                refine ⟨493187290460986972471741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2630332215791930519849285 493187290460986972471741)
                ·
                  refine ⟨184945233922870114676903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493187290460986972471741 184945233922870114676903)
                  ·
                    rfl

theorem cell20_405202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_405202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405202 prefixEnd_405202 := by exact prefixLift 405202
  have htrace : WordTrace (prefixWord ++ tailWord_405202) baseStart_405202 baseEnd_405202 := by
    simpa [prefixWord, tailWord_405202, baseEnd_405202] using wordTrace_append hprefix tailTrace_405202
  have hstable : (prefixWord ++ tailWord_405202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405202).length < 2 ^ (prefixWord ++ tailWord_405202).sum := by decide
  have hdescent : baseEnd_405202 < baseStart_405202 := by decide
  rcases family_descends (prefixWord ++ tailWord_405202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405212 : List Nat := [2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_405212 : Nat := 118140960795 + 405212 * 2 ^ 59
def prefixEnd_405212 : Nat := 4983230072969 + 3 ^ 40 * 405212 * 2
def baseEnd_405212 : Nat := 61649932731784841447843

theorem tailTrace_405212 : CollatzResearch.WordTrace tailWord_405212 prefixEnd_405212 61649932731784841447843 := by
  unfold tailWord_405212
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389647903996801772520945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9852863871995735696694593 7389647903996801772520945)
  ·
    refine ⟨5542235927997601329390709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7389647903996801772520945 5542235927997601329390709)
    ·
      refine ⟨519584618249775124630379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5542235927997601329390709 519584618249775124630379)
      ·
        refine ⟨779376927374662686945569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519584618249775124630379 779376927374662686945569)
        ·
          refine ⟨584532695530997015209177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779376927374662686945569 584532695530997015209177)
          ·
            refine ⟨438399521648247761406883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584532695530997015209177 438399521648247761406883)
            ·
              refine ⟨657599282472371642110325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438399521648247761406883 657599282472371642110325)
              ·
                refine ⟨61649932731784841447843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657599282472371642110325 61649932731784841447843)
                ·
                  rfl

theorem cell20_405212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_405212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405212 prefixEnd_405212 := by exact prefixLift 405212
  have htrace : WordTrace (prefixWord ++ tailWord_405212) baseStart_405212 baseEnd_405212 := by
    simpa [prefixWord, tailWord_405212, baseEnd_405212] using wordTrace_append hprefix tailTrace_405212
  have hstable : (prefixWord ++ tailWord_405212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405212).length < 2 ^ (prefixWord ++ tailWord_405212).sum := by decide
  have hdescent : baseEnd_405212 < baseStart_405212 := by decide
  rcases family_descends (prefixWord ++ tailWord_405212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405247 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 2]
def baseStart_405247 : Nat := 118140960795 + 405247 * 2 ^ 59
def prefixEnd_405247 : Nat := 4983230072969 + 3 ^ 40 * 405247 * 2
def baseEnd_405247 : Nat := 184965773149049958176719

theorem tailTrace_405247 : CollatzResearch.WordTrace tailWord_405247 prefixEnd_405247 184965773149049958176719 := by
  unfold tailWord_405247
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780572362866804522565995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9853714908577869681710663 14780572362866804522565995)
  ·
    refine ⟨22170858544300206783848993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14780572362866804522565995 22170858544300206783848993)
    ·
      refine ⟨16628143908225155087886745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22170858544300206783848993 16628143908225155087886745)
      ·
        refine ⟨12471107931168866315915059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16628143908225155087886745 12471107931168866315915059)
        ·
          refine ⟨18706661896753299473872589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471107931168866315915059 18706661896753299473872589)
          ·
            refine ⟨7014998211282487302702221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18706661896753299473872589 7014998211282487302702221)
            ·
              refine ⟨2630624329230932738513333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7014998211282487302702221 2630624329230932738513333)
              ·
                refine ⟨246621030865399944235625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2630624329230932738513333 246621030865399944235625)
                ·
                  refine ⟨184965773149049958176719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246621030865399944235625 184965773149049958176719)
                  ·
                    rfl

theorem cell20_405247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 2].length) (baseStart_405247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405247 prefixEnd_405247 := by exact prefixLift 405247
  have htrace : WordTrace (prefixWord ++ tailWord_405247) baseStart_405247 baseEnd_405247 := by
    simpa [prefixWord, tailWord_405247, baseEnd_405247] using wordTrace_append hprefix tailTrace_405247
  have hstable : (prefixWord ++ tailWord_405247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405247).length < 2 ^ (prefixWord ++ tailWord_405247).sum := by decide
  have hdescent : baseEnd_405247 < baseStart_405247 := by decide
  rcases family_descends (prefixWord ++ tailWord_405247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405292 : List Nat := [2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_405292 : Nat := 118140960795 + 405292 * 2 ^ 59
def prefixEnd_405292 : Nat := 4983230072969 + 3 ^ 40 * 405292 * 2
def baseEnd_405292 : Nat := 61662104125076600558845

theorem tailTrace_405292 : CollatzResearch.WordTrace tailWord_405292 prefixEnd_405292 61662104125076600558845 := by
  unfold tailWord_405292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391106823851888603977065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9854809098469184805302753 7391106823851888603977065)
  ·
    refine ⟨5543330117888916452982799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391106823851888603977065 5543330117888916452982799)
    ·
      refine ⟨8314995176833374679474199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543330117888916452982799 8314995176833374679474199)
      ·
        refine ⟨12472492765250062019211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8314995176833374679474199 12472492765250062019211299)
        ·
          refine ⟨18708739147875093028816949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472492765250062019211299 18708739147875093028816949)
          ·
            refine ⟨1753944295113289971451589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18708739147875093028816949 1753944295113289971451589)
            ·
              refine ⟨328864555333741869647173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1753944295113289971451589 328864555333741869647173)
              ·
                refine ⟨61662104125076600558845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328864555333741869647173 61662104125076600558845)
                ·
                  rfl

theorem cell20_405292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_405292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405292 prefixEnd_405292 := by exact prefixLift 405292
  have htrace : WordTrace (prefixWord ++ tailWord_405292) baseStart_405292 baseEnd_405292 := by
    simpa [prefixWord, tailWord_405292, baseEnd_405292] using wordTrace_append hprefix tailTrace_405292
  have hstable : (prefixWord ++ tailWord_405292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405292).length < 2 ^ (prefixWord ++ tailWord_405292).sum := by decide
  have hdescent : baseEnd_405292 < baseStart_405292 := by decide
  rcases family_descends (prefixWord ++ tailWord_405292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405330 : List Nat := [3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_405330 : Nat := 118140960795 + 405330 * 2 ^ 59
def prefixEnd_405330 : Nat := 4983230072969 + 3 ^ 40 * 405330 * 2
def baseEnd_405330 : Nat := 61667885536890186136571

theorem tailTrace_405330 : CollatzResearch.WordTrace tailWord_405330 prefixEnd_405330 61667885536890186136571 := by
  unfold tailWord_405330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695899905391527424459361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9855733081044073131891629 3695899905391527424459361)
  ·
    refine ⟨2771924929043645568344521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3695899905391527424459361 2771924929043645568344521)
    ·
      refine ⟨2078943696782734176258391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2771924929043645568344521 2078943696782734176258391)
      ·
        refine ⟨3118415545174101264387587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078943696782734176258391 3118415545174101264387587)
        ·
          refine ⟨4677623317761151896581381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118415545174101264387587 4677623317761151896581381)
          ·
            refine ⟨877054372080215980609009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4677623317761151896581381 877054372080215980609009)
            ·
              refine ⟨657790779060161985456757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877054372080215980609009 657790779060161985456757)
              ·
                refine ⟨61667885536890186136571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657790779060161985456757 61667885536890186136571)
                ·
                  rfl

theorem cell20_405330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_405330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405330 prefixEnd_405330 := by exact prefixLift 405330
  have htrace : WordTrace (prefixWord ++ tailWord_405330) baseStart_405330 baseEnd_405330 := by
    simpa [prefixWord, tailWord_405330, baseEnd_405330] using wordTrace_append hprefix tailTrace_405330
  have hstable : (prefixWord ++ tailWord_405330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405330).length < 2 ^ (prefixWord ++ tailWord_405330).sum := by decide
  have hdescent : baseEnd_405330 < baseStart_405330 := by decide
  rcases family_descends (prefixWord ++ tailWord_405330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405333 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_405333 : Nat := 118140960795 + 405333 * 2 ^ 59
def prefixEnd_405333 : Nat := 4983230072969 + 3 ^ 40 * 405333 * 2
def baseEnd_405333 : Nat := 185005025892415881309701

theorem tailTrace_405333 : CollatzResearch.WordTrace tailWord_405333 prefixEnd_405333 185005025892415881309701 := by
  unfold tailWord_405333
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783709040555241210196653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9855806027036827473464435 14783709040555241210196653)
  ·
    refine ⟨5543890890208215453823745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14783709040555241210196653 5543890890208215453823745)
    ·
      refine ⟨4157918167656161590367809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5543890890208215453823745 4157918167656161590367809)
      ·
        refine ⟨3118438625742121192775857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157918167656161590367809 3118438625742121192775857)
        ·
          refine ⟨2338828969306590894581893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118438625742121192775857 2338828969306590894581893)
          ·
            refine ⟨438530431744985792734105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2338828969306590894581893 438530431744985792734105)
            ·
              refine ⟨328897823808739344550579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438530431744985792734105 328897823808739344550579)
              ·
                refine ⟨493346735713109016825869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328897823808739344550579 493346735713109016825869)
                ·
                  refine ⟨185005025892415881309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493346735713109016825869 185005025892415881309701)
                  ·
                    rfl

theorem cell20_405333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_405333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405333 prefixEnd_405333 := by exact prefixLift 405333
  have htrace : WordTrace (prefixWord ++ tailWord_405333) baseStart_405333 baseEnd_405333 := by
    simpa [prefixWord, tailWord_405333, baseEnd_405333] using wordTrace_append hprefix tailTrace_405333
  have hstable : (prefixWord ++ tailWord_405333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405333).length < 2 ^ (prefixWord ++ tailWord_405333).sum := by decide
  have hdescent : baseEnd_405333 < baseStart_405333 := by decide
  rcases family_descends (prefixWord ++ tailWord_405333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405337 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_405337 : Nat := 118140960795 + 405337 * 2 ^ 59
def prefixEnd_405337 : Nat := 4983230072969 + 3 ^ 40 * 405337 * 2
def baseEnd_405337 : Nat := 185006851601409645176351

theorem tailTrace_405337 : CollatzResearch.WordTrace tailWord_405337 prefixEnd_405337 185006851601409645176351 := by
  unfold tailWord_405337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783854932540749893342265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9855903288360499928894843 14783854932540749893342265)
  ·
    refine ⟨11087891199405562420006699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14783854932540749893342265 11087891199405562420006699)
    ·
      refine ⟨16631836799108343630010049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11087891199405562420006699 16631836799108343630010049)
      ·
        refine ⟨12473877599331257722507537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16631836799108343630010049 12473877599331257722507537)
        ·
          refine ⟨9355408199498443291880653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12473877599331257722507537 9355408199498443291880653)
          ·
            refine ⟨3508278074811916234455245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9355408199498443291880653 3508278074811916234455245)
            ·
              refine ⟨1315604278054468587920717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3508278074811916234455245 1315604278054468587920717)
              ·
                refine ⟨493351604270425720470269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315604278054468587920717 493351604270425720470269)
                ·
                  refine ⟨185006851601409645176351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493351604270425720470269 185006851601409645176351)
                  ·
                    rfl

theorem cell20_405337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_405337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405337 prefixEnd_405337 := by exact prefixLift 405337
  have htrace : WordTrace (prefixWord ++ tailWord_405337) baseStart_405337 baseEnd_405337 := by
    simpa [prefixWord, tailWord_405337, baseEnd_405337] using wordTrace_append hprefix tailTrace_405337
  have hstable : (prefixWord ++ tailWord_405337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405337).length < 2 ^ (prefixWord ++ tailWord_405337).sum := by decide
  have hdescent : baseEnd_405337 < baseStart_405337 := by decide
  rcases family_descends (prefixWord ++ tailWord_405337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405351 : List Nat := [1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_405351 : Nat := 118140960795 + 405351 * 2 ^ 59
def prefixEnd_405351 : Nat := 4983230072969 + 3 ^ 40 * 405351 * 2
def baseEnd_405351 : Nat := 61671080527629272903209

theorem tailTrace_405351 : CollatzResearch.WordTrace tailWord_405351 prefixEnd_405351 61671080527629272903209 := by
  unfold tailWord_405351
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784365554490030284351907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9856243702993353522901271 14784365554490030284351907)
  ·
    refine ⟨22176548331735045426527861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14784365554490030284351907 22176548331735045426527861)
    ·
      refine ⟨2079051406100160508736987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22176548331735045426527861 2079051406100160508736987)
      ·
        refine ⟨3118577109150240763105481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079051406100160508736987 3118577109150240763105481)
        ·
          refine ⟨2338932831862680572329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118577109150240763105481 2338932831862680572329111)
          ·
            refine ⟨3508399247794020858493667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338932831862680572329111 3508399247794020858493667)
            ·
              refine ⟨5262598871691031287740501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508399247794020858493667 5262598871691031287740501)
              ·
                refine ⟨61671080527629272903209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5262598871691031287740501 61671080527629272903209)
                ·
                  rfl

theorem cell20_405351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_405351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405351 prefixEnd_405351 := by exact prefixLift 405351
  have htrace : WordTrace (prefixWord ++ tailWord_405351) baseStart_405351 baseEnd_405351 := by
    simpa [prefixWord, tailWord_405351, baseEnd_405351] using wordTrace_append hprefix tailTrace_405351
  have hstable : (prefixWord ++ tailWord_405351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405351).length < 2 ^ (prefixWord ++ tailWord_405351).sum := by decide
  have hdescent : baseEnd_405351 < baseStart_405351 := by decide
  rcases family_descends (prefixWord ++ tailWord_405351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405361 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 2]
def baseStart_405361 : Nat := 118140960795 + 405361 * 2 ^ 59
def prefixEnd_405361 : Nat := 4983230072969 + 3 ^ 40 * 405361 * 2
def baseEnd_405361 : Nat := 185017805855372228376253

theorem tailTrace_405361 : CollatzResearch.WordTrace tailWord_405361 prefixEnd_405361 185017805855372228376253 := by
  unfold tailWord_405361
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784730284453801992215937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9856486856302534661477291 14784730284453801992215937)
  ·
    refine ⟨11088547713340351494161953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14784730284453801992215937 11088547713340351494161953)
    ·
      refine ⟨8316410785005263620621465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11088547713340351494161953 8316410785005263620621465)
      ·
        refine ⟨6237308088753947715466099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8316410785005263620621465 6237308088753947715466099)
        ·
          refine ⟨9355962133130921573199149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6237308088753947715466099 9355962133130921573199149)
          ·
            refine ⟨3508485799924095589949681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9355962133130921573199149 3508485799924095589949681)
            ·
              refine ⟨2631364349943071692462261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508485799924095589949681 2631364349943071692462261)
              ·
                refine ⟨246690407807162971168337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2631364349943071692462261 246690407807162971168337)
                ·
                  refine ⟨185017805855372228376253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246690407807162971168337 185017805855372228376253)
                  ·
                    rfl

theorem cell20_405361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_405361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405361 prefixEnd_405361 := by exact prefixLift 405361
  have htrace : WordTrace (prefixWord ++ tailWord_405361) baseStart_405361 baseEnd_405361 := by
    simpa [prefixWord, tailWord_405361, baseEnd_405361] using wordTrace_append hprefix tailTrace_405361
  have hstable : (prefixWord ++ tailWord_405361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405361).length < 2 ^ (prefixWord ++ tailWord_405361).sum := by decide
  have hdescent : baseEnd_405361 < baseStart_405361 := by decide
  rcases family_descends (prefixWord ++ tailWord_405361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405374 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_405374 : Nat := 118140960795 + 405374 * 2 ^ 59
def prefixEnd_405374 : Nat := 4983230072969 + 3 ^ 40 * 405374 * 2
def baseEnd_405374 : Nat := 185023739409601960942867

theorem tailTrace_405374 : CollatzResearch.WordTrace tailWord_405374 prefixEnd_405374 185023739409601960942867 := by
  unfold tailWord_405374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848150554175838151554897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9856802955604470141626117 1848150554175838151554897)
  ·
    refine ⟨1386112915631878613666173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1848150554175838151554897 1386112915631878613666173)
    ·
      refine ⟨519792343361954480124815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1386112915631878613666173 519792343361954480124815)
      ·
        refine ⟨779688515042931720187223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519792343361954480124815 779688515042931720187223)
        ·
          refine ⟨1169532772564397580280835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779688515042931720187223 1169532772564397580280835)
          ·
            refine ⟨1754299158846596370421253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169532772564397580280835 1754299158846596370421253)
            ·
              refine ⟨328931092283736819453985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1754299158846596370421253 328931092283736819453985)
              ·
                refine ⟨246698319212802614590489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328931092283736819453985 246698319212802614590489)
                ·
                  refine ⟨185023739409601960942867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246698319212802614590489 185023739409601960942867)
                  ·
                    rfl

theorem cell20_405374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_405374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405374 prefixEnd_405374 := by exact prefixLift 405374
  have htrace : WordTrace (prefixWord ++ tailWord_405374) baseStart_405374 baseEnd_405374 := by
    simpa [prefixWord, tailWord_405374, baseEnd_405374] using wordTrace_append hprefix tailTrace_405374
  have hstable : (prefixWord ++ tailWord_405374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405374).length < 2 ^ (prefixWord ++ tailWord_405374).sum := by decide
  have hdescent : baseEnd_405374 < baseStart_405374 := by decide
  rcases family_descends (prefixWord ++ tailWord_405374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405422 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_405422 : Nat := 118140960795 + 405422 * 2 ^ 59
def prefixEnd_405422 : Nat := 4983230072969 + 3 ^ 40 * 405422 * 2
def baseEnd_405422 : Nat := 185045647917527127342671

theorem tailTrace_405422 : CollatzResearch.WordTrace tailWord_405422 prefixEnd_405422 185045647917527127342671 := by
  unfold tailWord_405422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848369392154101176273315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9857970091488539606791013 1848369392154101176273315)
  ·
    refine ⟨2772554088231151764409973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848369392154101176273315 2772554088231151764409973)
    ·
      refine ⟨259926945771670477913435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2772554088231151764409973 259926945771670477913435)
      ·
        refine ⟨389890418657505716870153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259926945771670477913435 389890418657505716870153)
        ·
          refine ⟨292417813993129287652615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389890418657505716870153 292417813993129287652615)
          ·
            refine ⟨438626720989693931478923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292417813993129287652615 438626720989693931478923)
            ·
              refine ⟨657940081484540897218385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438626720989693931478923 657940081484540897218385)
              ·
                refine ⟨493455061113405672913789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657940081484540897218385 493455061113405672913789)
                ·
                  refine ⟨185045647917527127342671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493455061113405672913789 185045647917527127342671)
                  ·
                    rfl

theorem cell20_405422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_405422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405422 prefixEnd_405422 := by exact prefixLift 405422
  have htrace : WordTrace (prefixWord ++ tailWord_405422) baseStart_405422 baseEnd_405422 := by
    simpa [prefixWord, tailWord_405422, baseEnd_405422] using wordTrace_append hprefix tailTrace_405422
  have hstable : (prefixWord ++ tailWord_405422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405422).length < 2 ^ (prefixWord ++ tailWord_405422).sum := by decide
  have hdescent : baseEnd_405422 < baseStart_405422 := by decide
  rcases family_descends (prefixWord ++ tailWord_405422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405437 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_405437 : Nat := 118140960795 + 405437 * 2 ^ 59
def prefixEnd_405437 : Nat := 4983230072969 + 3 ^ 40 * 405437 * 2
def baseEnd_405437 : Nat := 185052494326253741842609

theorem tailTrace_405437 : CollatzResearch.WordTrace tailWord_405437 prefixEnd_405437 185052494326253741842609 := by
  unfold tailWord_405437
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787502232178466971982565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858334821452311314655043 14787502232178466971982565)
  ·
    refine ⟨2772656668533462557246731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14787502232178466971982565 2772656668533462557246731)
    ·
      refine ⟨4158985002800193835870097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772656668533462557246731 4158985002800193835870097)
      ·
        refine ⟨3119238752100145376902573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4158985002800193835870097 3119238752100145376902573)
        ·
          refine ⟨1169714532037554516338465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3119238752100145376902573 1169714532037554516338465)
          ·
            refine ⟨877285899028165887253849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169714532037554516338465 877285899028165887253849)
            ·
              refine ⟨657964424271124415440387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877285899028165887253849 657964424271124415440387)
              ·
                refine ⟨986946636406686623160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657964424271124415440387 986946636406686623160581)
                ·
                  refine ⟨185052494326253741842609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986946636406686623160581 185052494326253741842609)
                  ·
                    rfl

theorem cell20_405437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_405437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405437 prefixEnd_405437 := by exact prefixLift 405437
  have htrace : WordTrace (prefixWord ++ tailWord_405437) baseStart_405437 baseEnd_405437 := by
    simpa [prefixWord, tailWord_405437, baseEnd_405437] using wordTrace_append hprefix tailTrace_405437
  have hstable : (prefixWord ++ tailWord_405437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405437).length < 2 ^ (prefixWord ++ tailWord_405437).sum := by decide
  have hdescent : baseEnd_405437 < baseStart_405437 := by decide
  rcases family_descends (prefixWord ++ tailWord_405437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405461 : List Nat := [1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_405461 : Nat := 118140960795 + 405461 * 2 ^ 59
def prefixEnd_405461 : Nat := 4983230072969 + 3 ^ 40 * 405461 * 2
def baseEnd_405461 : Nat := 61687816193405441680837

theorem tailTrace_405461 : CollatzResearch.WordTrace tailWord_405461 prefixEnd_405461 61687816193405441680837 := by
  unfold tailWord_405461
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788377584091519070856237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858918389394346047237491 14788377584091519070856237)
  ·
    refine ⟨5545641594034319651571089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14788377584091519070856237 5545641594034319651571089)
    ·
      refine ⟨4159231195525739738678317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5545641594034319651571089 4159231195525739738678317)
      ·
        refine ⟨1559711698322152402004369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4159231195525739738678317 1559711698322152402004369)
        ·
          refine ⟨1169783773741614301503277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559711698322152402004369 1169783773741614301503277)
          ·
            refine ⟨438668915153105363063729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169783773741614301503277 438668915153105363063729)
            ·
              refine ⟨329001686364829022297797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438668915153105363063729 329001686364829022297797)
              ·
                refine ⟨61687816193405441680837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329001686364829022297797 61687816193405441680837)
                ·
                  rfl

theorem cell20_405461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_405461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405461 prefixEnd_405461 := by exact prefixLift 405461
  have htrace : WordTrace (prefixWord ++ tailWord_405461) baseStart_405461 baseEnd_405461 := by
    simpa [prefixWord, tailWord_405461, baseEnd_405461] using wordTrace_append hprefix tailTrace_405461
  have hstable : (prefixWord ++ tailWord_405461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405461).length < 2 ^ (prefixWord ++ tailWord_405461).sum := by decide
  have hdescent : baseEnd_405461 < baseStart_405461 := by decide
  rcases family_descends (prefixWord ++ tailWord_405461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405496 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_405496 : Nat := 118140960795 + 405496 * 2 ^ 59
def prefixEnd_405496 : Nat := 4983230072969 + 3 ^ 40 * 405496 * 2
def baseEnd_405496 : Nat := 185079423533911758875701

theorem tailTrace_405496 : CollatzResearch.WordTrace tailWord_405496 prefixEnd_405496 185079423533911758875701 := by
  unfold tailWord_405496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394827069482360024190171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9859769425976480032253561 7394827069482360024190171)
  ·
    refine ⟨11092240604223540036285257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7394827069482360024190171 11092240604223540036285257)
    ·
      refine ⟨8319180453167655027213943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11092240604223540036285257 8319180453167655027213943)
      ·
        refine ⟨12478770679751482540820915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319180453167655027213943 12478770679751482540820915)
        ·
          refine ⟨18718156019627223811231373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478770679751482540820915 18718156019627223811231373)
          ·
            refine ⟨7019308507360208929211765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18718156019627223811231373 7019308507360208929211765)
            ·
              refine ⟨658060172565019587113603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7019308507360208929211765 658060172565019587113603)
              ·
                refine ⟨987090258847529380670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658060172565019587113603 987090258847529380670405)
                ·
                  refine ⟨185079423533911758875701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987090258847529380670405 185079423533911758875701)
                  ·
                    rfl

theorem cell20_405496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_405496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405496 prefixEnd_405496 := by exact prefixLift 405496
  have htrace : WordTrace (prefixWord ++ tailWord_405496) baseStart_405496 baseEnd_405496 := by
    simpa [prefixWord, tailWord_405496, baseEnd_405496] using wordTrace_append hprefix tailTrace_405496
  have hstable : (prefixWord ++ tailWord_405496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405496).length < 2 ^ (prefixWord ++ tailWord_405496).sum := by decide
  have hdescent : baseEnd_405496 < baseStart_405496 := by decide
  rcases family_descends (prefixWord ++ tailWord_405496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405502 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_405502 : Nat := 118140960795 + 405502 * 2 ^ 59
def prefixEnd_405502 : Nat := 4983230072969 + 3 ^ 40 * 405502 * 2
def baseEnd_405502 : Nat := 185082162097402404675677

theorem tailTrace_405502 : CollatzResearch.WordTrace tailWord_405502 prefixEnd_405502 185082162097402404675677 := by
  unfold tailWord_405502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848734122117872884137345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9859915317961988715399173 1848734122117872884137345)
  ·
    refine ⟨1386550591588404663103009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1848734122117872884137345 1386550591588404663103009)
    ·
      refine ⟨1039912943691303497327257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386550591588404663103009 1039912943691303497327257)
      ·
        refine ⟨779934707768477622995443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039912943691303497327257 779934707768477622995443)
        ·
          refine ⟨1169902061652716434493165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779934707768477622995443 1169902061652716434493165)
          ·
            refine ⟨438713273119768662934937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169902061652716434493165 438713273119768662934937)
            ·
              refine ⟨329034954839826497201203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438713273119768662934937 329034954839826497201203)
              ·
                refine ⟨493552432259739745801805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329034954839826497201203 493552432259739745801805)
                ·
                  refine ⟨185082162097402404675677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493552432259739745801805 185082162097402404675677)
                  ·
                    rfl

theorem cell20_405502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_405502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405502 prefixEnd_405502 := by exact prefixLift 405502
  have htrace : WordTrace (prefixWord ++ tailWord_405502) baseStart_405502 baseEnd_405502 := by
    simpa [prefixWord, tailWord_405502, baseEnd_405502] using wordTrace_append hprefix tailTrace_405502
  have hstable : (prefixWord ++ tailWord_405502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405502).length < 2 ^ (prefixWord ++ tailWord_405502).sum := by decide
  have hdescent : baseEnd_405502 < baseStart_405502 := by decide
  rcases family_descends (prefixWord ++ tailWord_405502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405543 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 2]
def baseStart_405543 : Nat := 118140960795 + 405543 * 2 ^ 59
def prefixEnd_405543 : Nat := 4983230072969 + 3 ^ 40 * 405543 * 2
def baseEnd_405543 : Nat := 185100875614588484308843

theorem tailTrace_405543 : CollatzResearch.WordTrace tailWord_405543 prefixEnd_405543 185100875614588484308843 := by
  unfold tailWord_405543
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791368369794447075341283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9860912246529631383560855 14791368369794447075341283)
  ·
    refine ⟨22187052554691670613011925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14791368369794447075341283 22187052554691670613011925)
    ·
      refine ⟨520009044250586029992467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22187052554691670613011925 520009044250586029992467)
      ·
        refine ⟨780013566375879044988701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520009044250586029992467 780013566375879044988701)
        ·
          refine ⟨292505087390954641870763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 780013566375879044988701 292505087390954641870763)
          ·
            refine ⟨438757631086431962806145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292505087390954641870763 438757631086431962806145)
            ·
              refine ⟨329068223314823972104609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438757631086431962806145 329068223314823972104609)
              ·
                refine ⟨246801167486117979078457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329068223314823972104609 246801167486117979078457)
                ·
                  refine ⟨185100875614588484308843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246801167486117979078457 185100875614588484308843)
                  ·
                    rfl

theorem cell20_405543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2].length) (baseStart_405543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405543 prefixEnd_405543 := by exact prefixLift 405543
  have htrace : WordTrace (prefixWord ++ tailWord_405543) baseStart_405543 baseEnd_405543 := by
    simpa [prefixWord, tailWord_405543, baseEnd_405543] using wordTrace_append hprefix tailTrace_405543
  have hstable : (prefixWord ++ tailWord_405543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405543).length < 2 ^ (prefixWord ++ tailWord_405543).sum := by decide
  have hdescent : baseEnd_405543 < baseStart_405543 := by decide
  rcases family_descends (prefixWord ++ tailWord_405543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405565 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 3]
def baseStart_405565 : Nat := 118140960795 + 405565 * 2 ^ 59
def prefixEnd_405565 : Nat := 4983230072969 + 3 ^ 40 * 405565 * 2
def baseEnd_405565 : Nat := 185110917014054185575419

theorem tailTrace_405565 : CollatzResearch.WordTrace tailWord_405565 prefixEnd_405565 185110917014054185575419 := by
  unfold tailWord_405565
  simp only [CollatzResearch.WordTrace]
  refine ⟨14792170775714744832642149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9861447183809829888428099 14792170775714744832642149)
  ·
    refine ⟨2773532020446514656120403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14792170775714744832642149 2773532020446514656120403)
    ·
      refine ⟨4160298030669771984180605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773532020446514656120403 4160298030669771984180605)
      ·
        refine ⟨1560111761501164494067727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4160298030669771984180605 1560111761501164494067727)
        ·
          refine ⟨2340167642251746741101591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560111761501164494067727 2340167642251746741101591)
          ·
            refine ⟨3510251463377620111652387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340167642251746741101591 3510251463377620111652387)
            ·
              refine ⟨5265377195066430167478581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510251463377620111652387 5265377195066430167478581)
              ·
                refine ⟨493629112037477828201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5265377195066430167478581 493629112037477828201117)
                ·
                  refine ⟨185110917014054185575419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493629112037477828201117 185110917014054185575419)
                  ·
                    rfl

theorem cell20_405565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_405565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405565 prefixEnd_405565 := by exact prefixLift 405565
  have htrace : WordTrace (prefixWord ++ tailWord_405565) baseStart_405565 baseEnd_405565 := by
    simpa [prefixWord, tailWord_405565, baseEnd_405565] using wordTrace_append hprefix tailTrace_405565
  have hstable : (prefixWord ++ tailWord_405565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405565).length < 2 ^ (prefixWord ++ tailWord_405565).sum := by decide
  have hdescent : baseEnd_405565 < baseStart_405565 := by decide
  rcases family_descends (prefixWord ++ tailWord_405565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405589 : List Nat := [1, 3, 2, 2, 1, 3, 1, 5, 2]
def baseStart_405589 : Nat := 118140960795 + 405589 * 2 ^ 59
def prefixEnd_405589 : Nat := 4983230072969 + 3 ^ 40 * 405589 * 2
def baseEnd_405589 : Nat := 185121871268016768775321

theorem tailTrace_405589 : CollatzResearch.WordTrace tailWord_405589 prefixEnd_405589 185121871268016768775321 := by
  unfold tailWord_405589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793046127627796931515821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9862030751751864621010547 14793046127627796931515821)
  ·
    refine ⟨5547392297860423849318433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14793046127627796931515821 5547392297860423849318433)
    ·
      refine ⟨4160544223395317886988825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5547392297860423849318433 4160544223395317886988825)
      ·
        refine ⟨3120408167546488415241619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4160544223395317886988825 3120408167546488415241619)
        ·
          refine ⟨4680612251319732622862429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120408167546488415241619 4680612251319732622862429)
          ·
            refine ⟨1755229594244899733573411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4680612251319732622862429 1755229594244899733573411)
            ·
              refine ⟨2632844391367349600360117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755229594244899733573411 2632844391367349600360117)
              ·
                refine ⟨246829161690689025033761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2632844391367349600360117 246829161690689025033761)
                ·
                  refine ⟨185121871268016768775321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246829161690689025033761 185121871268016768775321)
                  ·
                    rfl

theorem cell20_405589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_405589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405589 prefixEnd_405589 := by exact prefixLift 405589
  have htrace : WordTrace (prefixWord ++ tailWord_405589) baseStart_405589 baseEnd_405589 := by
    simpa [prefixWord, tailWord_405589, baseEnd_405589] using wordTrace_append hprefix tailTrace_405589
  have hstable : (prefixWord ++ tailWord_405589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405589).length < 2 ^ (prefixWord ++ tailWord_405589).sum := by decide
  have hdescent : baseEnd_405589 < baseStart_405589 := by decide
  rcases family_descends (prefixWord ++ tailWord_405589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405593 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_405593 : Nat := 118140960795 + 405593 * 2 ^ 59
def prefixEnd_405593 : Nat := 4983230072969 + 3 ^ 40 * 405593 * 2
def baseEnd_405593 : Nat := 185123696977010532641971

theorem tailTrace_405593 : CollatzResearch.WordTrace tailWord_405593 prefixEnd_405593 185123696977010532641971 := by
  unfold tailWord_405593
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793192019613305614661433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9862128013075537076440955 14793192019613305614661433)
  ·
    refine ⟨11094894014709979210996075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14793192019613305614661433 11094894014709979210996075)
    ·
      refine ⟨16642341022064968816494113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094894014709979210996075 16642341022064968816494113)
      ·
        refine ⟨12481755766548726612370585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16642341022064968816494113 12481755766548726612370585)
        ·
          refine ⟨9361316824911544959277939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12481755766548726612370585 9361316824911544959277939)
          ·
            refine ⟨14041975237367317438916909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361316824911544959277939 14041975237367317438916909)
            ·
              refine ⟨5265740714012744039593841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14041975237367317438916909 5265740714012744039593841)
              ·
                refine ⟨3949305535509558029695381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265740714012744039593841 3949305535509558029695381)
                ·
                  refine ⟨185123696977010532641971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3949305535509558029695381 185123696977010532641971)
                  ·
                    rfl

theorem cell20_405593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_405593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405593 prefixEnd_405593 := by exact prefixLift 405593
  have htrace : WordTrace (prefixWord ++ tailWord_405593) baseStart_405593 baseEnd_405593 := by
    simpa [prefixWord, tailWord_405593, baseEnd_405593] using wordTrace_append hprefix tailTrace_405593
  have hstable : (prefixWord ++ tailWord_405593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405593).length < 2 ^ (prefixWord ++ tailWord_405593).sum := by decide
  have hdescent : baseEnd_405593 < baseStart_405593 := by decide
  rcases family_descends (prefixWord ++ tailWord_405593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405603 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_405603 : Nat := 118140960795 + 405603 * 2 ^ 59
def prefixEnd_405603 : Nat := 4983230072969 + 3 ^ 40 * 405603 * 2
def baseEnd_405603 : Nat := 185128261249494942308597

theorem tailTrace_405603 : CollatzResearch.WordTrace tailWord_405603 prefixEnd_405603 185128261249494942308597 := by
  unfold tailWord_405603
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793556749577077322525463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9862371166384718215016975 14793556749577077322525463)
  ·
    refine ⟨22190335124365615983788195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14793556749577077322525463 22190335124365615983788195)
    ·
      refine ⟨33285502686548423975682293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22190335124365615983788195 33285502686548423975682293)
      ·
        refine ⟨3120515876863914747720215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33285502686548423975682293 3120515876863914747720215)
        ·
          refine ⟨4680773815295872121580323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120515876863914747720215 4680773815295872121580323)
          ·
            refine ⟨7021160722943808182370485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680773815295872121580323 7021160722943808182370485)
            ·
              refine ⟨658233817775982017097233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7021160722943808182370485 658233817775982017097233)
              ·
                refine ⟨493675363331986512822925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658233817775982017097233 493675363331986512822925)
                ·
                  refine ⟨185128261249494942308597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493675363331986512822925 185128261249494942308597)
                  ·
                    rfl

theorem cell20_405603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_405603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405603 prefixEnd_405603 := by exact prefixLift 405603
  have htrace : WordTrace (prefixWord ++ tailWord_405603) baseStart_405603 baseEnd_405603 := by
    simpa [prefixWord, tailWord_405603, baseEnd_405603] using wordTrace_append hprefix tailTrace_405603
  have hstable : (prefixWord ++ tailWord_405603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405603).length < 2 ^ (prefixWord ++ tailWord_405603).sum := by decide
  have hdescent : baseEnd_405603 < baseStart_405603 := by decide
  rcases family_descends (prefixWord ++ tailWord_405603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405665 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_405665 : Nat := 118140960795 + 405665 * 2 ^ 59
def prefixEnd_405665 : Nat := 4983230072969 + 3 ^ 40 * 405665 * 2
def baseEnd_405665 : Nat := 185156559738898282241677

theorem tailTrace_405665 : CollatzResearch.WordTrace tailWord_405665 prefixEnd_405665 185156559738898282241677 := by
  unfold tailWord_405665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14795818075352461911282449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9863878716901641274188299 14795818075352461911282449)
  ·
    refine ⟨11096863556514346433461837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14795818075352461911282449 11096863556514346433461837)
    ·
      refine ⟨4161323833692879912548189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11096863556514346433461837 4161323833692879912548189)
      ·
        refine ⟨1560496437634829967205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4161323833692879912548189 1560496437634829967205571)
        ·
          refine ⟨2340744656452244950808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560496437634829967205571 2340744656452244950808357)
          ·
            refine ⟨438889623084795928276567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2340744656452244950808357 438889623084795928276567)
            ·
              refine ⟨658334434627193892414851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438889623084795928276567 658334434627193892414851)
              ·
                refine ⟨987501651940790838622277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658334434627193892414851 987501651940790838622277)
                ·
                  refine ⟨185156559738898282241677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987501651940790838622277 185156559738898282241677)
                  ·
                    rfl

theorem cell20_405665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_405665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405665 prefixEnd_405665 := by exact prefixLift 405665
  have htrace : WordTrace (prefixWord ++ tailWord_405665) baseStart_405665 baseEnd_405665 := by
    simpa [prefixWord, tailWord_405665, baseEnd_405665] using wordTrace_append hprefix tailTrace_405665
  have hstable : (prefixWord ++ tailWord_405665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405665).length < 2 ^ (prefixWord ++ tailWord_405665).sum := by decide
  have hdescent : baseEnd_405665 < baseStart_405665 := by decide
  rcases family_descends (prefixWord ++ tailWord_405665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405720 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_405720 : Nat := 118140960795 + 405720 * 2 ^ 59
def prefixEnd_405720 : Nat := 4983230072969 + 3 ^ 40 * 405720 * 2
def baseEnd_405720 : Nat := 185181663237562535408119

theorem tailTrace_405720 : CollatzResearch.WordTrace tailWord_405720 prefixEnd_405720 185181663237562535408119 := by
  unfold tailWord_405720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398912045076603152267307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9865216060102137536356409 7398912045076603152267307)
  ·
    refine ⟨11098368067614904728400961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398912045076603152267307 11098368067614904728400961)
    ·
      refine ⟨8323776050711178546300721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11098368067614904728400961 8323776050711178546300721)
      ·
        refine ⟨6242832038033383909725541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323776050711178546300721 6242832038033383909725541)
        ·
          refine ⟨1170531007131259483073539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6242832038033383909725541 1170531007131259483073539)
          ·
            refine ⟨1755796510696889224610309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170531007131259483073539 1755796510696889224610309)
            ·
              refine ⟨329211845755666729614433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1755796510696889224610309 329211845755666729614433)
              ·
                refine ⟨246908884316750047210825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329211845755666729614433 246908884316750047210825)
                ·
                  refine ⟨185181663237562535408119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246908884316750047210825 185181663237562535408119)
                  ·
                    rfl

theorem cell20_405720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_405720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405720 prefixEnd_405720 := by exact prefixLift 405720
  have htrace : WordTrace (prefixWord ++ tailWord_405720) baseStart_405720 baseEnd_405720 := by
    simpa [prefixWord, tailWord_405720, baseEnd_405720] using wordTrace_append hprefix tailTrace_405720
  have hstable : (prefixWord ++ tailWord_405720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405720).length < 2 ^ (prefixWord ++ tailWord_405720).sum := by decide
  have hdescent : baseEnd_405720 < baseStart_405720 := by decide
  rcases family_descends (prefixWord ++ tailWord_405720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405741 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_405741 : Nat := 118140960795 + 405741 * 2 ^ 59
def prefixEnd_405741 : Nat := 4983230072969 + 3 ^ 40 * 405741 * 2
def baseEnd_405741 : Nat := 185191248209779795708033

theorem tailTrace_405741 : CollatzResearch.WordTrace tailWord_405741 prefixEnd_405741 185191248209779795708033 := by
  unfold tailWord_405741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798590023077126891049077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9865726682051417927366051 14798590023077126891049077)
  ·
    refine ⟨1387367814663480646035851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14798590023077126891049077 1387367814663480646035851)
    ·
      refine ⟨2081051721995220969053777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387367814663480646035851 2081051721995220969053777)
      ·
        refine ⟨1560788791496415726790333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2081051721995220969053777 1560788791496415726790333)
        ·
          refine ⟨585295796811155897546375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1560788791496415726790333 585295796811155897546375)
          ·
            refine ⟨877943695216733846319563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585295796811155897546375 877943695216733846319563)
            ·
              refine ⟨1316915542825100769479345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877943695216733846319563 1316915542825100769479345)
              ·
                refine ⟨987686657118825577109509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316915542825100769479345 987686657118825577109509)
                ·
                  refine ⟨185191248209779795708033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987686657118825577109509 185191248209779795708033)
                  ·
                    rfl

theorem cell20_405741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_405741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405741 prefixEnd_405741 := by exact prefixLift 405741
  have htrace : WordTrace (prefixWord ++ tailWord_405741) baseStart_405741 baseEnd_405741 := by
    simpa [prefixWord, tailWord_405741, baseEnd_405741] using wordTrace_append hprefix tailTrace_405741
  have hstable : (prefixWord ++ tailWord_405741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405741).length < 2 ^ (prefixWord ++ tailWord_405741).sum := by decide
  have hdescent : baseEnd_405741 < baseStart_405741 := by decide
  rcases family_descends (prefixWord ++ tailWord_405741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405745 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_405745 : Nat := 118140960795 + 405745 * 2 ^ 59
def prefixEnd_405745 : Nat := 4983230072969 + 3 ^ 40 * 405745 * 2
def baseEnd_405745 : Nat := 185193073918773559574683

theorem tailTrace_405745 : CollatzResearch.WordTrace tailWord_405745 prefixEnd_405745 185193073918773559574683 := by
  unfold tailWord_405745
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798735915062635574194689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9865823943375090382796459 14798735915062635574194689)
  ·
    refine ⟨11099051936296976680646017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14798735915062635574194689 11099051936296976680646017)
    ·
      refine ⟨8324288952222732510484513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11099051936296976680646017 8324288952222732510484513)
      ·
        refine ⟨6243216714167049382863385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8324288952222732510484513 6243216714167049382863385)
        ·
          refine ⟨4682412535625287037147539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243216714167049382863385 4682412535625287037147539)
          ·
            refine ⟨7023618803437930555721309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682412535625287037147539 7023618803437930555721309)
            ·
              refine ⟨2633857051289223958395491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7023618803437930555721309 2633857051289223958395491)
              ·
                refine ⟨3950785576933835937593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633857051289223958395491 3950785576933835937593237)
                ·
                  refine ⟨185193073918773559574683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3950785576933835937593237 185193073918773559574683)
                  ·
                    rfl

theorem cell20_405745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_405745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405745 prefixEnd_405745 := by exact prefixLift 405745
  have htrace : WordTrace (prefixWord ++ tailWord_405745) baseStart_405745 baseEnd_405745 := by
    simpa [prefixWord, tailWord_405745, baseEnd_405745] using wordTrace_append hprefix tailTrace_405745
  have hstable : (prefixWord ++ tailWord_405745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405745).length < 2 ^ (prefixWord ++ tailWord_405745).sum := by decide
  have hdescent : baseEnd_405745 < baseStart_405745 := by decide
  rcases family_descends (prefixWord ++ tailWord_405745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405752 : List Nat := [2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_405752 : Nat := 118140960795 + 405752 * 2 ^ 59
def prefixEnd_405752 : Nat := 4983230072969 + 3 ^ 40 * 405752 * 2
def baseEnd_405752 : Nat := 61732089636504215447107

theorem tailTrace_405752 : CollatzResearch.WordTrace tailWord_405752 prefixEnd_405752 61732089636504215447107 := by
  unfold tailWord_405752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399495613018637884849755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9865994150691517179799673 7399495613018637884849755)
  ·
    refine ⟨11099243419527956827274633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7399495613018637884849755 11099243419527956827274633)
    ·
      refine ⟨8324432564645967620455975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11099243419527956827274633 8324432564645967620455975)
      ·
        refine ⟨12486648846968951430683963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324432564645967620455975 12486648846968951430683963)
        ·
          refine ⟨18729973270453427146025945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12486648846968951430683963 18729973270453427146025945)
          ·
            refine ⟨14047479952840070359519459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18729973270453427146025945 14047479952840070359519459)
            ·
              refine ⟨21071219929260105539279189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047479952840070359519459 21071219929260105539279189)
              ·
                refine ⟨61732089636504215447107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21071219929260105539279189 61732089636504215447107)
                ·
                  rfl

theorem cell20_405752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_405752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405752 prefixEnd_405752 := by exact prefixLift 405752
  have htrace : WordTrace (prefixWord ++ tailWord_405752) baseStart_405752 baseEnd_405752 := by
    simpa [prefixWord, tailWord_405752, baseEnd_405752] using wordTrace_append hprefix tailTrace_405752
  have hstable : (prefixWord ++ tailWord_405752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405752).length < 2 ^ (prefixWord ++ tailWord_405752).sum := by decide
  have hdescent : baseEnd_405752 < baseStart_405752 := by decide
  rcases family_descends (prefixWord ++ tailWord_405752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405758 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_405758 : Nat := 118140960795 + 405758 * 2 ^ 59
def prefixEnd_405758 : Nat := 4983230072969 + 3 ^ 40 * 405758 * 2
def baseEnd_405758 : Nat := 185199007473003292141297

theorem tailTrace_405758 : CollatzResearch.WordTrace tailWord_405758 prefixEnd_405758 185199007473003292141297 := by
  unfold tailWord_405758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849901258001942349302241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9866140042677025862945285 1849901258001942349302241)
  ·
    refine ⟨1387425943501456761976681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1849901258001942349302241 1387425943501456761976681)
    ·
      refine ⟨1040569457626092571482511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1387425943501456761976681 1040569457626092571482511)
      ·
        refine ⟨1560854186439138857223767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040569457626092571482511 1560854186439138857223767)
        ·
          refine ⟨2341281279658708285835651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560854186439138857223767 2341281279658708285835651)
          ·
            refine ⟨3511921919488062428753477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341281279658708285835651 3511921919488062428753477)
            ·
              refine ⟨658485359904011705391277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3511921919488062428753477 658485359904011705391277)
              ·
                refine ⟨246932009964004389521729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 658485359904011705391277 246932009964004389521729)
                ·
                  refine ⟨185199007473003292141297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246932009964004389521729 185199007473003292141297)
                  ·
                    rfl

theorem cell20_405758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_405758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405758 prefixEnd_405758 := by exact prefixLift 405758
  have htrace : WordTrace (prefixWord ++ tailWord_405758) baseStart_405758 baseEnd_405758 := by
    simpa [prefixWord, tailWord_405758, baseEnd_405758] using wordTrace_append hprefix tailTrace_405758
  have hstable : (prefixWord ++ tailWord_405758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405758).length < 2 ^ (prefixWord ++ tailWord_405758).sum := by decide
  have hdescent : baseEnd_405758 < baseStart_405758 := by decide
  rcases family_descends (prefixWord ++ tailWord_405758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405789 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_405789 : Nat := 118140960795 + 405789 * 2 ^ 59
def prefixEnd_405789 : Nat := 4983230072969 + 3 ^ 40 * 405789 * 2
def baseEnd_405789 : Nat := 185213156717704962107837

theorem tailTrace_405789 : CollatzResearch.WordTrace tailWord_405789 prefixEnd_405789 185213156717704962107837 := by
  unfold tailWord_405789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800340726903231088796421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9866893817935487392530947 14800340726903231088796421)
  ·
    refine ⟨2775063886294355829149329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14800340726903231088796421 2775063886294355829149329)
    ·
      refine ⟨2081297914720766871861997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2775063886294355829149329 2081297914720766871861997)
      ·
        refine ⟨780486718020287576948249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081297914720766871861997 780486718020287576948249)
        ·
          refine ⟨585365038515215682711187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780486718020287576948249 585365038515215682711187)
          ·
            refine ⟨878047557772823524066781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585365038515215682711187 878047557772823524066781)
            ·
              refine ⟨329267834164808821525043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878047557772823524066781 329267834164808821525043)
              ·
                refine ⟨493901751247213232287565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329267834164808821525043 493901751247213232287565)
                ·
                  refine ⟨185213156717704962107837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493901751247213232287565 185213156717704962107837)
                  ·
                    rfl

theorem cell20_405789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_405789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405789 prefixEnd_405789 := by exact prefixLift 405789
  have htrace : WordTrace (prefixWord ++ tailWord_405789) baseStart_405789 baseEnd_405789 := by
    simpa [prefixWord, tailWord_405789, baseEnd_405789] using wordTrace_append hprefix tailTrace_405789
  have hstable : (prefixWord ++ tailWord_405789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405789).length < 2 ^ (prefixWord ++ tailWord_405789).sum := by decide
  have hdescent : baseEnd_405789 < baseStart_405789 := by decide
  rcases family_descends (prefixWord ++ tailWord_405789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405799 : List Nat := [1, 1, 8, 1, 1, 2, 2, 4]
def baseStart_405799 : Nat := 118140960795 + 405799 * 2 ^ 59
def prefixEnd_405799 : Nat := 4983230072969 + 3 ^ 40 * 405799 * 2
def baseEnd_405799 : Nat := 61739240330063123924821

theorem tailTrace_405799 : CollatzResearch.WordTrace tailWord_405799 prefixEnd_405799 61739240330063123924821 := by
  unfold tailWord_405799
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800705456867002796660451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9867136971244668531106967 14800705456867002796660451)
  ·
    refine ⟨22201058185300504194990677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800705456867002796660451 22201058185300504194990677)
    ·
      refine ⟨260168650608990283535047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 22201058185300504194990677 260168650608990283535047)
      ·
        refine ⟨390252975913485425302571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260168650608990283535047 390252975913485425302571)
        ·
          refine ⟨585379463870228137953857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390252975913485425302571 585379463870228137953857)
          ·
            refine ⟨439034597902671103465393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585379463870228137953857 439034597902671103465393)
            ·
              refine ⟨329275948427003327599045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439034597902671103465393 329275948427003327599045)
              ·
                refine ⟨61739240330063123924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329275948427003327599045 61739240330063123924821)
                ·
                  rfl

theorem cell20_405799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 4].length) (baseStart_405799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405799 prefixEnd_405799 := by exact prefixLift 405799
  have htrace : WordTrace (prefixWord ++ tailWord_405799) baseStart_405799 baseEnd_405799 := by
    simpa [prefixWord, tailWord_405799, baseEnd_405799] using wordTrace_append hprefix tailTrace_405799
  have hstable : (prefixWord ++ tailWord_405799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405799).length < 2 ^ (prefixWord ++ tailWord_405799).sum := by decide
  have hdescent : baseEnd_405799 < baseStart_405799 := by decide
  rcases family_descends (prefixWord ++ tailWord_405799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405807 : List Nat := [1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_405807 : Nat := 118140960795 + 405807 * 2 ^ 59
def prefixEnd_405807 : Nat := 4983230072969 + 3 ^ 40 * 405807 * 2
def baseEnd_405807 : Nat := 61740457469392299835921

theorem tailTrace_405807 : CollatzResearch.WordTrace tailWord_405807 prefixEnd_405807 61740457469392299835921 := by
  unfold tailWord_405807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800997240838020162951675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9867331493892013441967783 14800997240838020162951675)
  ·
    refine ⟨22201495861257030244427513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800997240838020162951675 22201495861257030244427513)
    ·
      refine ⟨16651121895942772683320635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22201495861257030244427513 16651121895942772683320635)
      ·
        refine ⟨24976682843914159024980953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651121895942772683320635 24976682843914159024980953)
        ·
          refine ⟨18732512132935619268735715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24976682843914159024980953 18732512132935619268735715)
          ·
            refine ⟨28098768199403428903103573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732512132935619268735715 28098768199403428903103573)
            ·
              refine ⟨329282439836758932458245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 28098768199403428903103573 329282439836758932458245)
              ·
                refine ⟨61740457469392299835921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329282439836758932458245 61740457469392299835921)
                ·
                  rfl

theorem cell20_405807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_405807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405807 prefixEnd_405807 := by exact prefixLift 405807
  have htrace : WordTrace (prefixWord ++ tailWord_405807) baseStart_405807 baseEnd_405807 := by
    simpa [prefixWord, tailWord_405807, baseEnd_405807] using wordTrace_append hprefix tailTrace_405807
  have hstable : (prefixWord ++ tailWord_405807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405807).length < 2 ^ (prefixWord ++ tailWord_405807).sum := by decide
  have hdescent : baseEnd_405807 < baseStart_405807 := by decide
  rcases family_descends (prefixWord ++ tailWord_405807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405859 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_405859 : Nat := 118140960795 + 405859 * 2 ^ 59
def prefixEnd_405859 : Nat := 4983230072969 + 3 ^ 40 * 405859 * 2
def baseEnd_405859 : Nat := 185245106625095829774217

theorem tailTrace_405859 : CollatzResearch.WordTrace tailWord_405859 prefixEnd_405859 185245106625095829774217 := by
  unfold tailWord_405859
  simp only [CollatzResearch.WordTrace]
  refine ⟨14802893836649633043844631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9868595891099755362563087 14802893836649633043844631)
  ·
    refine ⟨22204340754974449565766947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14802893836649633043844631 22204340754974449565766947)
    ·
      refine ⟨33306511132461674348650421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22204340754974449565766947 33306511132461674348650421)
      ·
        refine ⟨3122485418668281970185977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33306511132461674348650421 3122485418668281970185977)
        ·
          refine ⟨2341864064001211477639483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122485418668281970185977 2341864064001211477639483)
          ·
            refine ⟨3512796096001817216459225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341864064001211477639483 3512796096001817216459225)
            ·
              refine ⟨2634597072001362912344419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512796096001817216459225 2634597072001362912344419)
              ·
                refine ⟨3951895608002044368516629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634597072001362912344419 3951895608002044368516629)
                ·
                  refine ⟨185245106625095829774217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3951895608002044368516629 185245106625095829774217)
                  ·
                    rfl

theorem cell20_405859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_405859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405859 prefixEnd_405859 := by exact prefixLift 405859
  have htrace : WordTrace (prefixWord ++ tailWord_405859) baseStart_405859 baseEnd_405859 := by
    simpa [prefixWord, tailWord_405859, baseEnd_405859] using wordTrace_append hprefix tailTrace_405859
  have hstable : (prefixWord ++ tailWord_405859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405859).length < 2 ^ (prefixWord ++ tailWord_405859).sum := by decide
  have hdescent : baseEnd_405859 < baseStart_405859 := by decide
  rcases family_descends (prefixWord ++ tailWord_405859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405889 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 2]
def baseStart_405889 : Nat := 118140960795 + 405889 * 2 ^ 59
def prefixEnd_405889 : Nat := 4983230072969 + 3 ^ 40 * 405889 * 2
def baseEnd_405889 : Nat := 185258799442549058774095

theorem tailTrace_405889 : CollatzResearch.WordTrace tailWord_405889 prefixEnd_405889 185258799442549058774095 := by
  unfold tailWord_405889
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803988026540948167436721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9869325351027298778291147 14803988026540948167436721)
  ·
    refine ⟨11102991019905711125577541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14803988026540948167436721 11102991019905711125577541)
    ·
      refine ⟨2081810816232320836045789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11102991019905711125577541 2081810816232320836045789)
      ·
        refine ⟨780679056087120313517171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081810816232320836045789 780679056087120313517171)
        ·
          refine ⟨1171018584130680470275757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780679056087120313517171 1171018584130680470275757)
          ·
            refine ⟨439131969049005176353409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1171018584130680470275757 439131969049005176353409)
            ·
              refine ⟨329348976786753882265057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439131969049005176353409 329348976786753882265057)
              ·
                refine ⟨247011732590065411698793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329348976786753882265057 247011732590065411698793)
                ·
                  refine ⟨185258799442549058774095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247011732590065411698793 185258799442549058774095)
                  ·
                    rfl

theorem cell20_405889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_405889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405889 prefixEnd_405889 := by exact prefixLift 405889
  have htrace : WordTrace (prefixWord ++ tailWord_405889) baseStart_405889 baseEnd_405889 := by
    simpa [prefixWord, tailWord_405889, baseEnd_405889] using wordTrace_append hprefix tailTrace_405889
  have hstable : (prefixWord ++ tailWord_405889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405889).length < 2 ^ (prefixWord ++ tailWord_405889).sum := by decide
  have hdescent : baseEnd_405889 < baseStart_405889 := by decide
  rcases family_descends (prefixWord ++ tailWord_405889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405914 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_405914 : Nat := 118140960795 + 405914 * 2 ^ 59
def prefixEnd_405914 : Nat := 4983230072969 + 3 ^ 40 * 405914 * 2
def baseEnd_405914 : Nat := 185270210123760082940659

theorem tailTrace_405914 : CollatzResearch.WordTrace tailWord_405914 prefixEnd_405914 185270210123760082940659 := by
  unfold tailWord_405914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701224962862594359274199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9869933234300251624731197 3701224962862594359274199)
  ·
    refine ⟨5551837444293891538911299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701224962862594359274199 5551837444293891538911299)
    ·
      refine ⟨8327756166440837308366949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551837444293891538911299 8327756166440837308366949)
      ·
        refine ⟨1561454281207656995318803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8327756166440837308366949 1561454281207656995318803)
        ·
          refine ⟨2342181421811485492978205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561454281207656995318803 2342181421811485492978205)
          ·
            refine ⟨878318033179307059866827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2342181421811485492978205 878318033179307059866827)
            ·
              refine ⟨1317477049768960589800241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878318033179307059866827 1317477049768960589800241)
              ·
                refine ⟨988107787326720442350181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317477049768960589800241 988107787326720442350181)
                ·
                  refine ⟨185270210123760082940659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 988107787326720442350181 185270210123760082940659)
                  ·
                    rfl

theorem cell20_405914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_405914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405914 prefixEnd_405914 := by exact prefixLift 405914
  have htrace : WordTrace (prefixWord ++ tailWord_405914) baseStart_405914 baseEnd_405914 := by
    simpa [prefixWord, tailWord_405914, baseEnd_405914] using wordTrace_append hprefix tailTrace_405914
  have hstable : (prefixWord ++ tailWord_405914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405914).length < 2 ^ (prefixWord ++ tailWord_405914).sum := by decide
  have hdescent : baseEnd_405914 < baseStart_405914 := by decide
  rcases family_descends (prefixWord ++ tailWord_405914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405941 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 3]
def baseStart_405941 : Nat := 118140960795 + 405941 * 2 ^ 59
def prefixEnd_405941 : Nat := 4983230072969 + 3 ^ 40 * 405941 * 2
def baseEnd_405941 : Nat := 185282533659467989040549

theorem tailTrace_405941 : CollatzResearch.WordTrace tailWord_405941 prefixEnd_405941 185282533659467989040549 := by
  unfold tailWord_405941
  simp only [CollatzResearch.WordTrace]
  refine ⟨14805884622352561048329677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9870589748235040698886451 14805884622352561048329677)
  ·
    refine ⟨5552206733382210393123629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14805884622352561048329677 5552206733382210393123629)
    ·
      refine ⟨2082077525018328897421361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5552206733382210393123629 2082077525018328897421361)
      ·
        refine ⟨1561558143763746673066021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082077525018328897421361 1561558143763746673066021)
        ·
          refine ⟨292792151955702501199879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1561558143763746673066021 292792151955702501199879)
          ·
            refine ⟨439188227933553751799819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292792151955702501199879 439188227933553751799819)
            ·
              refine ⟨658782341900330627699729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439188227933553751799819 658782341900330627699729)
              ·
                refine ⟨494086756425247970774797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658782341900330627699729 494086756425247970774797)
                ·
                  refine ⟨185282533659467989040549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494086756425247970774797 185282533659467989040549)
                  ·
                    rfl

theorem cell20_405941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_405941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405941 prefixEnd_405941 := by exact prefixLift 405941
  have htrace : WordTrace (prefixWord ++ tailWord_405941) baseStart_405941 baseEnd_405941 := by
    simpa [prefixWord, tailWord_405941, baseEnd_405941] using wordTrace_append hprefix tailTrace_405941
  have hstable : (prefixWord ++ tailWord_405941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405941).length < 2 ^ (prefixWord ++ tailWord_405941).sum := by decide
  have hdescent : baseEnd_405941 < baseStart_405941 := by decide
  rcases family_descends (prefixWord ++ tailWord_405941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405945 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_405945 : Nat := 118140960795 + 405945 * 2 ^ 59
def prefixEnd_405945 : Nat := 4983230072969 + 3 ^ 40 * 405945 * 2
def baseEnd_405945 : Nat := 185284359368461752907199

theorem tailTrace_405945 : CollatzResearch.WordTrace tailWord_405945 prefixEnd_405945 185284359368461752907199 := by
  unfold tailWord_405945
  simp only [CollatzResearch.WordTrace]
  refine ⟨14806030514338069731475289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9870687009558713154316859 14806030514338069731475289)
  ·
    refine ⟨11104522885753552298606467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14806030514338069731475289 11104522885753552298606467)
    ·
      refine ⟨16656784328630328447909701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11104522885753552298606467 16656784328630328447909701)
      ·
        refine ⟨3123147061618186583983069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16656784328630328447909701 3123147061618186583983069)
        ·
          refine ⟨1171180148106819968993651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3123147061618186583983069 1171180148106819968993651)
          ·
            refine ⟨1756770222160229953490477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171180148106819968993651 1756770222160229953490477)
            ·
              refine ⟨658788833310086232558929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1756770222160229953490477 658788833310086232558929)
              ·
                refine ⟨494091624982564674419197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658788833310086232558929 494091624982564674419197)
                ·
                  refine ⟨185284359368461752907199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494091624982564674419197 185284359368461752907199)
                  ·
                    rfl

theorem cell20_405945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_405945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405945 prefixEnd_405945 := by exact prefixLift 405945
  have htrace : WordTrace (prefixWord ++ tailWord_405945) baseStart_405945 baseEnd_405945 := by
    simpa [prefixWord, tailWord_405945, baseEnd_405945] using wordTrace_append hprefix tailTrace_405945
  have hstable : (prefixWord ++ tailWord_405945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405945).length < 2 ^ (prefixWord ++ tailWord_405945).sum := by decide
  have hdescent : baseEnd_405945 < baseStart_405945 := by decide
  rcases family_descends (prefixWord ++ tailWord_405945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405997 : List Nat := [1, 5, 1, 3, 1, 1, 8]
def baseStart_405997 : Nat := 118140960795 + 405997 * 2 ^ 59
def prefixEnd_405997 : Nat := 4983230072969 + 3 ^ 40 * 405997 * 2
def baseEnd_405997 : Nat := 20589788176153409241517

theorem tailTrace_405997 : CollatzResearch.WordTrace tailWord_405997 prefixEnd_405997 20589788176153409241517 := by
  unfold tailWord_405997
  simp only [CollatzResearch.WordTrace]
  refine ⟨14807927110149682612368245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9871951406766455074912163 14807927110149682612368245)
  ·
    refine ⟨1388243166576532744909523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14807927110149682612368245 1388243166576532744909523)
    ·
      refine ⟨2082364749864799117364285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388243166576532744909523 2082364749864799117364285)
      ·
        refine ⟨780886781199299669011607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2082364749864799117364285 780886781199299669011607)
        ·
          refine ⟨1171330171798949503517411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780886781199299669011607 1171330171798949503517411)
          ·
            refine ⟨1756995257698424255276117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171330171798949503517411 1756995257698424255276117)
            ·
              refine ⟨20589788176153409241517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1756995257698424255276117 20589788176153409241517)
              ·
                rfl

theorem cell20_405997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_405997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_405997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_405997 prefixEnd_405997 := by exact prefixLift 405997
  have htrace : WordTrace (prefixWord ++ tailWord_405997) baseStart_405997 baseEnd_405997 := by
    simpa [prefixWord, tailWord_405997, baseEnd_405997] using wordTrace_append hprefix tailTrace_405997
  have hstable : (prefixWord ++ tailWord_405997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405997).length < 2 ^ (prefixWord ++ tailWord_405997).sum := by decide
  have hdescent : baseEnd_405997 < baseStart_405997 := by decide
  rcases family_descends (prefixWord ++ tailWord_405997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406021 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_406021 : Nat := 118140960795 + 406021 * 2 ^ 59
def prefixEnd_406021 : Nat := 4983230072969 + 3 ^ 40 * 406021 * 2
def baseEnd_406021 : Nat := 185319047839343266373555

theorem tailTrace_406021 : CollatzResearch.WordTrace tailWord_406021 prefixEnd_406021 185319047839343266373555 := by
  unfold tailWord_406021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808802462062734711241917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872534974708489807494611 14808802462062734711241917)
  ·
    refine ⟨5553300923273525516715719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14808802462062734711241917 5553300923273525516715719)
    ·
      refine ⟨8329951384910288275073579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5553300923273525516715719 8329951384910288275073579)
      ·
        refine ⟨12494927077365432412610369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329951384910288275073579 12494927077365432412610369)
        ·
          refine ⟨9371195308024074309457777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12494927077365432412610369 9371195308024074309457777)
          ·
            refine ⟨7028396481018055732093333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9371195308024074309457777 7028396481018055732093333)
            ·
              refine ⟨329456085047721362441875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7028396481018055732093333 329456085047721362441875)
              ·
                refine ⟨494184127571582043662813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329456085047721362441875 494184127571582043662813)
                ·
                  refine ⟨185319047839343266373555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494184127571582043662813 185319047839343266373555)
                  ·
                    rfl

theorem cell20_406021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_406021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406021 prefixEnd_406021 := by exact prefixLift 406021
  have htrace : WordTrace (prefixWord ++ tailWord_406021) baseStart_406021 baseEnd_406021 := by
    simpa [prefixWord, tailWord_406021, baseEnd_406021] using wordTrace_append hprefix tailTrace_406021
  have hstable : (prefixWord ++ tailWord_406021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406021).length < 2 ^ (prefixWord ++ tailWord_406021).sum := by decide
  have hdescent : baseEnd_406021 < baseStart_406021 := by decide
  rcases family_descends (prefixWord ++ tailWord_406021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406025 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_406025 : Nat := 118140960795 + 406025 * 2 ^ 59
def prefixEnd_406025 : Nat := 4983230072969 + 3 ^ 40 * 406025 * 2
def baseEnd_406025 : Nat := 185320873548337030240205

theorem tailTrace_406025 : CollatzResearch.WordTrace tailWord_406025 prefixEnd_406025 185320873548337030240205 := by
  unfold tailWord_406025
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808948354048243394387529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872632236032162262925019 14808948354048243394387529)
  ·
    refine ⟨11106711265536182545790647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14808948354048243394387529 11106711265536182545790647)
    ·
      refine ⟨16660066898304273818685971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106711265536182545790647 16660066898304273818685971)
      ·
        refine ⟨24990100347456410728028957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16660066898304273818685971 24990100347456410728028957)
        ·
          refine ⟨9371287630296154023010859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24990100347456410728028957 9371287630296154023010859)
          ·
            refine ⟨14056931445444231034516289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371287630296154023010859 14056931445444231034516289)
            ·
              refine ⟨10542698584083173275887217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056931445444231034516289 10542698584083173275887217)
              ·
                refine ⟨7907023938062379956915413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10542698584083173275887217 7907023938062379956915413)
                ·
                  refine ⟨185320873548337030240205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7907023938062379956915413 185320873548337030240205)
                  ·
                    rfl

theorem cell20_406025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_406025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406025 prefixEnd_406025 := by exact prefixLift 406025
  have htrace : WordTrace (prefixWord ++ tailWord_406025) baseStart_406025 baseEnd_406025 := by
    simpa [prefixWord, tailWord_406025, baseEnd_406025] using wordTrace_append hprefix tailTrace_406025
  have hstable : (prefixWord ++ tailWord_406025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406025).length < 2 ^ (prefixWord ++ tailWord_406025).sum := by decide
  have hdescent : baseEnd_406025 < baseStart_406025 := by decide
  rcases family_descends (prefixWord ++ tailWord_406025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406052 : List Nat := [2, 3, 1, 5, 2, 7]
def baseStart_406052 : Nat := 118140960795 + 406052 * 2 ^ 59
def prefixEnd_406052 : Nat := 4983230072969 + 3 ^ 40 * 406052 * 2
def baseEnd_406052 : Nat := 6864192484594256901485

theorem tailTrace_406052 : CollatzResearch.WordTrace tailWord_406052 prefixEnd_406052 6864192484594256901485 := by
  unfold tailWord_406052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404966562475213502810205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9873288749966951337080273 7404966562475213502810205)
  ·
    refine ⟨2776862460928205063553827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7404966562475213502810205 2776862460928205063553827)
    ·
      refine ⟨4165293691392307595330741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776862460928205063553827 4165293691392307595330741)
      ·
        refine ⟨390496283568028837062257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4165293691392307595330741 390496283568028837062257)
        ·
          refine ⟨292872212676021627796693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390496283568028837062257 292872212676021627796693)
          ·
            refine ⟨6864192484594256901485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 292872212676021627796693 6864192484594256901485)
            ·
              rfl

theorem cell20_406052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 7].length) (baseStart_406052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406052 prefixEnd_406052 := by exact prefixLift 406052
  have htrace : WordTrace (prefixWord ++ tailWord_406052) baseStart_406052 baseEnd_406052 := by
    simpa [prefixWord, tailWord_406052, baseEnd_406052] using wordTrace_append hprefix tailTrace_406052
  have hstable : (prefixWord ++ tailWord_406052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406052).length < 2 ^ (prefixWord ++ tailWord_406052).sum := by decide
  have hdescent : baseEnd_406052 < baseStart_406052 := by decide
  rcases family_descends (prefixWord ++ tailWord_406052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406055 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_406055 : Nat := 118140960795 + 406055 * 2 ^ 59
def prefixEnd_406055 : Nat := 4983230072969 + 3 ^ 40 * 406055 * 2
def baseEnd_406055 : Nat := 185334566365790259240083

theorem tailTrace_406055 : CollatzResearch.WordTrace tailWord_406055 prefixEnd_406055 185334566365790259240083 := by
  unfold tailWord_406055
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810042543939558517979619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9873361695959705678653079 14810042543939558517979619)
  ·
    refine ⟨22215063815909337776969429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14810042543939558517979619 22215063815909337776969429)
    ·
      refine ⟨520665558185375104147721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22215063815909337776969429 520665558185375104147721)
      ·
        refine ⟨390499168639031328110791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520665558185375104147721 390499168639031328110791)
        ·
          refine ⟨585748752958546992166187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390499168639031328110791 585748752958546992166187)
          ·
            refine ⟨878623129437820488249281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585748752958546992166187 878623129437820488249281)
            ·
              refine ⟨658967347078365366186961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878623129437820488249281 658967347078365366186961)
              ·
                refine ⟨494225510308774024640221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658967347078365366186961 494225510308774024640221)
                ·
                  refine ⟨185334566365790259240083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494225510308774024640221 185334566365790259240083)
                  ·
                    rfl

theorem cell20_406055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_406055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406055 prefixEnd_406055 := by exact prefixLift 406055
  have htrace : WordTrace (prefixWord ++ tailWord_406055) baseStart_406055 baseEnd_406055 := by
    simpa [prefixWord, tailWord_406055, baseEnd_406055] using wordTrace_append hprefix tailTrace_406055
  have hstable : (prefixWord ++ tailWord_406055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406055).length < 2 ^ (prefixWord ++ tailWord_406055).sum := by decide
  have hdescent : baseEnd_406055 < baseStart_406055 := by decide
  rcases family_descends (prefixWord ++ tailWord_406055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406062 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_406062 : Nat := 118140960795 + 406062 * 2 ^ 59
def prefixEnd_406062 : Nat := 4983230072969 + 3 ^ 40 * 406062 * 2
def baseEnd_406062 : Nat := 185337761356529346006721

theorem tailTrace_406062 : CollatzResearch.WordTrace tailWord_406062 prefixEnd_406062 185337761356529346006721 := by
  unfold tailWord_406062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851287231864274839185555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9873531903276132475656293 1851287231864274839185555)
  ·
    refine ⟨2776930847796412258778333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851287231864274839185555 2776930847796412258778333)
    ·
      refine ⟨1041349067923654597041875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2776930847796412258778333 1041349067923654597041875)
      ·
        refine ⟨1562023601885481895562813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041349067923654597041875 1562023601885481895562813)
        ·
          refine ⟨585758850707055710836055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1562023601885481895562813 585758850707055710836055)
          ·
            refine ⟨878638276060583566254083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585758850707055710836055 878638276060583566254083)
            ·
              refine ⟨1317957414090875349381125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878638276060583566254083 1317957414090875349381125)
              ·
                refine ⟨247117015142039128008961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1317957414090875349381125 247117015142039128008961)
                ·
                  refine ⟨185337761356529346006721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247117015142039128008961 185337761356529346006721)
                  ·
                    rfl

theorem cell20_406062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_406062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406062 prefixEnd_406062 := by exact prefixLift 406062
  have htrace : WordTrace (prefixWord ++ tailWord_406062) baseStart_406062 baseEnd_406062 := by
    simpa [prefixWord, tailWord_406062, baseEnd_406062] using wordTrace_append hprefix tailTrace_406062
  have hstable : (prefixWord ++ tailWord_406062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406062).length < 2 ^ (prefixWord ++ tailWord_406062).sum := by decide
  have hdescent : baseEnd_406062 < baseStart_406062 := by decide
  rcases family_descends (prefixWord ++ tailWord_406062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406080 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_406080 : Nat := 118140960795 + 406080 * 2 ^ 59
def prefixEnd_406080 : Nat := 4983230072969 + 3 ^ 40 * 406080 * 2
def baseEnd_406080 : Nat := 185345977047001283406647

theorem tailTrace_406080 : CollatzResearch.WordTrace tailWord_406080 prefixEnd_406080 185345977047001283406647 := by
  unfold tailWord_406080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405477184424493893819847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9873969579232658525093129 7405477184424493893819847)
  ·
    refine ⟨11108215776636740840729771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405477184424493893819847 11108215776636740840729771)
    ·
      refine ⟨16662323664955111261094657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108215776636740840729771 16662323664955111261094657)
      ·
        refine ⟨12496742748716333445820993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16662323664955111261094657 12496742748716333445820993)
        ·
          refine ⟨9372557061537250084365745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12496742748716333445820993 9372557061537250084365745)
          ·
            refine ⟨7029417796152937563274309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372557061537250084365745 7029417796152937563274309)
            ·
              refine ⟨1318015836778675793113933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7029417796152937563274309 1318015836778675793113933)
              ·
                refine ⟨494255938792003422417725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318015836778675793113933 494255938792003422417725)
                ·
                  refine ⟨185345977047001283406647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494255938792003422417725 185345977047001283406647)
                  ·
                    rfl

theorem cell20_406080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_406080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406080 prefixEnd_406080 := by exact prefixLift 406080
  have htrace : WordTrace (prefixWord ++ tailWord_406080) baseStart_406080 baseEnd_406080 := by
    simpa [prefixWord, tailWord_406080, baseEnd_406080] using wordTrace_append hprefix tailTrace_406080
  have hstable : (prefixWord ++ tailWord_406080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406080).length < 2 ^ (prefixWord ++ tailWord_406080).sum := by decide
  have hdescent : baseEnd_406080 < baseStart_406080 := by decide
  rcases family_descends (prefixWord ++ tailWord_406080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406087 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_406087 : Nat := 118140960795 + 406087 * 2 ^ 59
def prefixEnd_406087 : Nat := 4983230072969 + 3 ^ 40 * 406087 * 2
def baseEnd_406087 : Nat := 185349172037740370173285

theorem tailTrace_406087 : CollatzResearch.WordTrace tailWord_406087 prefixEnd_406087 185349172037740370173285 := by
  unfold tailWord_406087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811209679823627983144515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9874139786549085322096343 14811209679823627983144515)
  ·
    refine ⟨22216814519735441974716773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14811209679823627983144515 22216814519735441974716773)
    ·
      refine ⟨4165652722450395370259395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22216814519735441974716773 4165652722450395370259395)
      ·
        refine ⟨6248479083675593055389093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165652722450395370259395 6248479083675593055389093)
        ·
          refine ⟨1171589828189173697885455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6248479083675593055389093 1171589828189173697885455)
          ·
            refine ⟨1757384742283760546828183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171589828189173697885455 1757384742283760546828183)
            ·
              refine ⟨2636077113425640820242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757384742283760546828183 2636077113425640820242275)
              ·
                refine ⟨3954115670138461230363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636077113425640820242275 3954115670138461230363413)
                ·
                  refine ⟨185349172037740370173285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3954115670138461230363413 185349172037740370173285)
                  ·
                    rfl

theorem cell20_406087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_406087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406087 prefixEnd_406087 := by exact prefixLift 406087
  have htrace : WordTrace (prefixWord ++ tailWord_406087) baseStart_406087 baseEnd_406087 := by
    simpa [prefixWord, tailWord_406087, baseEnd_406087] using wordTrace_append hprefix tailTrace_406087
  have hstable : (prefixWord ++ tailWord_406087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406087).length < 2 ^ (prefixWord ++ tailWord_406087).sum := by decide
  have hdescent : baseEnd_406087 < baseStart_406087 := by decide
  rcases family_descends (prefixWord ++ tailWord_406087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406094 : List Nat := [4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_406094 : Nat := 118140960795 + 406094 * 2 ^ 59
def prefixEnd_406094 : Nat := 4983230072969 + 3 ^ 40 * 406094 * 2
def baseEnd_406094 : Nat := 61784122342826485646641

theorem tailTrace_406094 : CollatzResearch.WordTrace tailWord_406094 prefixEnd_406094 61784122342826485646641 := by
  unfold tailWord_406094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851433123849783522331167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9874309993865512119099557 1851433123849783522331167)
  ·
    refine ⟨2777149685774675283496751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851433123849783522331167 2777149685774675283496751)
    ·
      refine ⟨4165724528662012925245127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777149685774675283496751 4165724528662012925245127)
      ·
        refine ⟨6248586792993019387867691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165724528662012925245127 6248586792993019387867691)
        ·
          refine ⟨9372880189489529081801537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248586792993019387867691 9372880189489529081801537)
          ·
            refine ⟨7029660142117146811351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372880189489529081801537 7029660142117146811351153)
            ·
              refine ⟨5272245106587860108513365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7029660142117146811351153 5272245106587860108513365)
              ·
                refine ⟨61784122342826485646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5272245106587860108513365 61784122342826485646641)
                ·
                  rfl

theorem cell20_406094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_406094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406094 prefixEnd_406094 := by exact prefixLift 406094
  have htrace : WordTrace (prefixWord ++ tailWord_406094) baseStart_406094 baseEnd_406094 := by
    simpa [prefixWord, tailWord_406094, baseEnd_406094] using wordTrace_append hprefix tailTrace_406094
  have hstable : (prefixWord ++ tailWord_406094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406094).length < 2 ^ (prefixWord ++ tailWord_406094).sum := by decide
  have hdescent : baseEnd_406094 < baseStart_406094 := by decide
  rcases family_descends (prefixWord ++ tailWord_406094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406104 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_406104 : Nat := 118140960795 + 406104 * 2 ^ 59
def prefixEnd_406104 : Nat := 4983230072969 + 3 ^ 40 * 406104 * 2
def baseEnd_406104 : Nat := 185356931300963866606549

theorem tailTrace_406104 : CollatzResearch.WordTrace tailWord_406104 prefixEnd_406104 185356931300963866606549 := by
  unfold tailWord_406104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405914860381019943256683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9874553147174693257675577 7405914860381019943256683)
  ·
    refine ⟨11108872290571529914885025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405914860381019943256683 11108872290571529914885025)
    ·
      refine ⟨8331654217928647436163769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11108872290571529914885025 8331654217928647436163769)
      ·
        refine ⟨6248740663446485577122827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8331654217928647436163769 6248740663446485577122827)
        ·
          refine ⟨9373110995169728365684241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248740663446485577122827 9373110995169728365684241)
          ·
            refine ⟨7029833246377296274263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9373110995169728365684241 7029833246377296274263181)
            ·
              refine ⟨2636187467391486102848693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7029833246377296274263181 2636187467391486102848693)
              ·
                refine ⟨247142575067951822142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2636187467391486102848693 247142575067951822142065)
                ·
                  refine ⟨185356931300963866606549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247142575067951822142065 185356931300963866606549)
                  ·
                    rfl

theorem cell20_406104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_406104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406104 prefixEnd_406104 := by exact prefixLift 406104
  have htrace : WordTrace (prefixWord ++ tailWord_406104) baseStart_406104 baseEnd_406104 := by
    simpa [prefixWord, tailWord_406104, baseEnd_406104] using wordTrace_append hprefix tailTrace_406104
  have hstable : (prefixWord ++ tailWord_406104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406104).length < 2 ^ (prefixWord ++ tailWord_406104).sum := by decide
  have hdescent : baseEnd_406104 < baseStart_406104 := by decide
  rcases family_descends (prefixWord ++ tailWord_406104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406114 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_406114 : Nat := 118140960795 + 406114 * 2 ^ 59
def prefixEnd_406114 : Nat := 4983230072969 + 3 ^ 40 * 406114 * 2
def baseEnd_406114 : Nat := 185361495573448276273175

theorem tailTrace_406114 : CollatzResearch.WordTrace tailWord_406114 prefixEnd_406114 185361495573448276273175 := by
  unfold tailWord_406114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703048612681452898594349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9874796300483874396251597 3703048612681452898594349)
  ·
    refine ⟨1388643229755544836972881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3703048612681452898594349 1388643229755544836972881)
    ·
      refine ⟨1041482422316658627729661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1388643229755544836972881 1041482422316658627729661)
      ·
        refine ⟨390555908368746985398623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041482422316658627729661 390555908368746985398623)
        ·
          refine ⟨585833862553120478097935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390555908368746985398623 585833862553120478097935)
          ·
            refine ⟨878750793829680717146903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585833862553120478097935 878750793829680717146903)
            ·
              refine ⟨1318126190744521075720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878750793829680717146903 1318126190744521075720355)
              ·
                refine ⟨1977189286116781613580533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318126190744521075720355 1977189286116781613580533)
                ·
                  refine ⟨185361495573448276273175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977189286116781613580533 185361495573448276273175)
                  ·
                    rfl

theorem cell20_406114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_406114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406114 prefixEnd_406114 := by exact prefixLift 406114
  have htrace : WordTrace (prefixWord ++ tailWord_406114) baseStart_406114 baseEnd_406114 := by
    simpa [prefixWord, tailWord_406114, baseEnd_406114] using wordTrace_append hprefix tailTrace_406114
  have hstable : (prefixWord ++ tailWord_406114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406114).length < 2 ^ (prefixWord ++ tailWord_406114).sum := by decide
  have hdescent : baseEnd_406114 < baseStart_406114 := by decide
  rcases family_descends (prefixWord ++ tailWord_406114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406149 : List Nat := [1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_406149 : Nat := 118140960795 + 406149 * 2 ^ 59
def prefixEnd_406149 : Nat := 4983230072969 + 3 ^ 40 * 406149 * 2
def baseEnd_406149 : Nat := 61792490175714570035455

theorem tailTrace_406149 : CollatzResearch.WordTrace tailWord_406149 prefixEnd_406149 61792490175714570035455 := by
  unfold tailWord_406149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14813471005599012571901501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9875647337066008381267667 14813471005599012571901501)
  ·
    refine ⟨5555051627099629714463063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14813471005599012571901501 5555051627099629714463063)
    ·
      refine ⟨8332577440649444571694595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555051627099629714463063 8332577440649444571694595)
      ·
        refine ⟨12498866160974166857541893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332577440649444571694595 12498866160974166857541893)
        ·
          refine ⟨2343537405182656285789105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12498866160974166857541893 2343537405182656285789105)
          ·
            refine ⟨1757653053886992214341829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343537405182656285789105 1757653053886992214341829)
            ·
              refine ⟨329559947603811040189093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1757653053886992214341829 329559947603811040189093)
              ·
                refine ⟨61792490175714570035455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329559947603811040189093 61792490175714570035455)
                ·
                  rfl

theorem cell20_406149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_406149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406149 prefixEnd_406149 := by exact prefixLift 406149
  have htrace : WordTrace (prefixWord ++ tailWord_406149) baseStart_406149 baseEnd_406149 := by
    simpa [prefixWord, tailWord_406149, baseEnd_406149] using wordTrace_append hprefix tailTrace_406149
  have hstable : (prefixWord ++ tailWord_406149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406149).length < 2 ^ (prefixWord ++ tailWord_406149).sum := by decide
  have hdescent : baseEnd_406149 < baseStart_406149 := by decide
  rcases family_descends (prefixWord ++ tailWord_406149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406176 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_406176 : Nat := 118140960795 + 406176 * 2 ^ 59
def prefixEnd_406176 : Nat := 4983230072969 + 3 ^ 40 * 406176 * 2
def baseEnd_406176 : Nat := 185389794062851616206255

theorem tailTrace_406176 : CollatzResearch.WordTrace tailWord_406176 prefixEnd_406176 185389794062851616206255 := by
  unfold tailWord_406176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407227888250598091567191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9876303851000797455422921 7407227888250598091567191)
  ·
    refine ⟨11110841832375897137350787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407227888250598091567191 11110841832375897137350787)
    ·
      refine ⟨16666262748563845706026181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11110841832375897137350787 16666262748563845706026181)
      ·
        refine ⟨3124924265355721069879909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16666262748563845706026181 3124924265355721069879909)
        ·
          refine ⟨585923299754197700602483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3124924265355721069879909 585923299754197700602483)
          ·
            refine ⟨878884949631296550903725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585923299754197700602483 878884949631296550903725)
            ·
              refine ⟨329581856111736206588897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878884949631296550903725 329581856111736206588897)
              ·
                refine ⟨247186392083802154941673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329581856111736206588897 247186392083802154941673)
                ·
                  refine ⟨185389794062851616206255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247186392083802154941673 185389794062851616206255)
                  ·
                    rfl

theorem cell20_406176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_406176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406176 prefixEnd_406176 := by exact prefixLift 406176
  have htrace : WordTrace (prefixWord ++ tailWord_406176) baseStart_406176 baseEnd_406176 := by
    simpa [prefixWord, tailWord_406176, baseEnd_406176] using wordTrace_append hprefix tailTrace_406176
  have hstable : (prefixWord ++ tailWord_406176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406176).length < 2 ^ (prefixWord ++ tailWord_406176).sum := by decide
  have hdescent : baseEnd_406176 < baseStart_406176 := by decide
  rcases family_descends (prefixWord ++ tailWord_406176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406186 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_406186 : Nat := 118140960795 + 406186 * 2 ^ 59
def prefixEnd_406186 : Nat := 4983230072969 + 3 ^ 40 * 406186 * 2
def baseEnd_406186 : Nat := 185394358335336025872881

theorem tailTrace_406186 : CollatzResearch.WordTrace tailWord_406186 prefixEnd_406186 185394358335336025872881 := by
  unfold tailWord_406186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703705126616241972749603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9876547004309978593998941 3703705126616241972749603)
  ·
    refine ⟨5555557689924362959124405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703705126616241972749603 5555557689924362959124405)
    ·
      refine ⟨520833533430409027417913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5555557689924362959124405 520833533430409027417913)
      ·
        refine ⟨390625150072806770563435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520833533430409027417913 390625150072806770563435)
        ·
          refine ⟨585937725109210155845153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390625150072806770563435 585937725109210155845153)
          ·
            refine ⟨439453293831907616883865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585937725109210155845153 439453293831907616883865)
            ·
              refine ⟨329589970373930712662899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439453293831907616883865 329589970373930712662899)
              ·
                refine ⟨494384955560896068994349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329589970373930712662899 494384955560896068994349)
                ·
                  refine ⟨185394358335336025872881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494384955560896068994349 185394358335336025872881)
                  ·
                    rfl

theorem cell20_406186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_406186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406186 prefixEnd_406186 := by exact prefixLift 406186
  have htrace : WordTrace (prefixWord ++ tailWord_406186) baseStart_406186 baseEnd_406186 := by
    simpa [prefixWord, tailWord_406186, baseEnd_406186] using wordTrace_append hprefix tailTrace_406186
  have hstable : (prefixWord ++ tailWord_406186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406186).length < 2 ^ (prefixWord ++ tailWord_406186).sum := by decide
  have hdescent : baseEnd_406186 < baseStart_406186 := by decide
  rcases family_descends (prefixWord ++ tailWord_406186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406190 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_406190 : Nat := 118140960795 + 406190 * 2 ^ 59
def prefixEnd_406190 : Nat := 4983230072969 + 3 ^ 40 * 406190 * 2
def baseEnd_406190 : Nat := 185396184044329789739531

theorem tailTrace_406190 : CollatzResearch.WordTrace tailWord_406190 prefixEnd_406190 185396184044329789739531 := by
  unfold tailWord_406190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851870799806309571768003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9876644265633651049429349 1851870799806309571768003)
  ·
    refine ⟨2777806199709464357652005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851870799806309571768003 2777806199709464357652005)
    ·
      refine ⟨520838662445524567059751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2777806199709464357652005 520838662445524567059751)
      ·
        refine ⟨781257993668286850589627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520838662445524567059751 781257993668286850589627)
        ·
          refine ⟨1171886990502430275884441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781257993668286850589627 1171886990502430275884441)
          ·
            refine ⟨878915242876822706913331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171886990502430275884441 878915242876822706913331)
            ·
              refine ⟨1318372864315234060369997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 878915242876822706913331 1318372864315234060369997)
              ·
                refine ⟨494389824118212772638749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1318372864315234060369997 494389824118212772638749)
                ·
                  refine ⟨185396184044329789739531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494389824118212772638749 185396184044329789739531)
                  ·
                    rfl

theorem cell20_406190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_406190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406190 prefixEnd_406190 := by exact prefixLift 406190
  have htrace : WordTrace (prefixWord ++ tailWord_406190) baseStart_406190 baseEnd_406190 := by
    simpa [prefixWord, tailWord_406190, baseEnd_406190] using wordTrace_append hprefix tailTrace_406190
  have hstable : (prefixWord ++ tailWord_406190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406190).length < 2 ^ (prefixWord ++ tailWord_406190).sum := by decide
  have hdescent : baseEnd_406190 < baseStart_406190 := by decide
  rcases family_descends (prefixWord ++ tailWord_406190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406208 : List Nat := [2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_406208 : Nat := 118140960795 + 406208 * 2 ^ 59
def prefixEnd_406208 : Nat := 4983230072969 + 3 ^ 40 * 406208 * 2
def baseEnd_406208 : Nat := 61801466578267242379819

theorem tailTrace_406208 : CollatzResearch.WordTrace tailWord_406208 prefixEnd_406208 61801466578267242379819 := by
  unfold tailWord_406208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407811456192632824149639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9877081941590177098866185 7407811456192632824149639)
  ·
    refine ⟨11111717184288949236224459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407811456192632824149639 11111717184288949236224459)
    ·
      refine ⟨16667575776433423854336689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11111717184288949236224459 16667575776433423854336689)
      ·
        refine ⟨12500681832325067890752517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16667575776433423854336689 12500681832325067890752517)
        ·
          refine ⟨2343877843560950229516097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12500681832325067890752517 2343877843560950229516097)
          ·
            refine ⟨1757908382670712672137073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343877843560950229516097 1757908382670712672137073)
            ·
              refine ⟨1318431287003034504102805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757908382670712672137073 1318431287003034504102805)
              ·
                refine ⟨61801466578267242379819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1318431287003034504102805 61801466578267242379819)
                ·
                  rfl

theorem cell20_406208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_406208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406208 prefixEnd_406208 := by exact prefixLift 406208
  have htrace : WordTrace (prefixWord ++ tailWord_406208) baseStart_406208 baseEnd_406208 := by
    simpa [prefixWord, tailWord_406208, baseEnd_406208] using wordTrace_append hprefix tailTrace_406208
  have hstable : (prefixWord ++ tailWord_406208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406208).length < 2 ^ (prefixWord ++ tailWord_406208).sum := by decide
  have hdescent : baseEnd_406208 < baseStart_406208 := by decide
  rcases family_descends (prefixWord ++ tailWord_406208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406215 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_406215 : Nat := 118140960795 + 406215 * 2 ^ 59
def prefixEnd_406215 : Nat := 4983230072969 + 3 ^ 40 * 406215 * 2
def baseEnd_406215 : Nat := 185407594725540813906095

theorem tailTrace_406215 : CollatzResearch.WordTrace tailWord_406215 prefixEnd_406215 185407594725540813906095 := by
  unfold tailWord_406215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815878223359905843804099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9877252148906603895869399 14815878223359905843804099)
  ·
    refine ⟨22223817335039858765706149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14815878223359905843804099 22223817335039858765706149)
    ·
      refine ⟨4166965750319973518569903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22223817335039858765706149 4166965750319973518569903)
      ·
        refine ⟨6250448625479960277854855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166965750319973518569903 6250448625479960277854855)
        ·
          refine ⟨9375672938219940416782283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250448625479960277854855 9375672938219940416782283)
          ·
            refine ⟨14063509407329910625173425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375672938219940416782283 14063509407329910625173425)
            ·
              refine ⟨10547632055497432968880069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14063509407329910625173425 10547632055497432968880069)
              ·
                refine ⟨1977681010405768681665013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10547632055497432968880069 1977681010405768681665013)
                ·
                  refine ⟨185407594725540813906095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977681010405768681665013 185407594725540813906095)
                  ·
                    rfl

theorem cell20_406215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_406215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406215 prefixEnd_406215 := by exact prefixLift 406215
  have htrace : WordTrace (prefixWord ++ tailWord_406215) baseStart_406215 baseEnd_406215 := by
    simpa [prefixWord, tailWord_406215, baseEnd_406215] using wordTrace_append hprefix tailTrace_406215
  have hstable : (prefixWord ++ tailWord_406215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406215).length < 2 ^ (prefixWord ++ tailWord_406215).sum := by decide
  have hdescent : baseEnd_406215 < baseStart_406215 := by decide
  rcases family_descends (prefixWord ++ tailWord_406215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406228 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_406228 : Nat := 118140960795 + 406228 * 2 ^ 59
def prefixEnd_406228 : Nat := 4983230072969 + 3 ^ 40 * 406228 * 2
def baseEnd_406228 : Nat := 185413528279770546472709

theorem tailTrace_406228 : CollatzResearch.WordTrace tailWord_406228 prefixEnd_406228 185413528279770546472709 := by
  unfold tailWord_406228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408176186156404532013669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9877568248208539376018225 7408176186156404532013669)
  ·
    refine ⟨1389033034904325849752563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7408176186156404532013669 1389033034904325849752563)
    ·
      refine ⟨2083549552356488774628845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389033034904325849752563 2083549552356488774628845)
      ·
        refine ⟨781331082133683290485817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2083549552356488774628845 781331082133683290485817)
        ·
          refine ⟨585998311600262467864363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781331082133683290485817 585998311600262467864363)
          ·
            refine ⟨878997467400393701796545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585998311600262467864363 878997467400393701796545)
            ·
              refine ⟨659248100550295276347409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878997467400393701796545 659248100550295276347409)
              ·
                refine ⟨494436075412721457260557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659248100550295276347409 494436075412721457260557)
                ·
                  refine ⟨185413528279770546472709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494436075412721457260557 185413528279770546472709)
                  ·
                    rfl

theorem cell20_406228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_406228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406228 prefixEnd_406228 := by exact prefixLift 406228
  have htrace : WordTrace (prefixWord ++ tailWord_406228) baseStart_406228 baseEnd_406228 := by
    simpa [prefixWord, tailWord_406228, baseEnd_406228] using wordTrace_append hprefix tailTrace_406228
  have hstable : (prefixWord ++ tailWord_406228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406228).length < 2 ^ (prefixWord ++ tailWord_406228).sum := by decide
  have hdescent : baseEnd_406228 < baseStart_406228 := by decide
  rcases family_descends (prefixWord ++ tailWord_406228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406232 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_406232 : Nat := 118140960795 + 406232 * 2 ^ 59
def prefixEnd_406232 : Nat := 4983230072969 + 3 ^ 40 * 406232 * 2
def baseEnd_406232 : Nat := 185415353988764310339359

theorem tailTrace_406232 : CollatzResearch.WordTrace tailWord_406232 prefixEnd_406232 185415353988764310339359 := by
  unfold tailWord_406232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408249132149158873586475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9877665509532211831448633 7408249132149158873586475)
  ·
    refine ⟨11112373698223738310379713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7408249132149158873586475 11112373698223738310379713)
    ·
      refine ⟨8334280273667803732784785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11112373698223738310379713 8334280273667803732784785)
      ·
        refine ⟨6250710205250852799588589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8334280273667803732784785 6250710205250852799588589)
        ·
          refine ⟨2344016326969069799845721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6250710205250852799588589 2344016326969069799845721)
          ·
            refine ⟨1758012245226802349884291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344016326969069799845721 1758012245226802349884291)
            ·
              refine ⟨2637018367840203524826437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758012245226802349884291 2637018367840203524826437)
              ·
                refine ⟨494440943970038160904957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2637018367840203524826437 494440943970038160904957)
                ·
                  refine ⟨185415353988764310339359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494440943970038160904957 185415353988764310339359)
                  ·
                    rfl

theorem cell20_406232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_406232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406232 prefixEnd_406232 := by exact prefixLift 406232
  have htrace : WordTrace (prefixWord ++ tailWord_406232) baseStart_406232 baseEnd_406232 := by
    simpa [prefixWord, tailWord_406232, baseEnd_406232] using wordTrace_append hprefix tailTrace_406232
  have hstable : (prefixWord ++ tailWord_406232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406232).length < 2 ^ (prefixWord ++ tailWord_406232).sum := by decide
  have hdescent : baseEnd_406232 < baseStart_406232 := by decide
  rcases family_descends (prefixWord ++ tailWord_406232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406291 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_406291 : Nat := 118140960795 + 406291 * 2 ^ 59
def prefixEnd_406291 : Nat := 4983230072969 + 3 ^ 40 * 406291 * 2
def baseEnd_406291 : Nat := 185442283196422327372451

theorem tailTrace_406291 : CollatzResearch.WordTrace tailWord_406291 prefixEnd_406291 185442283196422327372451 := by
  unfold tailWord_406291
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818650171084570823570727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9879100114056380549047151 14818650171084570823570727)
  ·
    refine ⟨22227975256626856235356091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14818650171084570823570727 22227975256626856235356091)
    ·
      refine ⟨33341962884940284353034137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22227975256626856235356091 33341962884940284353034137)
      ·
        refine ⟨25006472163705213264775603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33341962884940284353034137 25006472163705213264775603)
        ·
          refine ⟨37509708245557819897163405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25006472163705213264775603 37509708245557819897163405)
          ·
            refine ⟨14066140592084182461436277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37509708245557819897163405 14066140592084182461436277)
            ·
              refine ⟨1318700680507892105759651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14066140592084182461436277 1318700680507892105759651)
              ·
                refine ⟨1978051020761838158639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318700680507892105759651 1978051020761838158639477)
                ·
                  refine ⟨185442283196422327372451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978051020761838158639477 185442283196422327372451)
                  ·
                    rfl

theorem cell20_406291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_406291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406291 prefixEnd_406291 := by exact prefixLift 406291
  have htrace : WordTrace (prefixWord ++ tailWord_406291) baseStart_406291 baseEnd_406291 := by
    simpa [prefixWord, tailWord_406291, baseEnd_406291] using wordTrace_append hprefix tailTrace_406291
  have hstable : (prefixWord ++ tailWord_406291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406291).length < 2 ^ (prefixWord ++ tailWord_406291).sum := by decide
  have hdescent : baseEnd_406291 < baseStart_406291 := by decide
  rcases family_descends (prefixWord ++ tailWord_406291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406314 : List Nat := [3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_406314 : Nat := 118140960795 + 406314 * 2 ^ 59
def prefixEnd_406314 : Nat := 4983230072969 + 3 ^ 40 * 406314 * 2
def baseEnd_406314 : Nat := 61817593674378823201897

theorem tailTrace_406314 : CollatzResearch.WordTrace tailWord_406314 prefixEnd_406314 61817593674378823201897 := by
  unfold tailWord_406314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704872262500311437914499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9879659366667497167771997 3704872262500311437914499)
  ·
    refine ⟨5557308393750467156871749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3704872262500311437914499 5557308393750467156871749)
    ·
      refine ⟨1041995323828212591913453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5557308393750467156871749 1041995323828212591913453)
      ·
        refine ⟨390748246435579721967545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041995323828212591913453 390748246435579721967545)
        ·
          refine ⟨293061184826684791475659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390748246435579721967545 293061184826684791475659)
          ·
            refine ⟨439591777240027187213489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293061184826684791475659 439591777240027187213489)
            ·
              refine ⟨329693832930020390410117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439591777240027187213489 329693832930020390410117)
              ·
                refine ⟨61817593674378823201897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329693832930020390410117 61817593674378823201897)
                ·
                  rfl

theorem cell20_406314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_406314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406314 prefixEnd_406314 := by exact prefixLift 406314
  have htrace : WordTrace (prefixWord ++ tailWord_406314) baseStart_406314 baseEnd_406314 := by
    simpa [prefixWord, tailWord_406314, baseEnd_406314] using wordTrace_append hprefix tailTrace_406314
  have hstable : (prefixWord ++ tailWord_406314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406314).length < 2 ^ (prefixWord ++ tailWord_406314).sum := by decide
  have hdescent : baseEnd_406314 < baseStart_406314 := by decide
  rcases family_descends (prefixWord ++ tailWord_406314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406318 : List Nat := [4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_406318 : Nat := 118140960795 + 406318 * 2 ^ 59
def prefixEnd_406318 : Nat := 4983230072969 + 3 ^ 40 * 406318 * 2
def baseEnd_406318 : Nat := 61818202244043411157447

theorem tailTrace_406318 : CollatzResearch.WordTrace tailWord_406318 prefixEnd_406318 61818202244043411157447 := by
  unfold tailWord_406318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1852454367748344304350451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9879756627991169623202405 1852454367748344304350451)
  ·
    refine ⟨2778681551622516456525677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1852454367748344304350451 2778681551622516456525677)
    ·
      refine ⟨1042005581858443671197129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2778681551622516456525677 1042005581858443671197129)
      ·
        refine ⟨781504186393832753397847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1042005581858443671197129 781504186393832753397847)
        ·
          refine ⟨1172256279590749130096771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781504186393832753397847 1172256279590749130096771)
          ·
            refine ⟨1758384419386123695145157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172256279590749130096771 1758384419386123695145157)
            ·
              refine ⟨329697078634898192839717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1758384419386123695145157 329697078634898192839717)
              ·
                refine ⟨61818202244043411157447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329697078634898192839717 61818202244043411157447)
                ·
                  rfl

theorem cell20_406318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_406318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406318 prefixEnd_406318 := by exact prefixLift 406318
  have htrace : WordTrace (prefixWord ++ tailWord_406318) baseStart_406318 baseEnd_406318 := by
    simpa [prefixWord, tailWord_406318, baseEnd_406318] using wordTrace_append hprefix tailTrace_406318
  have hstable : (prefixWord ++ tailWord_406318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406318).length < 2 ^ (prefixWord ++ tailWord_406318).sum := by decide
  have hdescent : baseEnd_406318 < baseStart_406318 := by decide
  rcases family_descends (prefixWord ++ tailWord_406318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406322 : List Nat := [3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_406322 : Nat := 118140960795 + 406322 * 2 ^ 59
def prefixEnd_406322 : Nat := 4983230072969 + 3 ^ 40 * 406322 * 2
def baseEnd_406322 : Nat := 61818810813707999112997

theorem tailTrace_406322 : CollatzResearch.WordTrace tailWord_406322 prefixEnd_406322 61818810813707999112997 := by
  unfold tailWord_406322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704945208493065779487305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9879853889314842078632813 3704945208493065779487305)
  ·
    refine ⟨2778708906369799334615479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3704945208493065779487305 2778708906369799334615479)
    ·
      refine ⟨4168063359554699001923219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778708906369799334615479 4168063359554699001923219)
      ·
        refine ⟨6252095039332048502884829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168063359554699001923219 6252095039332048502884829)
        ·
          refine ⟨2344535639749518188581811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6252095039332048502884829 2344535639749518188581811)
          ·
            refine ⟨3516803459624277282872717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344535639749518188581811 3516803459624277282872717)
            ·
              refine ⟨1318801297359103981077269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516803459624277282872717 1318801297359103981077269)
              ·
                refine ⟨61818810813707999112997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1318801297359103981077269 61818810813707999112997)
                ·
                  rfl

theorem cell20_406322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_406322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406322 prefixEnd_406322 := by exact prefixLift 406322
  have htrace : WordTrace (prefixWord ++ tailWord_406322) baseStart_406322 baseEnd_406322 := by
    simpa [prefixWord, tailWord_406322, baseEnd_406322] using wordTrace_append hprefix tailTrace_406322
  have hstable : (prefixWord ++ tailWord_406322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406322).length < 2 ^ (prefixWord ++ tailWord_406322).sum := by decide
  have hdescent : baseEnd_406322 < baseStart_406322 := by decide
  rcases family_descends (prefixWord ++ tailWord_406322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406336 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_406336 : Nat := 118140960795 + 406336 * 2 ^ 59
def prefixEnd_406336 : Nat := 4983230072969 + 3 ^ 40 * 406336 * 2
def baseEnd_406336 : Nat := 185462822422602170872267

theorem tailTrace_406336 : CollatzResearch.WordTrace tailWord_406336 prefixEnd_406336 185462822422602170872267 := by
  unfold tailWord_406336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410145727960771754479431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9880194303947695672639241 7410145727960771754479431)
  ·
    refine ⟨11115218591941157631719147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7410145727960771754479431 11115218591941157631719147)
    ·
      refine ⟨16672827887911736447578721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115218591941157631719147 16672827887911736447578721)
      ·
        refine ⟨12504620915933802335684041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16672827887911736447578721 12504620915933802335684041)
        ·
          refine ⟨9378465686950351751763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12504620915933802335684041 9378465686950351751763031)
          ·
            refine ⟨14067698530425527627644547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378465686950351751763031 14067698530425527627644547)
            ·
              refine ⟨21101547795638291441466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14067698530425527627644547 21101547795638291441466821)
              ·
                refine ⟨3956540211682179645275029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21101547795638291441466821 3956540211682179645275029)
                ·
                  refine ⟨185462822422602170872267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3956540211682179645275029 185462822422602170872267)
                  ·
                    rfl

theorem cell20_406336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_406336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406336 prefixEnd_406336 := by exact prefixLift 406336
  have htrace : WordTrace (prefixWord ++ tailWord_406336) baseStart_406336 baseEnd_406336 := by
    simpa [prefixWord, tailWord_406336, baseEnd_406336] using wordTrace_append hprefix tailTrace_406336
  have hstable : (prefixWord ++ tailWord_406336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406336).length < 2 ^ (prefixWord ++ tailWord_406336).sum := by decide
  have hdescent : baseEnd_406336 < baseStart_406336 := by decide
  rcases family_descends (prefixWord ++ tailWord_406336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406419 : List Nat := [1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_406419 : Nat := 118140960795 + 406419 * 2 ^ 59
def prefixEnd_406419 : Nat := 4983230072969 + 3 ^ 40 * 406419 * 2
def baseEnd_406419 : Nat := 61833568628074257035087

theorem tailTrace_406419 : CollatzResearch.WordTrace tailWord_406419 prefixEnd_406419 61833568628074257035087 := by
  unfold tailWord_406419
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823318714620848684230311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9882212476413899122820207 14823318714620848684230311)
  ·
    refine ⟨22234978071931273026345467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14823318714620848684230311 22234978071931273026345467)
    ·
      refine ⟨33352467107896909539518201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234978071931273026345467 33352467107896909539518201)
      ·
        refine ⟨25014350330922682154638651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33352467107896909539518201 25014350330922682154638651)
        ·
          refine ⟨37521525496384023231957977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25014350330922682154638651 37521525496384023231957977)
          ·
            refine ⟨28141144122288017423968483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37521525496384023231957977 28141144122288017423968483)
            ·
              refine ⟨42211716183432026135952725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28141144122288017423968483 42211716183432026135952725)
              ·
                refine ⟨61833568628074257035087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 42211716183432026135952725 61833568628074257035087)
                ·
                  rfl

theorem cell20_406419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_406419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406419 prefixEnd_406419 := by exact prefixLift 406419
  have htrace : WordTrace (prefixWord ++ tailWord_406419) baseStart_406419 baseEnd_406419 := by
    simpa [prefixWord, tailWord_406419, baseEnd_406419] using wordTrace_append hprefix tailTrace_406419
  have hstable : (prefixWord ++ tailWord_406419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406419).length < 2 ^ (prefixWord ++ tailWord_406419).sum := by decide
  have hdescent : baseEnd_406419 < baseStart_406419 := by decide
  rcases family_descends (prefixWord ++ tailWord_406419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406429 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_406429 : Nat := 118140960795 + 406429 * 2 ^ 59
def prefixEnd_406429 : Nat := 4983230072969 + 3 ^ 40 * 406429 * 2
def baseEnd_406429 : Nat := 185505270156707180771887

theorem tailTrace_406429 : CollatzResearch.WordTrace tailWord_406429 prefixEnd_406429 185505270156707180771887 := by
  unfold tailWord_406429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823683444584620392094341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9882455629723080261396227 14823683444584620392094341)
  ·
    refine ⟨2779440645859616323517689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14823683444584620392094341 2779440645859616323517689)
    ·
      refine ⟨2084580484394712242638267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2779440645859616323517689 2084580484394712242638267)
      ·
        refine ⟨3126870726592068363957401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084580484394712242638267 3126870726592068363957401)
        ·
          refine ⟨2345153044944051272968051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3126870726592068363957401 2345153044944051272968051)
          ·
            refine ⟨3517729567416076909452077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345153044944051272968051 3517729567416076909452077)
            ·
              refine ⟨1319148587781028841044529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3517729567416076909452077 1319148587781028841044529)
              ·
                refine ⟨989361440835771630783397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319148587781028841044529 989361440835771630783397)
                ·
                  refine ⟨185505270156707180771887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989361440835771630783397 185505270156707180771887)
                  ·
                    rfl

theorem cell20_406429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_406429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406429 prefixEnd_406429 := by exact prefixLift 406429
  have htrace : WordTrace (prefixWord ++ tailWord_406429) baseStart_406429 baseEnd_406429 := by
    simpa [prefixWord, tailWord_406429, baseEnd_406429] using wordTrace_append hprefix tailTrace_406429
  have hstable : (prefixWord ++ tailWord_406429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406429).length < 2 ^ (prefixWord ++ tailWord_406429).sum := by decide
  have hdescent : baseEnd_406429 < baseStart_406429 := by decide
  rcases family_descends (prefixWord ++ tailWord_406429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406518 : List Nat := [5, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_406518 : Nat := 118140960795 + 406518 * 2 ^ 59
def prefixEnd_406518 : Nat := 4983230072969 + 3 ^ 40 * 406518 * 2
def baseEnd_406518 : Nat := 185545892181818426804857

theorem tailTrace_406518 : CollatzResearch.WordTrace tailWord_406518 prefixEnd_406518 185545892181818426804857 := by
  unfold tailWord_406518
  simp only [CollatzResearch.WordTrace]
  refine ⟨926683096328886787005263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9884619694174792394722805 926683096328886787005263)
  ·
    refine ⟨1390024644493330180507895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926683096328886787005263 1390024644493330180507895)
    ·
      refine ⟨2085036966739995270761843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390024644493330180507895 2085036966739995270761843)
      ·
        refine ⟨3127555450109992906142765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085036966739995270761843 3127555450109992906142765)
        ·
          refine ⟨1172833293791247339803537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3127555450109992906142765 1172833293791247339803537)
          ·
            refine ⟨879624970343435504852653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172833293791247339803537 879624970343435504852653)
            ·
              refine ⟨329859363878788314319745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879624970343435504852653 329859363878788314319745)
              ·
                refine ⟨247394522909091235739809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329859363878788314319745 247394522909091235739809)
                ·
                  refine ⟨185545892181818426804857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247394522909091235739809 185545892181818426804857)
                  ·
                    rfl

theorem cell20_406518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_406518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406518 prefixEnd_406518 := by exact prefixLift 406518
  have htrace : WordTrace (prefixWord ++ tailWord_406518) baseStart_406518 baseEnd_406518 := by
    simpa [prefixWord, tailWord_406518, baseEnd_406518] using wordTrace_append hprefix tailTrace_406518
  have hstable : (prefixWord ++ tailWord_406518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406518).length < 2 ^ (prefixWord ++ tailWord_406518).sum := by decide
  have hdescent : baseEnd_406518 < baseStart_406518 := by decide
  rcases family_descends (prefixWord ++ tailWord_406518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406536 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_406536 : Nat := 118140960795 + 406536 * 2 ^ 59
def prefixEnd_406536 : Nat := 4983230072969 + 3 ^ 40 * 406536 * 2
def baseEnd_406536 : Nat := 185554107872290364204783

theorem tailTrace_406536 : CollatzResearch.WordTrace tailWord_406536 prefixEnd_406536 185554107872290364204783 := by
  unfold tailWord_406536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413793027598488833119731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9885057370131318444159641 7413793027598488833119731)
  ·
    refine ⟨11120689541397733249679597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7413793027598488833119731 11120689541397733249679597)
    ·
      refine ⟨4170258578024149968629849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11120689541397733249679597 4170258578024149968629849)
      ·
        refine ⟨3127693933518112476472387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4170258578024149968629849 3127693933518112476472387)
        ·
          refine ⟨4691540900277168714708581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127693933518112476472387 4691540900277168714708581)
          ·
            refine ⟨879663918801969134007859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4691540900277168714708581 879663918801969134007859)
            ·
              refine ⟨1319495878202953701011789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879663918801969134007859 1319495878202953701011789)
              ·
                refine ⟨494810954326107637879421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319495878202953701011789 494810954326107637879421)
                ·
                  refine ⟨185554107872290364204783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494810954326107637879421 185554107872290364204783)
                  ·
                    rfl

theorem cell20_406536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_406536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406536 prefixEnd_406536 := by exact prefixLift 406536
  have htrace : WordTrace (prefixWord ++ tailWord_406536) baseStart_406536 baseEnd_406536 := by
    simpa [prefixWord, tailWord_406536, baseEnd_406536] using wordTrace_append hprefix tailTrace_406536
  have hstable : (prefixWord ++ tailWord_406536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406536).length < 2 ^ (prefixWord ++ tailWord_406536).sum := by decide
  have hdescent : baseEnd_406536 < baseStart_406536 := by decide
  rcases family_descends (prefixWord ++ tailWord_406536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406588 : List Nat := [2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_406588 : Nat := 118140960795 + 406588 * 2 ^ 59
def prefixEnd_406588 : Nat := 4983230072969 + 3 ^ 40 * 406588 * 2
def baseEnd_406588 : Nat := 61859280696403098157079

theorem tailTrace_406588 : CollatzResearch.WordTrace tailWord_406588 prefixEnd_406588 61859280696403098157079 := by
  unfold tailWord_406588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414741325504295273566209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9886321767339060364754945 7414741325504295273566209)
  ·
    refine ⟨5561055994128221455174657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7414741325504295273566209 5561055994128221455174657)
    ·
      refine ⟨4170791995596166091380993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561055994128221455174657 4170791995596166091380993)
      ·
        refine ⟨3128093996697124568535745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4170791995596166091380993 3128093996697124568535745)
        ·
          refine ⟨2346070497522843426401809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128093996697124568535745 2346070497522843426401809)
          ·
            refine ⟨1759552873142132569801357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346070497522843426401809 1759552873142132569801357)
            ·
              refine ⟨659832327428299713675509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759552873142132569801357 659832327428299713675509)
              ·
                refine ⟨61859280696403098157079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659832327428299713675509 61859280696403098157079)
                ·
                  rfl

theorem cell20_406588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_406588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406588 prefixEnd_406588 := by exact prefixLift 406588
  have htrace : WordTrace (prefixWord ++ tailWord_406588) baseStart_406588 baseEnd_406588 := by
    simpa [prefixWord, tailWord_406588, baseEnd_406588] using wordTrace_append hprefix tailTrace_406588
  have hstable : (prefixWord ++ tailWord_406588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406588).length < 2 ^ (prefixWord ++ tailWord_406588).sum := by decide
  have hdescent : baseEnd_406588 < baseStart_406588 := by decide
  rcases family_descends (prefixWord ++ tailWord_406588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406595 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_406595 : Nat := 118140960795 + 406595 * 2 ^ 59
def prefixEnd_406595 : Nat := 4983230072969 + 3 ^ 40 * 406595 * 2
def baseEnd_406595 : Nat := 185581037079948381237875

theorem tailTrace_406595 : CollatzResearch.WordTrace tailWord_406595 prefixEnd_406595 185581037079948381237875 := by
  unfold tailWord_406595
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829737961983230742637239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886491974655487161758159 14829737961983230742637239)
  ·
    refine ⟨22244606942974846113955859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14829737961983230742637239 22244606942974846113955859)
    ·
      refine ⟨33366910414462269170933789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22244606942974846113955859 33366910414462269170933789)
      ·
        refine ⟨12512591405423350939100171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33366910414462269170933789 12512591405423350939100171)
        ·
          refine ⟨18768887108135026408650257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12512591405423350939100171 18768887108135026408650257)
          ·
            refine ⟨14076665331101269806487693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18768887108135026408650257 14076665331101269806487693)
            ·
              refine ⟨5278749499162976177432885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14076665331101269806487693 5278749499162976177432885)
              ·
                refine ⟨494882765546529016634333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5278749499162976177432885 494882765546529016634333)
                ·
                  refine ⟨185581037079948381237875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494882765546529016634333 185581037079948381237875)
                  ·
                    rfl

theorem cell20_406595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_406595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406595 prefixEnd_406595 := by exact prefixLift 406595
  have htrace : WordTrace (prefixWord ++ tailWord_406595) baseStart_406595 baseEnd_406595 := by
    simpa [prefixWord, tailWord_406595, baseEnd_406595] using wordTrace_append hprefix tailTrace_406595
  have hstable : (prefixWord ++ tailWord_406595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406595).length < 2 ^ (prefixWord ++ tailWord_406595).sum := by decide
  have hdescent : baseEnd_406595 < baseStart_406595 := by decide
  rcases family_descends (prefixWord ++ tailWord_406595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406598 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_406598 : Nat := 118140960795 + 406598 * 2 ^ 59
def prefixEnd_406598 : Nat := 4983230072969 + 3 ^ 40 * 406598 * 2
def baseEnd_406598 : Nat := 185582406361693704137863

theorem tailTrace_406598 : CollatzResearch.WordTrace tailWord_406598 prefixEnd_406598 185582406361693704137863 := by
  unfold tailWord_406598
  simp only [CollatzResearch.WordTrace]
  refine ⟨463432730655386320468639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9886564920648241503330965 463432730655386320468639)
  ·
    refine ⟨695149095983079480702959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463432730655386320468639 695149095983079480702959)
    ·
      refine ⟨1042723643974619221054439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695149095983079480702959 1042723643974619221054439)
      ·
        refine ⟨1564085465961928831581659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042723643974619221054439 1564085465961928831581659)
        ·
          refine ⟨2346128198942893247372489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564085465961928831581659 2346128198942893247372489)
          ·
            refine ⟨1759596149207169935529367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346128198942893247372489 1759596149207169935529367)
            ·
              refine ⟨2639394223810754903294051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759596149207169935529367 2639394223810754903294051)
              ·
                refine ⟨3959091335716132354941077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639394223810754903294051 3959091335716132354941077)
                ·
                  refine ⟨185582406361693704137863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3959091335716132354941077 185582406361693704137863)
                  ·
                    rfl

theorem cell20_406598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_406598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406598 prefixEnd_406598 := by exact prefixLift 406598
  have htrace : WordTrace (prefixWord ++ tailWord_406598) baseStart_406598 baseEnd_406598 := by
    simpa [prefixWord, tailWord_406598, baseEnd_406598] using wordTrace_append hprefix tailTrace_406598
  have hstable : (prefixWord ++ tailWord_406598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406598).length < 2 ^ (prefixWord ++ tailWord_406598).sum := by decide
  have hdescent : baseEnd_406598 < baseStart_406598 := by decide
  rcases family_descends (prefixWord ++ tailWord_406598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406602 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_406602 : Nat := 118140960795 + 406602 * 2 ^ 59
def prefixEnd_406602 : Nat := 4983230072969 + 3 ^ 40 * 406602 * 2
def baseEnd_406602 : Nat := 185584232070687468004513

theorem tailTrace_406602 : CollatzResearch.WordTrace tailWord_406602 prefixEnd_406602 185584232070687468004513 := by
  unfold tailWord_406602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707498318239467734535515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9886662181971913958761373 3707498318239467734535515)
  ·
    refine ⟨5561247477359201601803273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707498318239467734535515 5561247477359201601803273)
    ·
      refine ⟨4170935608019401201352455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561247477359201601803273 4170935608019401201352455)
      ·
        refine ⟨6256403412029101802028683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170935608019401201352455 6256403412029101802028683)
        ·
          refine ⟨9384605118043652703043025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256403412029101802028683 9384605118043652703043025)
          ·
            refine ⟨7038453838532739527282269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384605118043652703043025 7038453838532739527282269)
            ·
              refine ⟨2639420189449777322730851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038453838532739527282269 2639420189449777322730851)
              ·
                refine ⟨3959130284174665984096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639420189449777322730851 3959130284174665984096277)
                ·
                  refine ⟨185584232070687468004513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3959130284174665984096277 185584232070687468004513)
                  ·
                    rfl

theorem cell20_406602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_406602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406602 prefixEnd_406602 := by exact prefixLift 406602
  have htrace : WordTrace (prefixWord ++ tailWord_406602) baseStart_406602 baseEnd_406602 := by
    simpa [prefixWord, tailWord_406602, baseEnd_406602] using wordTrace_append hprefix tailTrace_406602
  have hstable : (prefixWord ++ tailWord_406602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406602).length < 2 ^ (prefixWord ++ tailWord_406602).sum := by decide
  have hdescent : baseEnd_406602 < baseStart_406602 := by decide
  rcases family_descends (prefixWord ++ tailWord_406602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406609 : List Nat := [1, 2, 2, 1, 3, 1, 2, 8]
def baseStart_406609 : Nat := 118140960795 + 406609 * 2 ^ 59
def prefixEnd_406609 : Nat := 4983230072969 + 3 ^ 40 * 406609 * 2
def baseEnd_406609 : Nat := 61862475687142184923717

theorem tailTrace_406609 : CollatzResearch.WordTrace tailWord_406609 prefixEnd_406609 61862475687142184923717 := by
  unfold tailWord_406609
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830248583932511133646881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886832389288340755764587 14830248583932511133646881)
  ·
    refine ⟨11122686437949383350235161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14830248583932511133646881 11122686437949383350235161)
    ·
      refine ⟨8342014828462037512676371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11122686437949383350235161 8342014828462037512676371)
      ·
        refine ⟨12513022242693056269014557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8342014828462037512676371 12513022242693056269014557)
        ·
          refine ⟨4692383341009896100880459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12513022242693056269014557 4692383341009896100880459)
          ·
            refine ⟨7038575011514844151320689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692383341009896100880459 7038575011514844151320689)
            ·
              refine ⟨5278931258636133113490517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038575011514844151320689 5278931258636133113490517)
              ·
                refine ⟨61862475687142184923717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5278931258636133113490517 61862475687142184923717)
                ·
                  rfl

theorem cell20_406609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_406609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406609 prefixEnd_406609 := by exact prefixLift 406609
  have htrace : WordTrace (prefixWord ++ tailWord_406609) baseStart_406609 baseEnd_406609 := by
    simpa [prefixWord, tailWord_406609, baseEnd_406609] using wordTrace_append hprefix tailTrace_406609
  have hstable : (prefixWord ++ tailWord_406609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406609).length < 2 ^ (prefixWord ++ tailWord_406609).sum := by decide
  have hdescent : baseEnd_406609 < baseStart_406609 := by decide
  rcases family_descends (prefixWord ++ tailWord_406609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406622 : List Nat := [4, 4, 1, 1, 1, 2, 7]
def baseStart_406622 : Nat := 118140960795 + 406622 * 2 ^ 59
def prefixEnd_406622 : Nat := 4983230072969 + 3 ^ 40 * 406622 * 2
def baseEnd_406622 : Nat := 20621484512850698593085

theorem tailTrace_406622 : CollatzResearch.WordTrace tailWord_406622 prefixEnd_406622 20621484512850698593085 := by
  unfold tailWord_406622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853840341610676794233765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9887148488590276235913413 1853840341610676794233765)
  ·
    refine ⟨347595064052001898918831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1853840341610676794233765 347595064052001898918831)
    ·
      refine ⟨521392596078002848378247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347595064052001898918831 521392596078002848378247)
      ·
        refine ⟨782088894117004272567371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521392596078002848378247 782088894117004272567371)
        ·
          refine ⟨1173133341175506408851057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782088894117004272567371 1173133341175506408851057)
          ·
            refine ⟨879850005881629806638293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173133341175506408851057 879850005881629806638293)
            ·
              refine ⟨20621484512850698593085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 879850005881629806638293 20621484512850698593085)
              ·
                rfl

theorem cell20_406622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_406622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406622 prefixEnd_406622 := by exact prefixLift 406622
  have htrace : WordTrace (prefixWord ++ tailWord_406622) baseStart_406622 baseEnd_406622 := by
    simpa [prefixWord, tailWord_406622, baseEnd_406622] using wordTrace_append hprefix tailTrace_406622
  have hstable : (prefixWord ++ tailWord_406622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406622).length < 2 ^ (prefixWord ++ tailWord_406622).sum := by decide
  have hdescent : baseEnd_406622 < baseStart_406622 := by decide
  rcases family_descends (prefixWord ++ tailWord_406622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406633 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_406633 : Nat := 118140960795 + 406633 * 2 ^ 59
def prefixEnd_406633 : Nat := 4983230072969 + 3 ^ 40 * 406633 * 2
def baseEnd_406633 : Nat := 185598381315389137971053

theorem tailTrace_406633 : CollatzResearch.WordTrace tailWord_406633 prefixEnd_406633 185598381315389137971053 := by
  unfold tailWord_406633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831123935845563232520553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887415957230375488347035 14831123935845563232520553)
  ·
    refine ⟨11123342951884172424390415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14831123935845563232520553 11123342951884172424390415)
    ·
      refine ⟨16685014427826258636585623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123342951884172424390415 16685014427826258636585623)
      ·
        refine ⟨25027521641739387954878435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16685014427826258636585623 25027521641739387954878435)
        ·
          refine ⟨37541282462609081932317653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027521641739387954878435 37541282462609081932317653)
          ·
            refine ⟨879873807717400357788695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37541282462609081932317653 879873807717400357788695)
            ·
              refine ⟨1319810711576100536683043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879873807717400357788695 1319810711576100536683043)
              ·
                refine ⟨1979716067364150805024565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319810711576100536683043 1979716067364150805024565)
                ·
                  refine ⟨185598381315389137971053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1979716067364150805024565 185598381315389137971053)
                  ·
                    rfl

theorem cell20_406633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_406633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406633 prefixEnd_406633 := by exact prefixLift 406633
  have htrace : WordTrace (prefixWord ++ tailWord_406633) baseStart_406633 baseEnd_406633 := by
    simpa [prefixWord, tailWord_406633, baseEnd_406633] using wordTrace_append hprefix tailTrace_406633
  have hstable : (prefixWord ++ tailWord_406633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406633).length < 2 ^ (prefixWord ++ tailWord_406633).sum := by decide
  have hdescent : baseEnd_406633 < baseStart_406633 := by decide
  rcases family_descends (prefixWord ++ tailWord_406633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406647 : List Nat := [1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_406647 : Nat := 118140960795 + 406647 * 2 ^ 59
def prefixEnd_406647 : Nat := 4983230072969 + 3 ^ 40 * 406647 * 2
def baseEnd_406647 : Nat := 61868257098955770501443

theorem tailTrace_406647 : CollatzResearch.WordTrace tailWord_406647 prefixEnd_406647 61868257098955770501443 := by
  unfold tailWord_406647
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831634557794843623530195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887756371863229082353463 14831634557794843623530195)
  ·
    refine ⟨22247451836692265435295293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14831634557794843623530195 22247451836692265435295293)
    ·
      refine ⟨8342794438759599538235735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22247451836692265435295293 8342794438759599538235735)
      ·
        refine ⟨12514191658139399307353603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8342794438759599538235735 12514191658139399307353603)
        ·
          refine ⟨18771287487209098961030405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12514191658139399307353603 18771287487209098961030405)
          ·
            refine ⟨3519616403851706055193201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18771287487209098961030405 3519616403851706055193201)
            ·
              refine ⟨2639712302888779541394901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519616403851706055193201 2639712302888779541394901)
              ·
                refine ⟨61868257098955770501443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2639712302888779541394901 61868257098955770501443)
                ·
                  rfl

theorem cell20_406647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_406647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406647 prefixEnd_406647 := by exact prefixLift 406647
  have htrace : WordTrace (prefixWord ++ tailWord_406647) baseStart_406647 baseEnd_406647 := by
    simpa [prefixWord, tailWord_406647, baseEnd_406647] using wordTrace_append hprefix tailTrace_406647
  have hstable : (prefixWord ++ tailWord_406647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406647).length < 2 ^ (prefixWord ++ tailWord_406647).sum := by decide
  have hdescent : baseEnd_406647 < baseStart_406647 := by decide
  rcases family_descends (prefixWord ++ tailWord_406647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406657 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_406657 : Nat := 118140960795 + 406657 * 2 ^ 59
def prefixEnd_406657 : Nat := 4983230072969 + 3 ^ 40 * 406657 * 2
def baseEnd_406657 : Nat := 185609335569351721170955

theorem tailTrace_406657 : CollatzResearch.WordTrace tailWord_406657 prefixEnd_406657 185609335569351721170955 := by
  unfold tailWord_406657
  simp only [CollatzResearch.WordTrace]
  refine ⟨14831999287758615331394225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887999525172410220929483 14831999287758615331394225)
  ·
    refine ⟨11123999465818961498545669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14831999287758615331394225 11123999465818961498545669)
    ·
      refine ⟨2085749899841055280977313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11123999465818961498545669 2085749899841055280977313)
      ·
        refine ⟨1564312424880791460732985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085749899841055280977313 1564312424880791460732985)
        ·
          refine ⟨1173234318660593595549739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564312424880791460732985 1173234318660593595549739)
          ·
            refine ⟨1759851477990890393324609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173234318660593595549739 1759851477990890393324609)
            ·
              refine ⟨1319888608493167794993457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759851477990890393324609 1319888608493167794993457)
              ·
                refine ⟨989916456369875846245093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319888608493167794993457 989916456369875846245093)
                ·
                  refine ⟨185609335569351721170955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989916456369875846245093 185609335569351721170955)
                  ·
                    rfl

theorem cell20_406657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_406657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406657 prefixEnd_406657 := by exact prefixLift 406657
  have htrace : WordTrace (prefixWord ++ tailWord_406657) baseStart_406657 baseEnd_406657 := by
    simpa [prefixWord, tailWord_406657, baseEnd_406657] using wordTrace_append hprefix tailTrace_406657
  have hstable : (prefixWord ++ tailWord_406657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406657).length < 2 ^ (prefixWord ++ tailWord_406657).sum := by decide
  have hdescent : baseEnd_406657 < baseStart_406657 := by decide
  rcases family_descends (prefixWord ++ tailWord_406657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406701 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 3]
def baseStart_406701 : Nat := 118140960795 + 406701 * 2 ^ 59
def prefixEnd_406701 : Nat := 4983230072969 + 3 ^ 40 * 406701 * 2
def baseEnd_406701 : Nat := 185629418368283123704109

theorem tailTrace_406701 : CollatzResearch.WordTrace tailWord_406701 prefixEnd_406701 185629418368283123704109 := by
  unfold tailWord_406701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833604099599210845995957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9889069399732807230663971 14833604099599210845995957)
  ·
    refine ⟨1390650384337426016812121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14833604099599210845995957 1390650384337426016812121)
    ·
      refine ⟨1042987788253069512609091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1390650384337426016812121 1042987788253069512609091)
      ·
        refine ⟨1564481682379604268913637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042987788253069512609091 1564481682379604268913637)
        ·
          refine ⟨293340315446175800421307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1564481682379604268913637 293340315446175800421307)
          ·
            refine ⟨440010473169263700631961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293340315446175800421307 440010473169263700631961)
            ·
              refine ⟨330007854876947775473971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440010473169263700631961 330007854876947775473971)
              ·
                refine ⟨495011782315421663210957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330007854876947775473971 495011782315421663210957)
                ·
                  refine ⟨185629418368283123704109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495011782315421663210957 185629418368283123704109)
                  ·
                    rfl

theorem cell20_406701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_406701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406701 prefixEnd_406701 := by exact prefixLift 406701
  have htrace : WordTrace (prefixWord ++ tailWord_406701) baseStart_406701 baseEnd_406701 := by
    simpa [prefixWord, tailWord_406701, baseEnd_406701] using wordTrace_append hprefix tailTrace_406701
  have hstable : (prefixWord ++ tailWord_406701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406701).length < 2 ^ (prefixWord ++ tailWord_406701).sum := by decide
  have hdescent : baseEnd_406701 < baseStart_406701 := by decide
  rcases family_descends (prefixWord ++ tailWord_406701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406705 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_406705 : Nat := 118140960795 + 406705 * 2 ^ 59
def prefixEnd_406705 : Nat := 4983230072969 + 3 ^ 40 * 406705 * 2
def baseEnd_406705 : Nat := 185631244077276887570759

theorem tailTrace_406705 : CollatzResearch.WordTrace tailWord_406705 prefixEnd_406705 185631244077276887570759 := by
  unfold tailWord_406705
  simp only [CollatzResearch.WordTrace]
  refine ⟨14833749991584719529141569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9889166661056479686094379 14833749991584719529141569)
  ·
    refine ⟨11125312493688539646856177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14833749991584719529141569 11125312493688539646856177)
    ·
      refine ⟨8343984370266404735142133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11125312493688539646856177 8343984370266404735142133)
      ·
        refine ⟨782248534712475443919575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8343984370266404735142133 782248534712475443919575)
        ·
          refine ⟨1173372802068713165879363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782248534712475443919575 1173372802068713165879363)
          ·
            refine ⟨1760059203103069748819045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173372802068713165879363 1760059203103069748819045)
            ·
              refine ⟨330011100581825577903571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1760059203103069748819045 330011100581825577903571)
              ·
                refine ⟨495016650872738366855357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330011100581825577903571 495016650872738366855357)
                ·
                  refine ⟨185631244077276887570759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495016650872738366855357 185631244077276887570759)
                  ·
                    rfl

theorem cell20_406705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_406705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406705 prefixEnd_406705 := by exact prefixLift 406705
  have htrace : WordTrace (prefixWord ++ tailWord_406705) baseStart_406705 baseEnd_406705 := by
    simpa [prefixWord, tailWord_406705, baseEnd_406705] using wordTrace_append hprefix tailTrace_406705
  have hstable : (prefixWord ++ tailWord_406705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406705).length < 2 ^ (prefixWord ++ tailWord_406705).sum := by decide
  have hdescent : baseEnd_406705 < baseStart_406705 := by decide
  rcases family_descends (prefixWord ++ tailWord_406705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406740 : List Nat := [2, 4, 1, 4, 9]
def baseStart_406740 : Nat := 118140960795 + 406740 * 2 ^ 59
def prefixEnd_406740 : Nat := 4983230072969 + 3 ^ 40 * 406740 * 2
def baseEnd_406740 : Nat := 2291940975691016313629

theorem tailTrace_406740 : CollatzResearch.WordTrace tailWord_406740 prefixEnd_406740 2291940975691016313629 := by
  unfold tailWord_406740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417513273228960253332837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9890017697638613671110449 7417513273228960253332837)
  ·
    refine ⟨1390783738730430047499907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7417513273228960253332837 1390783738730430047499907)
    ·
      refine ⟨2086175608095645071249861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390783738730430047499907 2086175608095645071249861)
      ·
        refine ⟨391157926517933450859349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2086175608095645071249861 391157926517933450859349)
        ·
          refine ⟨2291940975691016313629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 391157926517933450859349 2291940975691016313629)
          ·
            rfl

theorem cell20_406740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 9].length) (baseStart_406740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406740 prefixEnd_406740 := by exact prefixLift 406740
  have htrace : WordTrace (prefixWord ++ tailWord_406740) baseStart_406740 baseEnd_406740 := by
    simpa [prefixWord, tailWord_406740, baseEnd_406740] using wordTrace_append hprefix tailTrace_406740
  have hstable : (prefixWord ++ tailWord_406740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406740).length < 2 ^ (prefixWord ++ tailWord_406740).sum := by decide
  have hdescent : baseEnd_406740 < baseStart_406740 := by decide
  rcases family_descends (prefixWord ++ tailWord_406740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406742 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_406742 : Nat := 118140960795 + 406742 * 2 ^ 59
def prefixEnd_406742 : Nat := 4983230072969 + 3 ^ 40 * 406742 * 2
def baseEnd_406742 : Nat := 185648131885469203337275

theorem tailTrace_406742 : CollatzResearch.WordTrace tailWord_406742 prefixEnd_406742 185648131885469203337275 := by
  unfold tailWord_406742
  simp only [CollatzResearch.WordTrace]
  refine ⟨927193718278167178014905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9890066328300449898825653 927193718278167178014905)
  ·
    refine ⟨695395288708625383511179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 927193718278167178014905 695395288708625383511179)
    ·
      refine ⟨1043092933062938075266769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695395288708625383511179 1043092933062938075266769)
      ·
        refine ⟨782319699797203556450077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043092933062938075266769 782319699797203556450077)
        ·
          refine ⟨293369887423951333668779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 782319699797203556450077 293369887423951333668779)
          ·
            refine ⟨440054831135927000503169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293369887423951333668779 440054831135927000503169)
            ·
              refine ⟨330041123351945250377377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440054831135927000503169 330041123351945250377377)
              ·
                refine ⟨247530842513958937783033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330041123351945250377377 247530842513958937783033)
                ·
                  refine ⟨185648131885469203337275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247530842513958937783033 185648131885469203337275)
                  ·
                    rfl

theorem cell20_406742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_406742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406742 prefixEnd_406742 := by exact prefixLift 406742
  have htrace : WordTrace (prefixWord ++ tailWord_406742) baseStart_406742 baseEnd_406742 := by
    simpa [prefixWord, tailWord_406742, baseEnd_406742] using wordTrace_append hprefix tailTrace_406742
  have hstable : (prefixWord ++ tailWord_406742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406742).length < 2 ^ (prefixWord ++ tailWord_406742).sum := by decide
  have hdescent : baseEnd_406742 < baseStart_406742 := by decide
  rcases family_descends (prefixWord ++ tailWord_406742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406757 : List Nat := [1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_406757 : Nat := 118140960795 + 406757 * 2 ^ 59
def prefixEnd_406757 : Nat := 4983230072969 + 3 ^ 40 * 406757 * 2
def baseEnd_406757 : Nat := 61884992764731939279071

theorem tailTrace_406757 : CollatzResearch.WordTrace tailWord_406757 prefixEnd_406757 61884992764731939279071 := by
  unfold tailWord_406757
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835646587396332410034525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9890431058264221606689683 14835646587396332410034525)
  ·
    refine ⟨5563367470273624653762947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14835646587396332410034525 5563367470273624653762947)
    ·
      refine ⟨8345051205410436980644421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563367470273624653762947 8345051205410436980644421)
      ·
        refine ⟨1564697101014456933870829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8345051205410436980644421 1564697101014456933870829)
        ·
          refine ⟨586761412880421350201561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1564697101014456933870829 586761412880421350201561)
          ·
            refine ⟨440071059660316012651171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586761412880421350201561 440071059660316012651171)
            ·
              refine ⟨660106589490474018976757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440071059660316012651171 660106589490474018976757)
              ·
                refine ⟨61884992764731939279071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660106589490474018976757 61884992764731939279071)
                ·
                  rfl

theorem cell20_406757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_406757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406757 prefixEnd_406757 := by exact prefixLift 406757
  have htrace : WordTrace (prefixWord ++ tailWord_406757) baseStart_406757 baseEnd_406757 := by
    simpa [prefixWord, tailWord_406757, baseEnd_406757] using wordTrace_append hprefix tailTrace_406757
  have hstable : (prefixWord ++ tailWord_406757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406757).length < 2 ^ (prefixWord ++ tailWord_406757).sum := by decide
  have hdescent : baseEnd_406757 < baseStart_406757 := by decide
  rcases family_descends (prefixWord ++ tailWord_406757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406768 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_406768 : Nat := 118140960795 + 406768 * 2 ^ 59
def prefixEnd_406768 : Nat := 4983230072969 + 3 ^ 40 * 406768 * 2
def baseEnd_406768 : Nat := 185659998993928668470501

theorem tailTrace_406768 : CollatzResearch.WordTrace tailWord_406768 prefixEnd_406768 185659998993928668470501 := by
  unfold tailWord_406768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7418023895178240644342479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9890698526904320859123305 7418023895178240644342479)
  ·
    refine ⟨11127035842767360966513719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7418023895178240644342479 11127035842767360966513719)
    ·
      refine ⟨16690553764151041449770579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127035842767360966513719 16690553764151041449770579)
      ·
        refine ⟨25035830646226562174655869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16690553764151041449770579 25035830646226562174655869)
        ·
          refine ⟨9388436492334960815495951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25035830646226562174655869 9388436492334960815495951)
          ·
            refine ⟨14082654738502441223243927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388436492334960815495951 14082654738502441223243927)
            ·
              refine ⟨21123982107753661834865891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082654738502441223243927 21123982107753661834865891)
              ·
                refine ⟨31685973161630492752298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21123982107753661834865891 31685973161630492752298837)
                ·
                  refine ⟨185659998993928668470501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31685973161630492752298837 185659998993928668470501)
                  ·
                    rfl

theorem cell20_406768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_406768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406768 prefixEnd_406768 := by exact prefixLift 406768
  have htrace : WordTrace (prefixWord ++ tailWord_406768) baseStart_406768 baseEnd_406768 := by
    simpa [prefixWord, tailWord_406768, baseEnd_406768] using wordTrace_append hprefix tailTrace_406768
  have hstable : (prefixWord ++ tailWord_406768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406768).length < 2 ^ (prefixWord ++ tailWord_406768).sum := by decide
  have hdescent : baseEnd_406768 < baseStart_406768 := by decide
  rcases family_descends (prefixWord ++ tailWord_406768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406778 : List Nat := [3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_406778 : Nat := 118140960795 + 406778 * 2 ^ 59
def prefixEnd_406778 : Nat := 4983230072969 + 3 ^ 40 * 406778 * 2
def baseEnd_406778 : Nat := 61888187755471026045709

theorem tailTrace_406778 : CollatzResearch.WordTrace tailWord_406778 prefixEnd_406778 61888187755471026045709 := by
  unfold tailWord_406778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709103130080063249137247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9890941680213501997699325 3709103130080063249137247)
  ·
    refine ⟨5563654695120094873705871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709103130080063249137247 5563654695120094873705871)
    ·
      refine ⟨8345482042680142310558807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563654695120094873705871 8345482042680142310558807)
      ·
        refine ⟨12518223064020213465838211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345482042680142310558807 12518223064020213465838211)
        ·
          refine ⟨18777334596030320198757317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518223064020213465838211 18777334596030320198757317)
          ·
            refine ⟨3520750236755685037266997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18777334596030320198757317 3520750236755685037266997)
            ·
              refine ⟨330070334695845472243781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3520750236755685037266997 330070334695845472243781)
              ·
                refine ⟨61888187755471026045709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330070334695845472243781 61888187755471026045709)
                ·
                  rfl

theorem cell20_406778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_406778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406778 prefixEnd_406778 := by exact prefixLift 406778
  have htrace : WordTrace (prefixWord ++ tailWord_406778) baseStart_406778 baseEnd_406778 := by
    simpa [prefixWord, tailWord_406778, baseEnd_406778] using wordTrace_append hprefix tailTrace_406778
  have hstable : (prefixWord ++ tailWord_406778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406778).length < 2 ^ (prefixWord ++ tailWord_406778).sum := by decide
  have hdescent : baseEnd_406778 < baseStart_406778 := by decide
  rcases family_descends (prefixWord ++ tailWord_406778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406788 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_406788 : Nat := 118140960795 + 406788 * 2 ^ 59
def prefixEnd_406788 : Nat := 4983230072969 + 3 ^ 40 * 406788 * 2
def baseEnd_406788 : Nat := 185669127538897487803753

theorem tailTrace_406788 : CollatzResearch.WordTrace tailWord_406788 prefixEnd_406788 185669127538897487803753 := by
  unfold tailWord_406788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7418388625142012352206509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9891184833522683136275345 7418388625142012352206509)
  ·
    refine ⟨2781895734428254632077441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7418388625142012352206509 2781895734428254632077441)
    ·
      refine ⟨2086421800821190974058081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2781895734428254632077441 2086421800821190974058081)
      ·
        refine ⟨1564816350615893230543561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2086421800821190974058081 1564816350615893230543561)
        ·
          refine ⟨1173612262961919922907671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564816350615893230543561 1173612262961919922907671)
          ·
            refine ⟨1760418394442879884361507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173612262961919922907671 1760418394442879884361507)
            ·
              refine ⟨2640627591664319826542261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760418394442879884361507 2640627591664319826542261)
              ·
                refine ⟨247558836718529983738337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2640627591664319826542261 247558836718529983738337)
                ·
                  refine ⟨185669127538897487803753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247558836718529983738337 185669127538897487803753)
                  ·
                    rfl

theorem cell20_406788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_406788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406788 prefixEnd_406788 := by exact prefixLift 406788
  have htrace : WordTrace (prefixWord ++ tailWord_406788) baseStart_406788 baseEnd_406788 := by
    simpa [prefixWord, tailWord_406788, baseEnd_406788] using wordTrace_append hprefix tailTrace_406788
  have hstable : (prefixWord ++ tailWord_406788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406788).length < 2 ^ (prefixWord ++ tailWord_406788).sum := by decide
  have hdescent : baseEnd_406788 < baseStart_406788 := by decide
  rcases family_descends (prefixWord ++ tailWord_406788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406833 : List Nat := [1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_406833 : Nat := 118140960795 + 406833 * 2 ^ 59
def prefixEnd_406833 : Nat := 4983230072969 + 3 ^ 40 * 406833 * 2
def baseEnd_406833 : Nat := 61896555588359110434523

theorem tailTrace_406833 : CollatzResearch.WordTrace tailWord_406833 prefixEnd_406833 61896555588359110434523 := by
  unfold tailWord_406833
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838418535120997389801153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892279023413998259867435 14838418535120997389801153)
  ·
    refine ⟨11128813901340748042350865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14838418535120997389801153 11128813901340748042350865)
    ·
      refine ⟨8346610426005561031763149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11128813901340748042350865 8346610426005561031763149)
      ·
        refine ⟨3129978909752085386911181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8346610426005561031763149 3129978909752085386911181)
        ·
          refine ⟨1173742091157032020091693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3129978909752085386911181 1173742091157032020091693)
          ·
            refine ⟨440153284183887007534385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173742091157032020091693 440153284183887007534385)
            ·
              refine ⟨330114963137915255650789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440153284183887007534385 330114963137915255650789)
              ·
                refine ⟨61896555588359110434523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330114963137915255650789 61896555588359110434523)
                ·
                  rfl

theorem cell20_406833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_406833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406833 prefixEnd_406833 := by exact prefixLift 406833
  have htrace : WordTrace (prefixWord ++ tailWord_406833) baseStart_406833 baseEnd_406833 := by
    simpa [prefixWord, tailWord_406833, baseEnd_406833] using wordTrace_append hprefix tailTrace_406833
  have hstable : (prefixWord ++ tailWord_406833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406833).length < 2 ^ (prefixWord ++ tailWord_406833).sum := by decide
  have hdescent : baseEnd_406833 < baseStart_406833 := by decide
  rcases family_descends (prefixWord ++ tailWord_406833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406864 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_406864 : Nat := 118140960795 + 406864 * 2 ^ 59
def prefixEnd_406864 : Nat := 4983230072969 + 3 ^ 40 * 406864 * 2
def baseEnd_406864 : Nat := 185703816009779001270109

theorem tailTrace_406864 : CollatzResearch.WordTrace tailWord_406864 prefixEnd_406864 185703816009779001270109 := by
  unfold tailWord_406864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419774599004344842089823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9893032798672459789453097 7419774599004344842089823)
  ·
    refine ⟨11129661898506517263134735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7419774599004344842089823 11129661898506517263134735)
    ·
      refine ⟨16694492847759775894702103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129661898506517263134735 16694492847759775894702103)
      ·
        refine ⟨25041739271639663842053155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694492847759775894702103 25041739271639663842053155)
        ·
          refine ⟨37562608907459495763079733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25041739271639663842053155 37562608907459495763079733)
          ·
            refine ⟨3521494585074327727788725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37562608907459495763079733 3521494585074327727788725)
            ·
              refine ⟨330140117350718224480193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3521494585074327727788725 330140117350718224480193)
              ·
                refine ⟨247605088013038668360145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330140117350718224480193 247605088013038668360145)
                ·
                  refine ⟨185703816009779001270109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247605088013038668360145 185703816009779001270109)
                  ·
                    rfl

theorem cell20_406864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_406864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406864 prefixEnd_406864 := by exact prefixLift 406864
  have htrace : WordTrace (prefixWord ++ tailWord_406864) baseStart_406864 baseEnd_406864 := by
    simpa [prefixWord, tailWord_406864, baseEnd_406864] using wordTrace_append hprefix tailTrace_406864
  have hstable : (prefixWord ++ tailWord_406864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406864).length < 2 ^ (prefixWord ++ tailWord_406864).sum := by decide
  have hdescent : baseEnd_406864 < baseStart_406864 := by decide
  rcases family_descends (prefixWord ++ tailWord_406864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406913 : List Nat := [1, 2, 4, 3, 10]
def baseStart_406913 : Nat := 118140960795 + 406913 * 2 ^ 59
def prefixEnd_406913 : Nat := 4983230072969 + 3 ^ 40 * 406913 * 2
def baseEnd_406913 : Nat := 2292915814135217390575

theorem tailTrace_406913 : CollatzResearch.WordTrace tailWord_406913 prefixEnd_406913 2292915814135217390575 := by
  unfold tailWord_406913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841336374831171052713393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9894224249887447368475595 14841336374831171052713393)
  ·
    refine ⟨11131002281123378289535045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14841336374831171052713393 11131002281123378289535045)
    ·
      refine ⟨2087062927710633429287821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11131002281123378289535045 2087062927710633429287821)
      ·
        refine ⟨782648597891487535982933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2087062927710633429287821 782648597891487535982933)
        ·
          refine ⟨2292915814135217390575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 782648597891487535982933 2292915814135217390575)
          ·
            rfl

theorem cell20_406913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 10].length) (baseStart_406913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406913 prefixEnd_406913 := by exact prefixLift 406913
  have htrace : WordTrace (prefixWord ++ tailWord_406913) baseStart_406913 baseEnd_406913 := by
    simpa [prefixWord, tailWord_406913, baseEnd_406913] using wordTrace_append hprefix tailTrace_406913
  have hstable : (prefixWord ++ tailWord_406913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406913).length < 2 ^ (prefixWord ++ tailWord_406913).sum := by decide
  have hdescent : baseEnd_406913 < baseStart_406913 := by decide
  rcases family_descends (prefixWord ++ tailWord_406913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406916 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_406916 : Nat := 118140960795 + 406916 * 2 ^ 59
def prefixEnd_406916 : Nat := 4983230072969 + 3 ^ 40 * 406916 * 2
def baseEnd_406916 : Nat := 185727550226697931536563

theorem tailTrace_406916 : CollatzResearch.WordTrace tailWord_406916 prefixEnd_406916 185727550226697931536563 := by
  unfold tailWord_406916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7420722896910151282536301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9894297195880201710048401 7420722896910151282536301)
  ·
    refine ⟨2782771086341306730951113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7420722896910151282536301 2782771086341306730951113)
    ·
      refine ⟨2087078314755980048213335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782771086341306730951113 2087078314755980048213335)
      ·
        refine ⟨3130617472133970072320003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087078314755980048213335 3130617472133970072320003)
        ·
          refine ⟨4695926208200955108480005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130617472133970072320003 4695926208200955108480005)
          ·
            refine ⟨880486164037679082840001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4695926208200955108480005 880486164037679082840001)
            ·
              refine ⟨660364623028259312130001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880486164037679082840001 660364623028259312130001)
              ·
                refine ⟨495273467271194484097501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660364623028259312130001 495273467271194484097501)
                ·
                  refine ⟨185727550226697931536563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495273467271194484097501 185727550226697931536563)
                  ·
                    rfl

theorem cell20_406916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_406916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406916 prefixEnd_406916 := by exact prefixLift 406916
  have htrace : WordTrace (prefixWord ++ tailWord_406916) baseStart_406916 baseEnd_406916 := by
    simpa [prefixWord, tailWord_406916, baseEnd_406916] using wordTrace_append hprefix tailTrace_406916
  have hstable : (prefixWord ++ tailWord_406916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406916).length < 2 ^ (prefixWord ++ tailWord_406916).sum := by decide
  have hdescent : baseEnd_406916 < baseStart_406916 := by decide
  rcases family_descends (prefixWord ++ tailWord_406916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406919 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 2]
def baseStart_406919 : Nat := 118140960795 + 406919 * 2 ^ 59
def prefixEnd_406919 : Nat := 4983230072969 + 3 ^ 40 * 406919 * 2
def baseEnd_406919 : Nat := 185728919508443254436551

theorem tailTrace_406919 : CollatzResearch.WordTrace tailWord_406919 prefixEnd_406919 185728919508443254436551 := by
  unfold tailWord_406919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841555212809434077431811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9894370141872956051621207 14841555212809434077431811)
  ·
    refine ⟨22262332819214151116147717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841555212809434077431811 22262332819214151116147717)
    ·
      refine ⟨4174187403602653334277697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22262332819214151116147717 4174187403602653334277697)
      ·
        refine ⟨3130640552701990000708273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174187403602653334277697 3130640552701990000708273)
        ·
          refine ⟨2347980414526492500531205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130640552701990000708273 2347980414526492500531205)
          ·
            refine ⟨440246327723717343849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2347980414526492500531205 440246327723717343849601)
            ·
              refine ⟨330184745792788007887201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440246327723717343849601 330184745792788007887201)
              ·
                refine ⟨247638559344591005915401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330184745792788007887201 247638559344591005915401)
                ·
                  refine ⟨185728919508443254436551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247638559344591005915401 185728919508443254436551)
                  ·
                    rfl

theorem cell20_406919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 2].length) (baseStart_406919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406919 prefixEnd_406919 := by exact prefixLift 406919
  have htrace : WordTrace (prefixWord ++ tailWord_406919) baseStart_406919 baseEnd_406919 := by
    simpa [prefixWord, tailWord_406919, baseEnd_406919] using wordTrace_append hprefix tailTrace_406919
  have hstable : (prefixWord ++ tailWord_406919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406919).length < 2 ^ (prefixWord ++ tailWord_406919).sum := by decide
  have hdescent : baseEnd_406919 < baseStart_406919 := by decide
  rcases family_descends (prefixWord ++ tailWord_406919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406923 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 2]
def baseStart_406923 : Nat := 118140960795 + 406923 * 2 ^ 59
def prefixEnd_406923 : Nat := 4983230072969 + 3 ^ 40 * 406923 * 2
def baseEnd_406923 : Nat := 185730745217437018303201

theorem tailTrace_406923 : CollatzResearch.WordTrace tailWord_406923 prefixEnd_406923 185730745217437018303201 := by
  unfold tailWord_406923
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841701104794942760577423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9894467403196628507051615 14841701104794942760577423)
  ·
    refine ⟨22262551657192414140866135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841701104794942760577423 22262551657192414140866135)
    ·
      refine ⟨33393827485788621211299203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22262551657192414140866135 33393827485788621211299203)
      ·
        refine ⟨50090741228682931816948805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33393827485788621211299203 50090741228682931816948805)
        ·
          refine ⟨9392013980378049715677901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50090741228682931816948805 9392013980378049715677901)
          ·
            refine ⟨3522005242641768643379213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9392013980378049715677901 3522005242641768643379213)
            ·
              refine ⟨1320751965990663241267205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3522005242641768643379213 1320751965990663241267205)
              ·
                refine ⟨247640993623249357737601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1320751965990663241267205 247640993623249357737601)
                ·
                  refine ⟨185730745217437018303201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247640993623249357737601 185730745217437018303201)
                  ·
                    rfl

theorem cell20_406923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2].length) (baseStart_406923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406923 prefixEnd_406923 := by exact prefixLift 406923
  have htrace : WordTrace (prefixWord ++ tailWord_406923) baseStart_406923 baseEnd_406923 := by
    simpa [prefixWord, tailWord_406923, baseEnd_406923] using wordTrace_append hprefix tailTrace_406923
  have hstable : (prefixWord ++ tailWord_406923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406923).length < 2 ^ (prefixWord ++ tailWord_406923).sum := by decide
  have hdescent : baseEnd_406923 < baseStart_406923 := by decide
  rcases family_descends (prefixWord ++ tailWord_406923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406926 : List Nat := [4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_406926 : Nat := 118140960795 + 406926 * 2 ^ 59
def prefixEnd_406926 : Nat := 4983230072969 + 3 ^ 40 * 406926 * 2
def baseEnd_406926 : Nat := 61910704833060780401063

theorem tailTrace_406926 : CollatzResearch.WordTrace tailWord_406926 prefixEnd_406926 61910704833060780401063 := by
  unfold tailWord_406926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855226315473009284117079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9894540349189382848624421 1855226315473009284117079)
  ·
    refine ⟨2782839473209513926175619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855226315473009284117079 2782839473209513926175619)
    ·
      refine ⟨4174259209814270889263429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782839473209513926175619 4174259209814270889263429)
      ·
        refine ⟨782673601840175791736893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4174259209814270889263429 782673601840175791736893)
        ·
          refine ⟨293502600690065921901335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 782673601840175791736893 293502600690065921901335)
          ·
            refine ⟨440253901035098882852003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293502600690065921901335 440253901035098882852003)
            ·
              refine ⟨660380851552648324278005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440253901035098882852003 660380851552648324278005)
              ·
                refine ⟨61910704833060780401063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660380851552648324278005 61910704833060780401063)
                ·
                  rfl

theorem cell20_406926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_406926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406926 prefixEnd_406926 := by exact prefixLift 406926
  have htrace : WordTrace (prefixWord ++ tailWord_406926) baseStart_406926 baseEnd_406926 := by
    simpa [prefixWord, tailWord_406926, baseEnd_406926] using wordTrace_append hprefix tailTrace_406926
  have hstable : (prefixWord ++ tailWord_406926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406926).length < 2 ^ (prefixWord ++ tailWord_406926).sum := by decide
  have hdescent : baseEnd_406926 < baseStart_406926 := by decide
  rcases family_descends (prefixWord ++ tailWord_406926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406937 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_406937 : Nat := 118140960795 + 406937 * 2 ^ 59
def prefixEnd_406937 : Nat := 4983230072969 + 3 ^ 40 * 406937 * 2
def baseEnd_406937 : Nat := 185737135198915191836477

theorem tailTrace_406937 : CollatzResearch.WordTrace tailWord_406937 prefixEnd_406937 185737135198915191836477 := by
  unfold tailWord_406937
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842211726744223151587065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9894807817829482101058043 14842211726744223151587065)
  ·
    refine ⟨11131658795058167363690299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14842211726744223151587065 11131658795058167363690299)
    ·
      refine ⟨16697488192587251045535449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11131658795058167363690299 16697488192587251045535449)
      ·
        refine ⟨12523116144440438284151587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16697488192587251045535449 12523116144440438284151587)
        ·
          refine ⟨18784674216660657426227381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12523116144440438284151587 18784674216660657426227381)
          ·
            refine ⟨1761063207811936633708817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18784674216660657426227381 1761063207811936633708817)
            ·
              refine ⟨1320797405858952475281613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761063207811936633708817 1320797405858952475281613)
              ·
                refine ⟨495299027197107178230605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320797405858952475281613 495299027197107178230605)
                ·
                  refine ⟨185737135198915191836477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495299027197107178230605 185737135198915191836477)
                  ·
                    rfl

theorem cell20_406937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_406937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406937 prefixEnd_406937 := by exact prefixLift 406937
  have htrace : WordTrace (prefixWord ++ tailWord_406937) baseStart_406937 baseEnd_406937 := by
    simpa [prefixWord, tailWord_406937, baseEnd_406937] using wordTrace_append hprefix tailTrace_406937
  have hstable : (prefixWord ++ tailWord_406937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406937).length < 2 ^ (prefixWord ++ tailWord_406937).sum := by decide
  have hdescent : baseEnd_406937 < baseStart_406937 := by decide
  rcases family_descends (prefixWord ++ tailWord_406937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406940 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_406940 : Nat := 118140960795 + 406940 * 2 ^ 59
def prefixEnd_406940 : Nat := 4983230072969 + 3 ^ 40 * 406940 * 2
def baseEnd_406940 : Nat := 185738504480660514736465

theorem tailTrace_406940 : CollatzResearch.WordTrace tailWord_406940 prefixEnd_406940 185738504480660514736465 := by
  unfold tailWord_406940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421160572866677331973137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9894880763822236442630849 7421160572866677331973137)
  ·
    refine ⟨5565870429650007998979853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7421160572866677331973137 5565870429650007998979853)
    ·
      refine ⟨2087201411118752999617445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5565870429650007998979853 2087201411118752999617445)
      ·
        refine ⟨391350264584766187428271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2087201411118752999617445 391350264584766187428271)
        ·
          refine ⟨587025396877149281142407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391350264584766187428271 587025396877149281142407)
          ·
            refine ⟨880538095315723921713611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587025396877149281142407 880538095315723921713611)
            ·
              refine ⟨1320807142973585882570417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880538095315723921713611 1320807142973585882570417)
              ·
                refine ⟨990605357230189411927813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320807142973585882570417 990605357230189411927813)
                ·
                  refine ⟨185738504480660514736465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990605357230189411927813 185738504480660514736465)
                  ·
                    rfl

theorem cell20_406940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_406940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406940 prefixEnd_406940 := by exact prefixLift 406940
  have htrace : WordTrace (prefixWord ++ tailWord_406940) baseStart_406940 baseEnd_406940 := by
    simpa [prefixWord, tailWord_406940, baseEnd_406940] using wordTrace_append hprefix tailTrace_406940
  have hstable : (prefixWord ++ tailWord_406940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406940).length < 2 ^ (prefixWord ++ tailWord_406940).sum := by decide
  have hdescent : baseEnd_406940 < baseStart_406940 := by decide
  rcases family_descends (prefixWord ++ tailWord_406940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406944 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_406944 : Nat := 118140960795 + 406944 * 2 ^ 59
def prefixEnd_406944 : Nat := 4983230072969 + 3 ^ 40 * 406944 * 2
def baseEnd_406944 : Nat := 185740330189654278603115

theorem tailTrace_406944 : CollatzResearch.WordTrace tailWord_406944 prefixEnd_406944 185740330189654278603115 := by
  unfold tailWord_406944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421233518859431673545943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9894978025145908898061257 7421233518859431673545943)
  ·
    refine ⟨11131850278289147510318915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421233518859431673545943 11131850278289147510318915)
    ·
      refine ⟨16697775417433721265478373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11131850278289147510318915 16697775417433721265478373)
      ·
        refine ⟨3130832890768822737277195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16697775417433721265478373 3130832890768822737277195)
        ·
          refine ⟨4696249336153234105915793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130832890768822737277195 4696249336153234105915793)
          ·
            refine ⟨3522187002114925579436845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4696249336153234105915793 3522187002114925579436845)
            ·
              refine ⟨1320820125793097092288817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3522187002114925579436845 1320820125793097092288817)
              ·
                refine ⟨990615094344822819216613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320820125793097092288817 990615094344822819216613)
                ·
                  refine ⟨185740330189654278603115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990615094344822819216613 185740330189654278603115)
                  ·
                    rfl

theorem cell20_406944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_406944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406944 prefixEnd_406944 := by exact prefixLift 406944
  have htrace : WordTrace (prefixWord ++ tailWord_406944) baseStart_406944 baseEnd_406944 := by
    simpa [prefixWord, tailWord_406944, baseEnd_406944] using wordTrace_append hprefix tailTrace_406944
  have hstable : (prefixWord ++ tailWord_406944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406944).length < 2 ^ (prefixWord ++ tailWord_406944).sum := by decide
  have hdescent : baseEnd_406944 < baseStart_406944 := by decide
  rcases family_descends (prefixWord ++ tailWord_406944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406957 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 2]
def baseStart_406957 : Nat := 118140960795 + 406957 * 2 ^ 59
def prefixEnd_406957 : Nat := 4983230072969 + 3 ^ 40 * 406957 * 2
def baseEnd_406957 : Nat := 185746263743884011169729

theorem tailTrace_406957 : CollatzResearch.WordTrace tailWord_406957 prefixEnd_406957 185746263743884011169729 := by
  unfold tailWord_406957
  simp only [CollatzResearch.WordTrace]
  refine ⟨14842941186671766567315125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9895294124447844378210083 14842941186671766567315125)
  ·
    refine ⟨1391525736250478115685793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14842941186671766567315125 1391525736250478115685793)
    ·
      refine ⟨1043644302187858586764345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1391525736250478115685793 1043644302187858586764345)
      ·
        refine ⟨782733226640893940073259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043644302187858586764345 782733226640893940073259)
        ·
          refine ⟨1174099839961340910109889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782733226640893940073259 1174099839961340910109889)
          ·
            refine ⟨880574879971005682582417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174099839961340910109889 880574879971005682582417)
            ·
              refine ⟨660431159978254261936813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 880574879971005682582417 660431159978254261936813)
              ·
                refine ⟨247661684991845348226305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660431159978254261936813 247661684991845348226305)
                ·
                  refine ⟨185746263743884011169729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247661684991845348226305 185746263743884011169729)
                  ·
                    rfl

theorem cell20_406957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_406957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_406957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_406957 prefixEnd_406957 := by exact prefixLift 406957
  have htrace : WordTrace (prefixWord ++ tailWord_406957) baseStart_406957 baseEnd_406957 := by
    simpa [prefixWord, tailWord_406957, baseEnd_406957] using wordTrace_append hprefix tailTrace_406957
  have hstable : (prefixWord ++ tailWord_406957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406957).length < 2 ^ (prefixWord ++ tailWord_406957).sum := by decide
  have hdescent : baseEnd_406957 < baseStart_406957 := by decide
  rcases family_descends (prefixWord ++ tailWord_406957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407013 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_407013 : Nat := 118140960795 + 407013 * 2 ^ 59
def prefixEnd_407013 : Nat := 4983230072969 + 3 ^ 40 * 407013 * 2
def baseEnd_407013 : Nat := 185771823669796705302833

theorem tailTrace_407013 : CollatzResearch.WordTrace tailWord_407013 prefixEnd_407013 185771823669796705302833 := by
  unfold tailWord_407013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844983674468888131353693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9896655782979258754235795 14844983674468888131353693)
  ·
    refine ⟨5566868877925833049257635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14844983674468888131353693 5566868877925833049257635)
    ·
      refine ⟨8350303316888749573886453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566868877925833049257635 8350303316888749573886453)
      ·
        refine ⟨782840935958320272551855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8350303316888749573886453 782840935958320272551855)
        ·
          refine ⟨1174261403937480408827783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782840935958320272551855 1174261403937480408827783)
          ·
            refine ⟨1761392105906220613241675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174261403937480408827783 1761392105906220613241675)
            ·
              refine ⟨2642088158859330919862513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761392105906220613241675 2642088158859330919862513)
              ·
                refine ⟨1981566119144498189896885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2642088158859330919862513 1981566119144498189896885)
                ·
                  refine ⟨185771823669796705302833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981566119144498189896885 185771823669796705302833)
                  ·
                    rfl

theorem cell20_407013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_407013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407013 prefixEnd_407013 := by exact prefixLift 407013
  have htrace : WordTrace (prefixWord ++ tailWord_407013) baseStart_407013 baseEnd_407013 := by
    simpa [prefixWord, tailWord_407013, baseEnd_407013] using wordTrace_append hprefix tailTrace_407013
  have hstable : (prefixWord ++ tailWord_407013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407013).length < 2 ^ (prefixWord ++ tailWord_407013).sum := by decide
  have hdescent : baseEnd_407013 < baseStart_407013 := by decide
  rcases family_descends (prefixWord ++ tailWord_407013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407034 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_407034 : Nat := 118140960795 + 407034 * 2 ^ 59
def prefixEnd_407034 : Nat := 4983230072969 + 3 ^ 40 * 407034 * 2
def baseEnd_407034 : Nat := 185781408642013965602747

theorem tailTrace_407034 : CollatzResearch.WordTrace tailWord_407034 prefixEnd_407034 185781408642013965602747 := by
  unfold tailWord_407034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711437401848202179467039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9897166404928539145245437 3711437401848202179467039)
  ·
    refine ⟨5567156102772303269200559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3711437401848202179467039 5567156102772303269200559)
    ·
      refine ⟨8350734154158454903800839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5567156102772303269200559 8350734154158454903800839)
      ·
        refine ⟨12526101231237682355701259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8350734154158454903800839 12526101231237682355701259)
        ·
          refine ⟨18789151846856523533551889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12526101231237682355701259 18789151846856523533551889)
          ·
            refine ⟨14091863885142392650163917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18789151846856523533551889 14091863885142392650163917)
            ·
              refine ⟨5284448956928397243811469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14091863885142392650163917 5284448956928397243811469)
              ·
                refine ⟨1981668358848148966429301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5284448956928397243811469 1981668358848148966429301)
                ·
                  refine ⟨185781408642013965602747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1981668358848148966429301 185781408642013965602747)
                  ·
                    rfl

theorem cell20_407034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_407034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407034 prefixEnd_407034 := by exact prefixLift 407034
  have htrace : WordTrace (prefixWord ++ tailWord_407034) baseStart_407034 baseEnd_407034 := by
    simpa [prefixWord, tailWord_407034, baseEnd_407034] using wordTrace_append hprefix tailTrace_407034
  have hstable : (prefixWord ++ tailWord_407034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407034).length < 2 ^ (prefixWord ++ tailWord_407034).sum := by decide
  have hdescent : baseEnd_407034 < baseStart_407034 := by decide
  rcases family_descends (prefixWord ++ tailWord_407034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407037 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_407037 : Nat := 118140960795 + 407037 * 2 ^ 59
def prefixEnd_407037 : Nat := 4983230072969 + 3 ^ 40 * 407037 * 2
def baseEnd_407037 : Nat := 185782777923759288502735

theorem tailTrace_407037 : CollatzResearch.WordTrace tailWord_407037 prefixEnd_407037 185782777923759288502735 := by
  unfold tailWord_407037
  simp only [CollatzResearch.WordTrace]
  refine ⟨14845859026381940230227365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9897239350921293486818243 14845859026381940230227365)
  ·
    refine ⟨2783598567446613793167631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14845859026381940230227365 2783598567446613793167631)
    ·
      refine ⟨4175397851169920689751447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783598567446613793167631 4175397851169920689751447)
      ·
        refine ⟨6263096776754881034627171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4175397851169920689751447 6263096776754881034627171)
        ·
          refine ⟨9394645165132321551940757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6263096776754881034627171 9394645165132321551940757)
          ·
            refine ⟨440373992115577572747223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9394645165132321551940757 440373992115577572747223)
            ·
              refine ⟨660560988173366359120835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440373992115577572747223 660560988173366359120835)
              ·
                refine ⟨990841482260049538681253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660560988173366359120835 990841482260049538681253)
                ·
                  refine ⟨185782777923759288502735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 990841482260049538681253 185782777923759288502735)
                  ·
                    rfl

theorem cell20_407037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_407037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407037 prefixEnd_407037 := by exact prefixLift 407037
  have htrace : WordTrace (prefixWord ++ tailWord_407037) baseStart_407037 baseEnd_407037 := by
    simpa [prefixWord, tailWord_407037, baseEnd_407037] using wordTrace_append hprefix tailTrace_407037
  have hstable : (prefixWord ++ tailWord_407037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407037).length < 2 ^ (prefixWord ++ tailWord_407037).sum := by decide
  have hdescent : baseEnd_407037 < baseStart_407037 := by decide
  rcases family_descends (prefixWord ++ tailWord_407037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407047 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_407047 : Nat := 118140960795 + 407047 * 2 ^ 59
def prefixEnd_407047 : Nat := 4983230072969 + 3 ^ 40 * 407047 * 2
def baseEnd_407047 : Nat := 185787342196243698169361

theorem tailTrace_407047 : CollatzResearch.WordTrace tailWord_407047 prefixEnd_407047 185787342196243698169361 := by
  unfold tailWord_407047
  simp only [CollatzResearch.WordTrace]
  refine ⟨14846223756345711938091395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9897482504230474625394263 14846223756345711938091395)
  ·
    refine ⟨22269335634518567907137093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14846223756345711938091395 22269335634518567907137093)
    ·
      refine ⟨4175500431472231482588205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22269335634518567907137093 4175500431472231482588205)
      ·
        refine ⟨1565812661802086805970577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4175500431472231482588205 1565812661802086805970577)
        ·
          refine ⟨1174359496351565104477933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565812661802086805970577 1174359496351565104477933)
          ·
            refine ⟨440384811131836914179225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1174359496351565104477933 440384811131836914179225)
            ·
              refine ⟨330288608348877685634419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440384811131836914179225 330288608348877685634419)
              ·
                refine ⟨495432912523316528451629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330288608348877685634419 495432912523316528451629)
                ·
                  refine ⟨185787342196243698169361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495432912523316528451629 185787342196243698169361)
                  ·
                    rfl

theorem cell20_407047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_407047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407047 prefixEnd_407047 := by exact prefixLift 407047
  have htrace : WordTrace (prefixWord ++ tailWord_407047) baseStart_407047 baseEnd_407047 := by
    simpa [prefixWord, tailWord_407047, baseEnd_407047] using wordTrace_append hprefix tailTrace_407047
  have hstable : (prefixWord ++ tailWord_407047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407047).length < 2 ^ (prefixWord ++ tailWord_407047).sum := by decide
  have hdescent : baseEnd_407047 < baseStart_407047 := by decide
  rcases family_descends (prefixWord ++ tailWord_407047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407103 : List Nat := [1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_407103 : Nat := 118140960795 + 407103 * 2 ^ 59
def prefixEnd_407103 : Nat := 4983230072969 + 3 ^ 40 * 407103 * 2
def baseEnd_407103 : Nat := 61937634040718797434155

theorem tailTrace_407103 : CollatzResearch.WordTrace tailWord_407103 prefixEnd_407103 61937634040718797434155 := by
  unfold tailWord_407103
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848266244142833502129963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9898844162761889001419975 14848266244142833502129963)
  ·
    refine ⟨22272399366214250253194945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848266244142833502129963 22272399366214250253194945)
    ·
      refine ⟨16704299524660687689896209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22272399366214250253194945 16704299524660687689896209)
      ·
        refine ⟨12528224643495515767422157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16704299524660687689896209 12528224643495515767422157)
        ·
          refine ⟨4698084241310818412783309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12528224643495515767422157 4698084241310818412783309)
          ·
            refine ⟨1761781590491556904793741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4698084241310818412783309 1761781590491556904793741)
            ·
              refine ⟨660668096434333839297653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1761781590491556904793741 660668096434333839297653)
              ·
                refine ⟨61937634040718797434155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660668096434333839297653 61937634040718797434155)
                ·
                  rfl

theorem cell20_407103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_407103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407103 prefixEnd_407103 := by exact prefixLift 407103
  have htrace : WordTrace (prefixWord ++ tailWord_407103) baseStart_407103 baseEnd_407103 := by
    simpa [prefixWord, tailWord_407103, baseEnd_407103] using wordTrace_append hprefix tailTrace_407103
  have hstable : (prefixWord ++ tailWord_407103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407103).length < 2 ^ (prefixWord ++ tailWord_407103).sum := by decide
  have hdescent : baseEnd_407103 < baseStart_407103 := by decide
  rcases family_descends (prefixWord ++ tailWord_407103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407141 : List Nat := [1, 3, 1, 3, 3, 2, 7]
def baseStart_407141 : Nat := 118140960795 + 407141 * 2 ^ 59
def prefixEnd_407141 : Nat := 4983230072969 + 3 ^ 40 * 407141 * 2
def baseEnd_407141 : Nat := 20647805150844127670627

theorem tailTrace_407141 : CollatzResearch.WordTrace tailWord_407141 prefixEnd_407141 20647805150844127670627 := by
  unfold tailWord_407141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849652218005165992013277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9899768145336777328008851 14849652218005165992013277)
  ·
    refine ⟨5568619581751937247004979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14849652218005165992013277 5568619581751937247004979)
    ·
      refine ⟨8352929372627905870507469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5568619581751937247004979 8352929372627905870507469)
      ·
        refine ⟨3132348514735464701440301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8352929372627905870507469 3132348514735464701440301)
        ·
          refine ⟨1174630693025799263040113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3132348514735464701440301 1174630693025799263040113)
          ·
            refine ⟨880973019769349447280085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174630693025799263040113 880973019769349447280085)
            ·
              refine ⟨20647805150844127670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 880973019769349447280085 20647805150844127670627)
              ·
                rfl

theorem cell20_407141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_407141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407141 prefixEnd_407141 := by exact prefixLift 407141
  have htrace : WordTrace (prefixWord ++ tailWord_407141) baseStart_407141 baseEnd_407141 := by
    simpa [prefixWord, tailWord_407141, baseEnd_407141] using wordTrace_append hprefix tailTrace_407141
  have hstable : (prefixWord ++ tailWord_407141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407141).length < 2 ^ (prefixWord ++ tailWord_407141).sum := by decide
  have hdescent : baseEnd_407141 < baseStart_407141 := by decide
  rcases family_descends (prefixWord ++ tailWord_407141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407144 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_407144 : Nat := 118140960795 + 407144 * 2 ^ 59
def prefixEnd_407144 : Nat := 4983230072969 + 3 ^ 40 * 407144 * 2
def baseEnd_407144 : Nat := 185831615639342471935631

theorem tailTrace_407144 : CollatzResearch.WordTrace tailWord_407144 prefixEnd_407144 185831615639342471935631 := by
  unfold tailWord_407144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424880818497148752186243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9899841091329531669581657 7424880818497148752186243)
  ·
    refine ⟨11137321227745723128279365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424880818497148752186243 11137321227745723128279365)
    ·
      refine ⟨2088247730202323086552381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11137321227745723128279365 2088247730202323086552381)
      ·
        refine ⟨783092898825871157457143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2088247730202323086552381 783092898825871157457143)
        ·
          refine ⟨1174639348238806736185715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783092898825871157457143 1174639348238806736185715)
          ·
            refine ⟨1761959022358210104278573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174639348238806736185715 1761959022358210104278573)
            ·
              refine ⟨660734633384328789104465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1761959022358210104278573 660734633384328789104465)
              ·
                refine ⟨495550975038246591828349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660734633384328789104465 495550975038246591828349)
                ·
                  refine ⟨185831615639342471935631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495550975038246591828349 185831615639342471935631)
                  ·
                    rfl

theorem cell20_407144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_407144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407144 prefixEnd_407144 := by exact prefixLift 407144
  have htrace : WordTrace (prefixWord ++ tailWord_407144) baseStart_407144 baseEnd_407144 := by
    simpa [prefixWord, tailWord_407144, baseEnd_407144] using wordTrace_append hprefix tailTrace_407144
  have hstable : (prefixWord ++ tailWord_407144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407144).length < 2 ^ (prefixWord ++ tailWord_407144).sum := by decide
  have hdescent : baseEnd_407144 < baseStart_407144 := by decide
  rcases family_descends (prefixWord ++ tailWord_407144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407196 : List Nat := [2, 2, 3, 2, 3, 2, 6]
def baseStart_407196 : Nat := 118140960795 + 407196 * 2 ^ 59
def prefixEnd_407196 : Nat := 4983230072969 + 3 ^ 40 * 407196 * 2
def baseEnd_407196 : Nat := 20650594428473489133565

theorem tailTrace_407196 : CollatzResearch.WordTrace tailWord_407196 prefixEnd_407196 20650594428473489133565 := by
  unfold tailWord_407196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425829116402955192632721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9901105488537273590176961 7425829116402955192632721)
  ·
    refine ⟨5569371837302216394474541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7425829116402955192632721 5569371837302216394474541)
    ·
      refine ⟨2088514438988331147927953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5569371837302216394474541 2088514438988331147927953)
      ·
        refine ⟨1566385829241248360945965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2088514438988331147927953 1566385829241248360945965)
        ·
          refine ⟨587394685965468135354737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1566385829241248360945965 587394685965468135354737)
          ·
            refine ⟨440546014474101101516053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587394685965468135354737 440546014474101101516053)
            ·
              refine ⟨20650594428473489133565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440546014474101101516053 20650594428473489133565)
              ·
                rfl

theorem cell20_407196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_407196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407196 prefixEnd_407196 := by exact prefixLift 407196
  have htrace : WordTrace (prefixWord ++ tailWord_407196) baseStart_407196 baseEnd_407196 := by
    simpa [prefixWord, tailWord_407196, baseEnd_407196] using wordTrace_append hprefix tailTrace_407196
  have hstable : (prefixWord ++ tailWord_407196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407196).length < 2 ^ (prefixWord ++ tailWord_407196).sum := by decide
  have hdescent : baseEnd_407196 < baseStart_407196 := by decide
  rcases family_descends (prefixWord ++ tailWord_407196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407202 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_407202 : Nat := 118140960795 + 407202 * 2 ^ 59
def prefixEnd_407202 : Nat := 4983230072969 + 3 ^ 40 * 407202 * 2
def baseEnd_407202 : Nat := 185858088419752048002061

theorem tailTrace_407202 : CollatzResearch.WordTrace tailWord_407202 prefixEnd_407202 185858088419752048002061 := by
  unfold tailWord_407202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712969267696043352495965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9901251380522782273322573 3712969267696043352495965)
  ·
    refine ⟨1392363475386016257185987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3712969267696043352495965 1392363475386016257185987)
    ·
      refine ⟨2088545213079024385778981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392363475386016257185987 2088545213079024385778981)
      ·
        refine ⟨391602227452317072333559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2088545213079024385778981 391602227452317072333559)
        ·
          refine ⟨587403341178475608500339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391602227452317072333559 587403341178475608500339)
          ·
            refine ⟨881105011767713412750509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587403341178475608500339 881105011767713412750509)
            ·
              refine ⟨330414379412892529781441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 881105011767713412750509 330414379412892529781441)
              ·
                refine ⟨247810784559669397336081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330414379412892529781441 247810784559669397336081)
                ·
                  refine ⟨185858088419752048002061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247810784559669397336081 185858088419752048002061)
                  ·
                    rfl

theorem cell20_407202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_407202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407202 prefixEnd_407202 := by exact prefixLift 407202
  have htrace : WordTrace (prefixWord ++ tailWord_407202) baseStart_407202 baseEnd_407202 := by
    simpa [prefixWord, tailWord_407202, baseEnd_407202] using wordTrace_append hprefix tailTrace_407202
  have hstable : (prefixWord ++ tailWord_407202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407202).length < 2 ^ (prefixWord ++ tailWord_407202).sum := by decide
  have hdescent : baseEnd_407202 < baseStart_407202 := by decide
  rcases family_descends (prefixWord ++ tailWord_407202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407231 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_407231 : Nat := 118140960795 + 407231 * 2 ^ 59
def prefixEnd_407231 : Nat := 4983230072969 + 3 ^ 40 * 407231 * 2
def baseEnd_407231 : Nat := 185871324809956836035275

theorem tailTrace_407231 : CollatzResearch.WordTrace tailWord_407231 prefixEnd_407231 185871324809956836035275 := by
  unfold tailWord_407231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14852934787679111362789547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9901956525119407575193031 14852934787679111362789547)
  ·
    refine ⟨22279402181518667044184321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14852934787679111362789547 22279402181518667044184321)
    ·
      refine ⟨16709551636139000283138241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22279402181518667044184321 16709551636139000283138241)
      ·
        refine ⟨12532163727104250212353681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16709551636139000283138241 12532163727104250212353681)
        ·
          refine ⟨9399122795328187659265261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12532163727104250212353681 9399122795328187659265261)
          ·
            refine ⟨3524671048248070372224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399122795328187659265261 3524671048248070372224473)
            ·
              refine ⟨2643503286186052779168355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524671048248070372224473 2643503286186052779168355)
              ·
                refine ⟨3965254929279079168752533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643503286186052779168355 3965254929279079168752533)
                ·
                  refine ⟨185871324809956836035275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3965254929279079168752533 185871324809956836035275)
                  ·
                    rfl

theorem cell20_407231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_407231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407231 prefixEnd_407231 := by exact prefixLift 407231
  have htrace : WordTrace (prefixWord ++ tailWord_407231) baseStart_407231 baseEnd_407231 := by
    simpa [prefixWord, tailWord_407231, baseEnd_407231] using wordTrace_append hprefix tailTrace_407231
  have hstable : (prefixWord ++ tailWord_407231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407231).length < 2 ^ (prefixWord ++ tailWord_407231).sum := by decide
  have hdescent : baseEnd_407231 < baseStart_407231 := by decide
  rcases family_descends (prefixWord ++ tailWord_407231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407254 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_407254 : Nat := 118140960795 + 407254 * 2 ^ 59
def prefixEnd_407254 : Nat := 4983230072969 + 3 ^ 40 * 407254 * 2
def baseEnd_407254 : Nat := 185881822636670978268515

theorem tailTrace_407254 : CollatzResearch.WordTrace tailWord_407254 prefixEnd_407254 185881822636670978268515 := by
  unfold tailWord_407254
  simp only [CollatzResearch.WordTrace]
  refine ⟨928360854162236643179801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9902515777730524193917877 928360854162236643179801)
  ·
    refine ⟨696270640621677482384851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 928360854162236643179801 696270640621677482384851)
    ·
      refine ⟨1044405960932516223577277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696270640621677482384851 1044405960932516223577277)
      ·
        refine ⟨391652235349693583841479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1044405960932516223577277 391652235349693583841479)
        ·
          refine ⟨587478353024540375762219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391652235349693583841479 587478353024540375762219)
          ·
            refine ⟨881217529536810563643329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587478353024540375762219 881217529536810563643329)
            ·
              refine ⟨660913147152607922732497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881217529536810563643329 660913147152607922732497)
              ·
                refine ⟨495684860364455942049373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 660913147152607922732497 495684860364455942049373)
                ·
                  refine ⟨185881822636670978268515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495684860364455942049373 185881822636670978268515)
                  ·
                    rfl

theorem cell20_407254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_407254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407254 prefixEnd_407254 := by exact prefixLift 407254
  have htrace : WordTrace (prefixWord ++ tailWord_407254) baseStart_407254 baseEnd_407254 := by
    simpa [prefixWord, tailWord_407254, baseEnd_407254] using wordTrace_append hprefix tailTrace_407254
  have hstable : (prefixWord ++ tailWord_407254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407254).length < 2 ^ (prefixWord ++ tailWord_407254).sum := by decide
  have hdescent : baseEnd_407254 < baseStart_407254 := by decide
  rcases family_descends (prefixWord ++ tailWord_407254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407261 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 2]
def baseStart_407261 : Nat := 118140960795 + 407261 * 2 ^ 59
def prefixEnd_407261 : Nat := 4983230072969 + 3 ^ 40 * 407261 * 2
def baseEnd_407261 : Nat := 185885017627410065035153

theorem tailTrace_407261 : CollatzResearch.WordTrace tailWord_407261 prefixEnd_407261 185885017627410065035153 := by
  unfold tailWord_407261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854028977570426486381637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9902685985046950990921091 14854028977570426486381637)
  ·
    refine ⟨2785130433294454966196557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14854028977570426486381637 2785130433294454966196557)
    ·
      refine ⟨1044423912485420612323709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2785130433294454966196557 1044423912485420612323709)
      ·
        refine ⟨391658967182032729621391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1044423912485420612323709 391658967182032729621391)
        ·
          refine ⟨587488450773049094432087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391658967182032729621391 587488450773049094432087)
          ·
            refine ⟨881232676159573641648131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587488450773049094432087 881232676159573641648131)
            ·
              refine ⟨1321849014239360462472197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881232676159573641648131 1321849014239360462472197)
              ·
                refine ⟨247846690169880086713537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1321849014239360462472197 247846690169880086713537)
                ·
                  refine ⟨185885017627410065035153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247846690169880086713537 185885017627410065035153)
                  ·
                    rfl

theorem cell20_407261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_407261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407261 prefixEnd_407261 := by exact prefixLift 407261
  have htrace : WordTrace (prefixWord ++ tailWord_407261) baseStart_407261 baseEnd_407261 := by
    simpa [prefixWord, tailWord_407261, baseEnd_407261] using wordTrace_append hprefix tailTrace_407261
  have hstable : (prefixWord ++ tailWord_407261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407261).length < 2 ^ (prefixWord ++ tailWord_407261).sum := by decide
  have hdescent : baseEnd_407261 < baseStart_407261 := by decide
  rcases family_descends (prefixWord ++ tailWord_407261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407272 : List Nat := [2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_407272 : Nat := 118140960795 + 407272 * 2 ^ 59
def prefixEnd_407272 : Nat := 4983230072969 + 3 ^ 40 * 407272 * 2
def baseEnd_407272 : Nat := 61963346109047638556147

theorem tailTrace_407272 : CollatzResearch.WordTrace tailWord_407272 prefixEnd_407272 61963346109047638556147 := by
  unfold tailWord_407272
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427215090265287682516035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9902953453687050243354713 7427215090265287682516035)
  ·
    refine ⟨11140822635397931523774053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7427215090265287682516035 11140822635397931523774053)
    ·
      refine ⟨2088904244137112160707635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11140822635397931523774053 2088904244137112160707635)
      ·
        refine ⟨3133356366205668241061453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088904244137112160707635 3133356366205668241061453)
        ·
          refine ⟨1175008637327125590398045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3133356366205668241061453 1175008637327125590398045)
          ·
            refine ⟨440628238997672096399267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175008637327125590398045 440628238997672096399267)
            ·
              refine ⟨660942358496508144598901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440628238997672096399267 660942358496508144598901)
              ·
                refine ⟨61963346109047638556147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 660942358496508144598901 61963346109047638556147)
                ·
                  rfl

theorem cell20_407272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_407272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407272 prefixEnd_407272 := by exact prefixLift 407272
  have htrace : WordTrace (prefixWord ++ tailWord_407272) baseStart_407272 baseEnd_407272 := by
    simpa [prefixWord, tailWord_407272, baseEnd_407272] using wordTrace_append hprefix tailTrace_407272
  have hstable : (prefixWord ++ tailWord_407272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407272).length < 2 ^ (prefixWord ++ tailWord_407272).sum := by decide
  have hdescent : baseEnd_407272 < baseStart_407272 := by decide
  rcases family_descends (prefixWord ++ tailWord_407272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407286 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_407286 : Nat := 118140960795 + 407286 * 2 ^ 59
def prefixEnd_407286 : Nat := 4983230072969 + 3 ^ 40 * 407286 * 2
def baseEnd_407286 : Nat := 185896428308621089201717

theorem tailTrace_407286 : CollatzResearch.WordTrace tailWord_407286 prefixEnd_407286 185896428308621089201717 := by
  unfold tailWord_407286
  simp only [CollatzResearch.WordTrace]
  refine ⟨928433800154990984752607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9903293868319903837361141 928433800154990984752607)
  ·
    refine ⟨1392650700232486477128911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928433800154990984752607 1392650700232486477128911)
    ·
      refine ⟨2088976050348729715693367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392650700232486477128911 2088976050348729715693367)
      ·
        refine ⟨3133464075523094573540051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088976050348729715693367 3133464075523094573540051)
        ·
          refine ⟨4700196113284641860310077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133464075523094573540051 4700196113284641860310077)
          ·
            refine ⟨1762573542481740697616279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4700196113284641860310077 1762573542481740697616279)
            ·
              refine ⟨2643860313722611046424419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762573542481740697616279 2643860313722611046424419)
              ·
                refine ⟨3965790470583916569636629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643860313722611046424419 3965790470583916569636629)
                ·
                  refine ⟨185896428308621089201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3965790470583916569636629 185896428308621089201717)
                  ·
                    rfl

theorem cell20_407286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_407286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407286 prefixEnd_407286 := by exact prefixLift 407286
  have htrace : WordTrace (prefixWord ++ tailWord_407286) baseStart_407286 baseEnd_407286 := by
    simpa [prefixWord, tailWord_407286, baseEnd_407286] using wordTrace_append hprefix tailTrace_407286
  have hstable : (prefixWord ++ tailWord_407286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407286).length < 2 ^ (prefixWord ++ tailWord_407286).sum := by decide
  have hdescent : baseEnd_407286 < baseStart_407286 := by decide
  rcases family_descends (prefixWord ++ tailWord_407286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407317 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_407317 : Nat := 118140960795 + 407317 * 2 ^ 59
def prefixEnd_407317 : Nat := 4983230072969 + 3 ^ 40 * 407317 * 2
def baseEnd_407317 : Nat := 185910577553322759168257

theorem tailTrace_407317 : CollatzResearch.WordTrace tailWord_407317 prefixEnd_407317 185910577553322759168257 := by
  unfold tailWord_407317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14856071465367548050420205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9904047643578365366946803 14856071465367548050420205)
  ·
    refine ⟨5571026799512830518907577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14856071465367548050420205 5571026799512830518907577)
    ·
      refine ⟨4178270099634622889180683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5571026799512830518907577 4178270099634622889180683)
      ·
        refine ⟨6267405149451934333771025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178270099634622889180683 6267405149451934333771025)
        ·
          refine ⟨4700553862088950750328269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6267405149451934333771025 4700553862088950750328269)
          ·
            refine ⟨1762707698283356531373101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4700553862088950750328269 1762707698283356531373101)
            ·
              refine ⟨661015386856258699264913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1762707698283356531373101 661015386856258699264913)
              ·
                refine ⟨495761540142194024448685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661015386856258699264913 495761540142194024448685)
                ·
                  refine ⟨185910577553322759168257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495761540142194024448685 185910577553322759168257)
                  ·
                    rfl

theorem cell20_407317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_407317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407317 prefixEnd_407317 := by exact prefixLift 407317
  have htrace : WordTrace (prefixWord ++ tailWord_407317) baseStart_407317 baseEnd_407317 := by
    simpa [prefixWord, tailWord_407317, baseEnd_407317] using wordTrace_append hprefix tailTrace_407317
  have hstable : (prefixWord ++ tailWord_407317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407317).length < 2 ^ (prefixWord ++ tailWord_407317).sum := by decide
  have hdescent : baseEnd_407317 < baseStart_407317 := by decide
  rcases family_descends (prefixWord ++ tailWord_407317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407324 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_407324 : Nat := 118140960795 + 407324 * 2 ^ 59
def prefixEnd_407324 : Nat := 4983230072969 + 3 ^ 40 * 407324 * 2
def baseEnd_407324 : Nat := 185913772544061845934895

theorem tailTrace_407324 : CollatzResearch.WordTrace tailWord_407324 prefixEnd_407324 185913772544061845934895 := by
  unfold tailWord_407324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428163388171094122962513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9904217850894792163950017 7428163388171094122962513)
  ·
    refine ⟨5571122541128320592221885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7428163388171094122962513 5571122541128320592221885)
    ·
      refine ⟨2089170952923120222083207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5571122541128320592221885 2089170952923120222083207)
      ·
        refine ⟨3133756429384680333124811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089170952923120222083207 3133756429384680333124811)
        ·
          refine ⟨4700634644077020499687217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133756429384680333124811 4700634644077020499687217)
          ·
            refine ⟨3525475983057765374765413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4700634644077020499687217 3525475983057765374765413)
            ·
              refine ⟨661026746823331007768515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3525475983057765374765413 661026746823331007768515)
              ·
                refine ⟨991540120234996511652773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661026746823331007768515 991540120234996511652773)
                ·
                  refine ⟨185913772544061845934895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991540120234996511652773 185913772544061845934895)
                  ·
                    rfl

theorem cell20_407324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_407324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407324 prefixEnd_407324 := by exact prefixLift 407324
  have htrace : WordTrace (prefixWord ++ tailWord_407324) baseStart_407324 baseEnd_407324 := by
    simpa [prefixWord, tailWord_407324, baseEnd_407324] using wordTrace_append hprefix tailTrace_407324
  have hstable : (prefixWord ++ tailWord_407324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407324).length < 2 ^ (prefixWord ++ tailWord_407324).sum := by decide
  have hdescent : baseEnd_407324 < baseStart_407324 := by decide
  rcases family_descends (prefixWord ++ tailWord_407324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407348 : List Nat := [2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_407348 : Nat := 118140960795 + 407348 * 2 ^ 59
def prefixEnd_407348 : Nat := 4983230072969 + 3 ^ 40 * 407348 * 2
def baseEnd_407348 : Nat := 61974908932674809711599

theorem tailTrace_407348 : CollatzResearch.WordTrace tailWord_407348 prefixEnd_407348 61974908932674809711599 := by
  unfold tailWord_407348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7428601064127620172399349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9904801418836826896532465 7428601064127620172399349)
  ·
    refine ⟨696431349761964391162439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7428601064127620172399349 696431349761964391162439)
    ·
      refine ⟨1044647024642946586743659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696431349761964391162439 1044647024642946586743659)
      ·
        refine ⟨1566970536964419880115489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044647024642946586743659 1566970536964419880115489)
        ·
          refine ⟨1175227902723314910086617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566970536964419880115489 1175227902723314910086617)
          ·
            refine ⟨881420927042486182564963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1175227902723314910086617 881420927042486182564963)
            ·
              refine ⟨1322131390563729273847445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881420927042486182564963 1322131390563729273847445)
              ·
                refine ⟨61974908932674809711599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1322131390563729273847445 61974908932674809711599)
                ·
                  rfl

theorem cell20_407348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_407348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407348 prefixEnd_407348 := by exact prefixLift 407348
  have htrace : WordTrace (prefixWord ++ tailWord_407348) baseStart_407348 baseEnd_407348 := by
    simpa [prefixWord, tailWord_407348, baseEnd_407348] using wordTrace_append hprefix tailTrace_407348
  have hstable : (prefixWord ++ tailWord_407348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407348).length < 2 ^ (prefixWord ++ tailWord_407348).sum := by decide
  have hdescent : baseEnd_407348 < baseStart_407348 := by decide
  rcases family_descends (prefixWord ++ tailWord_407348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407358 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_407358 : Nat := 118140960795 + 407358 * 2 ^ 59
def prefixEnd_407358 : Nat := 4983230072969 + 3 ^ 40 * 407358 * 2
def baseEnd_407358 : Nat := 185929291070508838801423

theorem tailTrace_407358 : CollatzResearch.WordTrace tailWord_407358 prefixEnd_407358 185929291070508838801423 := by
  unfold tailWord_407358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857195857277376506582841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9905044572146008035108485 1857195857277376506582841)
  ·
    refine ⟨1392896892958032379937131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1857195857277376506582841 1392896892958032379937131)
    ·
      refine ⟨2089345339437048569905697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392896892958032379937131 2089345339437048569905697)
      ·
        refine ⟨1567009004577786427429273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2089345339437048569905697 1567009004577786427429273)
        ·
          refine ⟨1175256753433339820571955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567009004577786427429273 1175256753433339820571955)
          ·
            refine ⟨1762885130150009730857933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175256753433339820571955 1762885130150009730857933)
            ·
              refine ⟨661081923806253649071725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1762885130150009730857933 661081923806253649071725)
              ·
                refine ⟨247905721427345118401897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661081923806253649071725 247905721427345118401897)
                ·
                  refine ⟨185929291070508838801423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247905721427345118401897 185929291070508838801423)
                  ·
                    rfl

theorem cell20_407358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_407358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407358 prefixEnd_407358 := by exact prefixLift 407358
  have htrace : WordTrace (prefixWord ++ tailWord_407358) baseStart_407358 baseEnd_407358 := by
    simpa [prefixWord, tailWord_407358, baseEnd_407358] using wordTrace_append hprefix tailTrace_407358
  have hstable : (prefixWord ++ tailWord_407358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407358).length < 2 ^ (prefixWord ++ tailWord_407358).sum := by decide
  have hdescent : baseEnd_407358 < baseStart_407358 := by decide
  rcases family_descends (prefixWord ++ tailWord_407358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407376 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_407376 : Nat := 118140960795 + 407376 * 2 ^ 59
def prefixEnd_407376 : Nat := 4983230072969 + 3 ^ 40 * 407376 * 2
def baseEnd_407376 : Nat := 185937506760980776201349

theorem tailTrace_407376 : CollatzResearch.WordTrace tailWord_407376 prefixEnd_407376 185937506760980776201349 := by
  unfold tailWord_407376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429111686076900563408991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9905482248102534084545321 7429111686076900563408991)
  ·
    refine ⟨11143667529115350845113487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7429111686076900563408991 11143667529115350845113487)
    ·
      refine ⟨16715501293673026267670231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11143667529115350845113487 16715501293673026267670231)
      ·
        refine ⟨25073251940509539401505347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16715501293673026267670231 25073251940509539401505347)
        ·
          refine ⟨37609877910764309102258021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25073251940509539401505347 37609877910764309102258021)
          ·
            refine ⟨7051852108268307956673379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37609877910764309102258021 7051852108268307956673379)
            ·
              refine ⟨10577778162402461935010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051852108268307956673379 10577778162402461935010069)
              ·
                refine ⟨495833351362615403203597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10577778162402461935010069 495833351362615403203597)
                ·
                  refine ⟨185937506760980776201349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495833351362615403203597 185937506760980776201349)
                  ·
                    rfl

theorem cell20_407376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_407376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407376 prefixEnd_407376 := by exact prefixLift 407376
  have htrace : WordTrace (prefixWord ++ tailWord_407376) baseStart_407376 baseEnd_407376 := by
    simpa [prefixWord, tailWord_407376, baseEnd_407376] using wordTrace_append hprefix tailTrace_407376
  have hstable : (prefixWord ++ tailWord_407376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407376).length < 2 ^ (prefixWord ++ tailWord_407376).sum := by decide
  have hdescent : baseEnd_407376 < baseStart_407376 := by decide
  rcases family_descends (prefixWord ++ tailWord_407376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407434 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_407434 : Nat := 118140960795 + 407434 * 2 ^ 59
def prefixEnd_407434 : Nat := 4983230072969 + 3 ^ 40 * 407434 * 2
def baseEnd_407434 : Nat := 185963979541390352267779

theorem tailTrace_407434 : CollatzResearch.WordTrace tailWord_407434 prefixEnd_407434 185963979541390352267779 := by
  unfold tailWord_407434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715084701485919258107339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9906892537295784688286237 3715084701485919258107339)
  ·
    refine ⟨5572627052228878887161009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715084701485919258107339 5572627052228878887161009)
    ·
      refine ⟨4179470289171659165370757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5572627052228878887161009 4179470289171659165370757)
      ·
        refine ⟨783650679219686093507017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4179470289171659165370757 783650679219686093507017)
        ·
          refine ⟨587738009414764570130263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783650679219686093507017 587738009414764570130263)
          ·
            refine ⟨881607014122146855195395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587738009414764570130263 881607014122146855195395)
            ·
              refine ⟨1322410521183220282793093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881607014122146855195395 1322410521183220282793093)
              ·
                refine ⟨247951972721853803023705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1322410521183220282793093 247951972721853803023705)
                ·
                  refine ⟨185963979541390352267779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247951972721853803023705 185963979541390352267779)
                  ·
                    rfl

theorem cell20_407434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_407434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407434 prefixEnd_407434 := by exact prefixLift 407434
  have htrace : WordTrace (prefixWord ++ tailWord_407434) baseStart_407434 baseEnd_407434 := by
    simpa [prefixWord, tailWord_407434, baseEnd_407434] using wordTrace_append hprefix tailTrace_407434
  have hstable : (prefixWord ++ tailWord_407434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407434).length < 2 ^ (prefixWord ++ tailWord_407434).sum := by decide
  have hdescent : baseEnd_407434 < baseStart_407434 := by decide
  rcases family_descends (prefixWord ++ tailWord_407434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407486 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_407486 : Nat := 118140960795 + 407486 * 2 ^ 59
def prefixEnd_407486 : Nat := 4983230072969 + 3 ^ 40 * 407486 * 2
def baseEnd_407486 : Nat := 185987713758309282534233

theorem tailTrace_407486 : CollatzResearch.WordTrace tailWord_407486 prefixEnd_407486 185987713758309282534233 := by
  unfold tailWord_407486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857779425219411239165289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9908156934503526608881541 1857779425219411239165289)
  ·
    refine ⟨1393334568914558429373967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1857779425219411239165289 1393334568914558429373967)
    ·
      refine ⟨2090001853371837644060951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393334568914558429373967 2090001853371837644060951)
      ·
        refine ⟨3135002780057756466091427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090001853371837644060951 3135002780057756466091427)
        ·
          refine ⟨4702504170086634699137141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135002780057756466091427 4702504170086634699137141)
          ·
            refine ⟨440859765945622003044107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4702504170086634699137141 440859765945622003044107)
            ·
              refine ⟨661289648918433004566161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440859765945622003044107 661289648918433004566161)
              ·
                refine ⟨495967236688824753424621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661289648918433004566161 495967236688824753424621)
                ·
                  refine ⟨185987713758309282534233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 495967236688824753424621 185987713758309282534233)
                  ·
                    rfl

theorem cell20_407486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_407486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407486 prefixEnd_407486 := by exact prefixLift 407486
  have htrace : WordTrace (prefixWord ++ tailWord_407486) baseStart_407486 baseEnd_407486 := by
    simpa [prefixWord, tailWord_407486, baseEnd_407486] using wordTrace_append hprefix tailTrace_407486
  have hstable : (prefixWord ++ tailWord_407486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407486).length < 2 ^ (prefixWord ++ tailWord_407486).sum := by decide
  have hdescent : baseEnd_407486 < baseStart_407486 := by decide
  rcases family_descends (prefixWord ++ tailWord_407486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
