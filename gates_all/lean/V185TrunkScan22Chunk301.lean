import V185TrunkScan22Chunk300

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2684616 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_2684616 : Nat := 118140960795 + 2684616 * 2 ^ 59
def prefixEnd_2684616 : Nat := 4983230072969 + 3 ^ 40 * 2684616 * 2
def baseEnd_2684616 : Nat := 918998920500515774169121

theorem tailTrace_2684616 : CollatzResearch.WordTrace tailWord_2684616 prefixEnd_2684616 918998920500515774169121 := by
  unfold tailWord_2684616
  simp only [CollatzResearch.WordTrace]
  refine ⟨48957994821051101377592851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65277326428068135170123801 48957994821051101377592851)
  ·
    refine ⟨73436992231576652066389277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48957994821051101377592851 73436992231576652066389277)
    ·
      refine ⟨27538872086841244524895979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73436992231576652066389277 27538872086841244524895979)
      ·
        refine ⟨41308308130261866787343969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27538872086841244524895979 41308308130261866787343969)
        ·
          refine ⟨30981231097696400090507977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41308308130261866787343969 30981231097696400090507977)
          ·
            refine ⟨23235923323272300067880983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30981231097696400090507977 23235923323272300067880983)
            ·
              refine ⟨34853884984908450101821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23235923323272300067880983 34853884984908450101821475)
              ·
                refine ⟨52280827477362675152732213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34853884984908450101821475 52280827477362675152732213)
                ·
                  refine ⟨4901327576002750795568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52280827477362675152732213 4901327576002750795568645)
                  ·
                    refine ⟨918998920500515774169121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4901327576002750795568645 918998920500515774169121)
                    ·
                      rfl

theorem cell22_2684616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_2684616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684616 prefixEnd_2684616 := by exact prefixLift 2684616
  have htrace : WordTrace (prefixWord ++ tailWord_2684616) baseStart_2684616 baseEnd_2684616 := by
    simpa [prefixWord, tailWord_2684616, baseEnd_2684616] using wordTrace_append hprefix tailTrace_2684616
  have hstable : (prefixWord ++ tailWord_2684616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684616).length < 2 ^ (prefixWord ++ tailWord_2684616).sum := by decide
  have hdescent : baseEnd_2684616 < baseStart_2684616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684618 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_2684618 : Nat := 118140960795 + 2684618 * 2 ^ 59
def prefixEnd_2684618 : Nat := 4983230072969 + 3 ^ 40 * 2684618 * 2
def baseEnd_2684618 : Nat := 918999605141388435619115

theorem tailTrace_2684618 : CollatzResearch.WordTrace tailWord_2684618 prefixEnd_2684618 918999605141388435619115 := by
  unfold tailWord_2684618
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479015647023739274189627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65277375058729971397839005 24479015647023739274189627)
  ·
    refine ⟨36718523470535608911284441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479015647023739274189627 36718523470535608911284441)
    ·
      refine ⟨27538892602901706683463331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36718523470535608911284441 27538892602901706683463331)
      ·
        refine ⟨41308338904352560025194997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27538892602901706683463331 41308338904352560025194997)
        ·
          refine ⟨3872656772283052502362031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41308338904352560025194997 3872656772283052502362031)
          ·
            refine ⟨5808985158424578753543047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872656772283052502362031 5808985158424578753543047)
            ·
              refine ⟨8713477737636868130314571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808985158424578753543047 8713477737636868130314571)
              ·
                refine ⟨13070216606455302195471857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8713477737636868130314571 13070216606455302195471857)
                ·
                  refine ⟨9802662454841476646603893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13070216606455302195471857 9802662454841476646603893)
                  ·
                    refine ⟨918999605141388435619115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9802662454841476646603893 918999605141388435619115)
                    ·
                      rfl

theorem cell22_2684618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_2684618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684618 prefixEnd_2684618 := by exact prefixLift 2684618
  have htrace : WordTrace (prefixWord ++ tailWord_2684618) baseStart_2684618 baseEnd_2684618 := by
    simpa [prefixWord, tailWord_2684618, baseEnd_2684618] using wordTrace_append hprefix tailTrace_2684618
  have hstable : (prefixWord ++ tailWord_2684618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684618).length < 2 ^ (prefixWord ++ tailWord_2684618).sum := by decide
  have hdescent : baseEnd_2684618 < baseStart_2684618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684631 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 6]
def baseStart_2684631 : Nat := 118140960795 + 2684631 * 2 ^ 59
def prefixEnd_2684631 : Nat := 4983230072969 + 3 ^ 40 * 2684631 * 2
def baseEnd_2684631 : Nat := 306334685102353578348025

theorem tailTrace_2684631 : CollatzResearch.WordTrace tailWord_2684631 prefixEnd_2684631 306334685102353578348025 := by
  unfold tailWord_2684631
  simp only [CollatzResearch.WordTrace]
  refine ⟨97916536737047860316981747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65277691158031906877987831 97916536737047860316981747)
  ·
    refine ⟨146874805105571790475472621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97916536737047860316981747 146874805105571790475472621)
    ·
      refine ⟨55078051914589421428302233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146874805105571790475472621 55078051914589421428302233)
      ·
        refine ⟨41308538935942066071226675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55078051914589421428302233 41308538935942066071226675)
        ·
          refine ⟨61962808403913099106840013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41308538935942066071226675 61962808403913099106840013)
          ·
            refine ⟨23236053151467412165065005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61962808403913099106840013 23236053151467412165065005)
            ·
              refine ⟨8713519931800279561899377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23236053151467412165065005 8713519931800279561899377)
              ·
                refine ⟨6535139948850209671424533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713519931800279561899377 6535139948850209671424533)
                ·
                  refine ⟨306334685102353578348025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6535139948850209671424533 306334685102353578348025)
                  ·
                    rfl

theorem cell22_2684631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 6].length) (baseStart_2684631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684631 prefixEnd_2684631 := by exact prefixLift 2684631
  have htrace : WordTrace (prefixWord ++ tailWord_2684631) baseStart_2684631 baseEnd_2684631 := by
    simpa [prefixWord, tailWord_2684631, baseEnd_2684631] using wordTrace_append hprefix tailTrace_2684631
  have hstable : (prefixWord ++ tailWord_2684631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684631).length < 2 ^ (prefixWord ++ tailWord_2684631).sum := by decide
  have hdescent : baseEnd_2684631 < baseStart_2684631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684650 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2684650 : Nat := 118140960795 + 2684650 * 2 ^ 59
def prefixEnd_2684650 : Nat := 4983230072969 + 3 ^ 40 * 2684650 * 2
def baseEnd_2684650 : Nat := 919010559395351018819017

theorem tailTrace_2684650 : CollatzResearch.WordTrace tailWord_2684650 prefixEnd_2684650 919010559395351018819017 := by
  unfold tailWord_2684650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479307430994756640480851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65278153149319351041282269 24479307430994756640480851)
  ·
    refine ⟨36718961146492134960721277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479307430994756640480851 36718961146492134960721277)
    ·
      refine ⟨13769610429934550610270479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36718961146492134960721277 13769610429934550610270479)
      ·
        refine ⟨20654415644901825915405719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769610429934550610270479 20654415644901825915405719)
        ·
          refine ⟨30981623467352738873108579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20654415644901825915405719 30981623467352738873108579)
          ·
            refine ⟨46472435201029108309662869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30981623467352738873108579 46472435201029108309662869)
            ·
              refine ⟨2178395400048239452015447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46472435201029108309662869 2178395400048239452015447)
              ·
                refine ⟨3267593100072359178023171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178395400048239452015447 3267593100072359178023171)
                ·
                  refine ⟨4901389650108538767034757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267593100072359178023171 4901389650108538767034757)
                  ·
                    refine ⟨919010559395351018819017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4901389650108538767034757 919010559395351018819017)
                    ·
                      rfl

theorem cell22_2684650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2684650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684650 prefixEnd_2684650 := by exact prefixLift 2684650
  have htrace : WordTrace (prefixWord ++ tailWord_2684650) baseStart_2684650 baseEnd_2684650 := by
    simpa [prefixWord, tailWord_2684650, baseEnd_2684650] using wordTrace_append hprefix tailTrace_2684650
  have hstable : (prefixWord ++ tailWord_2684650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684650).length < 2 ^ (prefixWord ++ tailWord_2684650).sum := by decide
  have hdescent : baseEnd_2684650 < baseStart_2684650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684693 : List Nat := [1, 3, 2, 1, 2, 3, 4, 6]
def baseStart_2684693 : Nat := 118140960795 + 2684693 * 2 ^ 59
def prefixEnd_2684693 : Nat := 4983230072969 + 3 ^ 40 * 2684693 * 2
def baseEnd_2684693 : Nat := 102113919908234804443765

theorem tailTrace_2684693 : CollatzResearch.WordTrace tailWord_2684693 prefixEnd_2684693 102113919908234804443765 := by
  unfold tailWord_2684693
  simp only [CollatzResearch.WordTrace]
  refine ⟨97918798062823244905738733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65279198708548829937159155 97918798062823244905738733)
  ·
    refine ⟨36719549273558716839652025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97918798062823244905738733 36719549273558716839652025)
    ·
      refine ⟨27539661955169037629739019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36719549273558716839652025 27539661955169037629739019)
      ·
        refine ⟨41309492932753556444608529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539661955169037629739019 41309492932753556444608529)
        ·
          refine ⟨30982119699565167333456397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41309492932753556444608529 30982119699565167333456397)
          ·
            refine ⟨11618294887336937750046149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30982119699565167333456397 11618294887336937750046149)
            ·
              refine ⟨2178430291375675828133653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11618294887336937750046149 2178430291375675828133653)
              ·
                refine ⟨102113919908234804443765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2178430291375675828133653 102113919908234804443765)
                ·
                  rfl

theorem cell22_2684693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 6].length) (baseStart_2684693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684693 prefixEnd_2684693 := by exact prefixLift 2684693
  have htrace : WordTrace (prefixWord ++ tailWord_2684693) baseStart_2684693 baseEnd_2684693 := by
    simpa [prefixWord, tailWord_2684693, baseEnd_2684693] using wordTrace_append hprefix tailTrace_2684693
  have hstable : (prefixWord ++ tailWord_2684693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684693).length < 2 ^ (prefixWord ++ tailWord_2684693).sum := by decide
  have hdescent : baseEnd_2684693 < baseStart_2684693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684849 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_2684849 : Nat := 118140960795 + 2684849 * 2 ^ 59
def prefixEnd_2684849 : Nat := 4983230072969 + 3 ^ 40 * 2684849 * 2
def baseEnd_2684849 : Nat := 919078681162180833093407

theorem tailTrace_2684849 : CollatzResearch.WordTrace tailWord_2684849 prefixEnd_2684849 919078681162180833093407 := by
  unfold tailWord_2684849
  simp only [CollatzResearch.WordTrace]
  refine ⟨97924487850258083548417601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65282991900172055698945067 97924487850258083548417601)
  ·
    refine ⟨73443365887693562661313201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97924487850258083548417601 73443365887693562661313201)
    ·
      refine ⟨55082524415770171995984901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73443365887693562661313201 55082524415770171995984901)
      ·
        refine ⟨10327973327956907249247169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55082524415770171995984901 10327973327956907249247169)
        ·
          refine ⟨7745979995967680436935377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10327973327956907249247169 7745979995967680436935377)
          ·
            refine ⟨5809484996975760327701533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745979995967680436935377 5809484996975760327701533)
            ·
              refine ⟨2178556873865910122888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5809484996975760327701533 2178556873865910122888075)
              ·
                refine ⟨3267835310798865184332113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178556873865910122888075 3267835310798865184332113)
                ·
                  refine ⟨2450876483099148888249085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267835310798865184332113 2450876483099148888249085)
                  ·
                    refine ⟨919078681162180833093407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2450876483099148888249085 919078681162180833093407)
                    ·
                      rfl

theorem cell22_2684849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_2684849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684849 prefixEnd_2684849 := by exact prefixLift 2684849
  have htrace : WordTrace (prefixWord ++ tailWord_2684849) baseStart_2684849 baseEnd_2684849 := by
    simpa [prefixWord, tailWord_2684849, baseEnd_2684849] using wordTrace_append hprefix tailTrace_2684849
  have hstable : (prefixWord ++ tailWord_2684849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684849).length < 2 ^ (prefixWord ++ tailWord_2684849).sum := by decide
  have hdescent : baseEnd_2684849 < baseStart_2684849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684862 : List Nat := [4, 2, 1, 1, 1, 5, 2, 6]
def baseStart_2684862 : Nat := 118140960795 + 2684862 * 2 ^ 59
def prefixEnd_2684862 : Nat := 4983230072969 + 3 ^ 40 * 2684862 * 2
def baseEnd_2684862 : Nat := 102120347925317014724263

theorem tailTrace_2684862 : CollatzResearch.WordTrace tailWord_2684862 prefixEnd_2684862 102120347925317014724263 := by
  unfold tailWord_2684862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240620249901373346080105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65283307999473991179093893 12240620249901373346080105)
  ·
    refine ⟨9180465187426030009560079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12240620249901373346080105 9180465187426030009560079)
    ·
      refine ⟨13770697781139045014340119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9180465187426030009560079 13770697781139045014340119)
      ·
        refine ⟨20656046671708567521510179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13770697781139045014340119 20656046671708567521510179)
        ·
          refine ⟨30984070007562851282265269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20656046671708567521510179 30984070007562851282265269)
          ·
            refine ⟨2904756563209017307712369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30984070007562851282265269 2904756563209017307712369)
            ·
              refine ⟨2178567422406762980784277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904756563209017307712369 2178567422406762980784277)
              ·
                refine ⟨102120347925317014724263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2178567422406762980784277 102120347925317014724263)
                ·
                  rfl

theorem cell22_2684862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_2684862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684862 prefixEnd_2684862 := by exact prefixLift 2684862
  have htrace : WordTrace (prefixWord ++ tailWord_2684862) baseStart_2684862 baseEnd_2684862 := by
    simpa [prefixWord, tailWord_2684862, baseEnd_2684862] using wordTrace_append hprefix tailTrace_2684862
  have hstable : (prefixWord ++ tailWord_2684862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684862).length < 2 ^ (prefixWord ++ tailWord_2684862).sum := by decide
  have hdescent : baseEnd_2684862 < baseStart_2684862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684952 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 4]
def baseStart_2684952 : Nat := 118140960795 + 2684952 * 2 ^ 59
def prefixEnd_2684952 : Nat := 4983230072969 + 3 ^ 40 * 2684952 * 2
def baseEnd_2684952 : Nat := 306371313389040965922697

theorem tailTrace_2684952 : CollatzResearch.WordTrace tailWord_2684952 prefixEnd_2684952 306371313389040965922697 := by
  unfold tailWord_2684952
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964122284442466069708555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65285496379256621426278073 48964122284442466069708555)
  ·
    refine ⟨73446183426663699104562833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48964122284442466069708555 73446183426663699104562833)
    ·
      refine ⟨55084637569997774328422125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73446183426663699104562833 55084637569997774328422125)
      ·
        refine ⟨20656739088749165373158297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55084637569997774328422125 20656739088749165373158297)
        ·
          refine ⟨15492554316561874029868723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20656739088749165373158297 15492554316561874029868723)
          ·
            refine ⟨23238831474842811044803085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492554316561874029868723 23238831474842811044803085)
            ·
              refine ⟨8714561803066054141801157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23238831474842811044803085 8714561803066054141801157)
              ·
                refine ⟨1633980338074885151587717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8714561803066054141801157 1633980338074885151587717)
                ·
                  refine ⟨306371313389040965922697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633980338074885151587717 306371313389040965922697)
                  ·
                    rfl

theorem cell22_2684952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_2684952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684952 prefixEnd_2684952 := by exact prefixLift 2684952
  have htrace : WordTrace (prefixWord ++ tailWord_2684952) baseStart_2684952 baseEnd_2684952 := by
    simpa [prefixWord, tailWord_2684952, baseEnd_2684952] using wordTrace_append hprefix tailTrace_2684952
  have hstable : (prefixWord ++ tailWord_2684952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684952).length < 2 ^ (prefixWord ++ tailWord_2684952).sum := by decide
  have hdescent : baseEnd_2684952 < baseStart_2684952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684982 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2684982 : Nat := 118140960795 + 2684982 * 2 ^ 59
def prefixEnd_2684982 : Nat := 4983230072969 + 3 ^ 40 * 2684982 * 2
def baseEnd_2684982 : Nat := 919124209780212819517999

theorem tailTrace_2684982 : CollatzResearch.WordTrace tailWord_2684982 prefixEnd_2684982 919124209780212819517999 := by
  unfold tailWord_2684982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120583672423515453938075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65286225839184164842006133 6120583672423515453938075)
  ·
    refine ⟨9180875508635273180907113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6120583672423515453938075 9180875508635273180907113)
    ·
      refine ⟨6885656631476454885680335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9180875508635273180907113 6885656631476454885680335)
      ·
        refine ⟨10328484947214682328520503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6885656631476454885680335 10328484947214682328520503)
        ·
          refine ⟨15492727420822023492780755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328484947214682328520503 15492727420822023492780755)
          ·
            refine ⟨23239091131233035239171133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492727420822023492780755 23239091131233035239171133)
            ·
              refine ⟨8714659174212388214689175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23239091131233035239171133 8714659174212388214689175)
              ·
                refine ⟨13071988761318582322033763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8714659174212388214689175 13071988761318582322033763)
                ·
                  refine ⟨19607983141977873483050645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13071988761318582322033763 19607983141977873483050645)
                  ·
                    refine ⟨919124209780212819517999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19607983141977873483050645 919124209780212819517999)
                    ·
                      rfl

theorem cell22_2684982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2684982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2684982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2684982 prefixEnd_2684982 := by exact prefixLift 2684982
  have htrace : WordTrace (prefixWord ++ tailWord_2684982) baseStart_2684982 baseEnd_2684982 := by
    simpa [prefixWord, tailWord_2684982, baseEnd_2684982] using wordTrace_append hprefix tailTrace_2684982
  have hstable : (prefixWord ++ tailWord_2684982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684982).length < 2 ^ (prefixWord ++ tailWord_2684982).sum := by decide
  have hdescent : baseEnd_2684982 < baseStart_2684982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685076 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 5]
def baseStart_2685076 : Nat := 118140960795 + 2685076 * 2 ^ 59
def prefixEnd_2685076 : Nat := 4983230072969 + 3 ^ 40 * 2685076 * 2
def baseEnd_2685076 : Nat := 306385462633742635889237

theorem tailTrace_2685076 : CollatzResearch.WordTrace tailWord_2685076 prefixEnd_2685076 306385462633742635889237 := by
  unfold tailWord_2685076
  simp only [CollatzResearch.WordTrace]
  refine ⟨48966383610217850658465541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65288511480290467544620721 48966383610217850658465541)
  ·
    refine ⟨9181196926915846998462289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48966383610217850658465541 9181196926915846998462289)
    ·
      refine ⟨6885897695186885248846717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9181196926915846998462289 6885897695186885248846717)
      ·
        refine ⟨2582211635695081968317519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6885897695186885248846717 2582211635695081968317519)
        ·
          refine ⟨3873317453542622952476279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582211635695081968317519 3873317453542622952476279)
          ·
            refine ⟨5809976180313934428714419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873317453542622952476279 5809976180313934428714419)
            ·
              refine ⟨8714964270470901643071629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809976180313934428714419 8714964270470901643071629)
              ·
                refine ⟨3268111601426588116151861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8714964270470901643071629 3268111601426588116151861)
                ·
                  refine ⟨306385462633742635889237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3268111601426588116151861 306385462633742635889237)
                  ·
                    rfl

theorem cell22_2685076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_2685076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685076 prefixEnd_2685076 := by exact prefixLift 2685076
  have htrace : WordTrace (prefixWord ++ tailWord_2685076) baseStart_2685076 baseEnd_2685076 := by
    simpa [prefixWord, tailWord_2685076, baseEnd_2685076] using wordTrace_append hprefix tailTrace_2685076
  have hstable : (prefixWord ++ tailWord_2685076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685076).length < 2 ^ (prefixWord ++ tailWord_2685076).sum := by decide
  have hdescent : baseEnd_2685076 < baseStart_2685076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685089 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2685089 : Nat := 118140960795 + 2685089 * 2 ^ 59
def prefixEnd_2685089 : Nat := 4983230072969 + 3 ^ 40 * 2685089 * 2
def baseEnd_2685089 : Nat := 919160838066900207092671

theorem tailTrace_2685089 : CollatzResearch.WordTrace tailWord_2685089 prefixEnd_2685089 919160838066900207092671 := by
  unfold tailWord_2685089
  simp only [CollatzResearch.WordTrace]
  refine ⟨97933241369388604537154321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65288827579592403024769547 97933241369388604537154321)
  ·
    refine ⟨73449931027041453402865741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97933241369388604537154321 73449931027041453402865741)
    ·
      refine ⟨27543724135140545026074653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73449931027041453402865741 27543724135140545026074653)
      ·
        refine ⟨10328896550677704384777995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27543724135140545026074653 10328896550677704384777995)
        ·
          refine ⟨15493344826016556577166993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328896550677704384777995 15493344826016556577166993)
          ·
            refine ⟨11620008619512417432875245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15493344826016556577166993 11620008619512417432875245)
            ·
              refine ⟨4357503232317156537328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11620008619512417432875245 4357503232317156537328217)
              ·
                refine ⟨3268127424237867402996163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357503232317156537328217 3268127424237867402996163)
                ·
                  refine ⟨4902191136356801104494245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268127424237867402996163 4902191136356801104494245)
                  ·
                    refine ⟨919160838066900207092671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902191136356801104494245 919160838066900207092671)
                    ·
                      rfl

theorem cell22_2685089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2685089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685089 prefixEnd_2685089 := by exact prefixLift 2685089
  have htrace : WordTrace (prefixWord ++ tailWord_2685089) baseStart_2685089 baseEnd_2685089 := by
    simpa [prefixWord, tailWord_2685089, baseEnd_2685089] using wordTrace_append hprefix tailTrace_2685089
  have hstable : (prefixWord ++ tailWord_2685089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685089).length < 2 ^ (prefixWord ++ tailWord_2685089).sum := by decide
  have hdescent : baseEnd_2685089 < baseStart_2685089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685100 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_2685100 : Nat := 118140960795 + 2685100 * 2 ^ 59
def prefixEnd_2685100 : Nat := 4983230072969 + 3 ^ 40 * 2685100 * 2
def baseEnd_2685100 : Nat := 919164603591699845067637

theorem tailTrace_2685100 : CollatzResearch.WordTrace tailWord_2685100 prefixEnd_2685100 919164603591699845067637 := by
  unfold tailWord_2685100
  simp only [CollatzResearch.WordTrace]
  refine ⟨48966821286174376707902377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65289095048232502277203169 48966821286174376707902377)
  ·
    refine ⟨36725115964630782530926783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48966821286174376707902377 36725115964630782530926783)
    ·
      refine ⟨55087673946946173796390175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36725115964630782530926783 55087673946946173796390175)
      ·
        refine ⟨82631510920419260694585263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55087673946946173796390175 82631510920419260694585263)
        ·
          refine ⟨123947266380628891041877895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82631510920419260694585263 123947266380628891041877895)
          ·
            refine ⟨185920899570943336562816843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123947266380628891041877895 185920899570943336562816843)
            ·
              refine ⟨278881349356415004844225265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185920899570943336562816843 278881349356415004844225265)
              ·
                refine ⟨209161012017311253633168949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278881349356415004844225265 209161012017311253633168949)
                ·
                  refine ⟨19608844876622930028109589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209161012017311253633168949 19608844876622930028109589)
                  ·
                    refine ⟨919164603591699845067637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19608844876622930028109589 919164603591699845067637)
                    ·
                      rfl

theorem cell22_2685100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_2685100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685100 prefixEnd_2685100 := by exact prefixLift 2685100
  have htrace : WordTrace (prefixWord ++ tailWord_2685100) baseStart_2685100 baseEnd_2685100 := by
    simpa [prefixWord, tailWord_2685100, baseEnd_2685100] using wordTrace_append hprefix tailTrace_2685100
  have hstable : (prefixWord ++ tailWord_2685100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685100).length < 2 ^ (prefixWord ++ tailWord_2685100).sum := by decide
  have hdescent : baseEnd_2685100 < baseStart_2685100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685147 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 5, 3]
def baseStart_2685147 : Nat := 118140960795 + 2685147 * 2 ^ 59
def prefixEnd_2685147 : Nat := 4983230072969 + 3 ^ 40 * 2685147 * 2
def baseEnd_2685147 : Nat := 919180692652207389142493

theorem tailTrace_2685147 : CollatzResearch.WordTrace tailWord_2685147 prefixEnd_2685147 919180692652207389142493 := by
  unfold tailWord_2685147
  simp only [CollatzResearch.WordTrace]
  refine ⟨97935356803178480442765695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65290237868785653628510463 97935356803178480442765695)
  ·
    refine ⟨146903035204767720664148543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97935356803178480442765695 146903035204767720664148543)
    ·
      refine ⟨220354552807151580996222815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146903035204767720664148543 220354552807151580996222815)
      ·
        refine ⟨330531829210727371494334223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220354552807151580996222815 330531829210727371494334223)
        ·
          refine ⟨495797743816091057241501335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330531829210727371494334223 495797743816091057241501335)
          ·
            refine ⟨743696615724136585862252003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495797743816091057241501335 743696615724136585862252003)
            ·
              refine ⟨1115544923586204878793378005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743696615724136585862252003 1115544923586204878793378005)
              ·
                refine ⟨26145584146551676846719797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1115544923586204878793378005 26145584146551676846719797)
                ·
                  refine ⟨2451148513739219704379981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26145584146551676846719797 2451148513739219704379981)
                  ·
                    refine ⟨919180692652207389142493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451148513739219704379981 919180692652207389142493)
                    ·
                      rfl

theorem cell22_2685147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 3].length) (baseStart_2685147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685147 prefixEnd_2685147 := by exact prefixLift 2685147
  have htrace : WordTrace (prefixWord ++ tailWord_2685147) baseStart_2685147 baseEnd_2685147 := by
    simpa [prefixWord, tailWord_2685147, baseEnd_2685147] using wordTrace_append hprefix tailTrace_2685147
  have hstable : (prefixWord ++ tailWord_2685147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685147).length < 2 ^ (prefixWord ++ tailWord_2685147).sum := by decide
  have hdescent : baseEnd_2685147 < baseStart_2685147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685177 : List Nat := [1, 2, 1, 3, 1, 1, 2, 6, 5]
def baseStart_2685177 : Nat := 118140960795 + 2685177 * 2 ^ 59
def prefixEnd_2685177 : Nat := 4983230072969 + 3 ^ 40 * 2685177 * 2
def baseEnd_2685177 : Nat := 306396987421765770297467

theorem tailTrace_2685177 : CollatzResearch.WordTrace tailWord_2685177 prefixEnd_2685177 306396987421765770297467 := by
  unfold tailWord_2685177
  simp only [CollatzResearch.WordTrace]
  refine ⟨97936450993069795566357785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65290967328713197044238523 97936450993069795566357785)
  ·
    refine ⟨73452338244802346674768339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97936450993069795566357785 73452338244802346674768339)
    ·
      refine ⟨110178507367203520012152509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73452338244802346674768339 110178507367203520012152509)
      ·
        refine ⟨41316940262701320004557191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110178507367203520012152509 41316940262701320004557191)
        ·
          refine ⟨61975410394051980006835787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41316940262701320004557191 61975410394051980006835787)
          ·
            refine ⟨92963115591077970010253681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61975410394051980006835787 92963115591077970010253681)
            ·
              refine ⟨69722336693308477507690261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92963115591077970010253681 69722336693308477507690261)
              ·
                refine ⟨3268234532498834883172981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69722336693308477507690261 3268234532498834883172981)
                ·
                  refine ⟨306396987421765770297467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3268234532498834883172981 306396987421765770297467)
                  ·
                    rfl

theorem cell22_2685177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_2685177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685177 prefixEnd_2685177 := by exact prefixLift 2685177
  have htrace : WordTrace (prefixWord ++ tailWord_2685177) baseStart_2685177 baseEnd_2685177 := by
    simpa [prefixWord, tailWord_2685177, baseEnd_2685177] using wordTrace_append hprefix tailTrace_2685177
  have hstable : (prefixWord ++ tailWord_2685177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685177).length < 2 ^ (prefixWord ++ tailWord_2685177).sum := by decide
  have hdescent : baseEnd_2685177 < baseStart_2685177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685239 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 4]
def baseStart_2685239 : Nat := 118140960795 + 2685239 * 2 ^ 59
def prefixEnd_2685239 : Nat := 4983230072969 + 3 ^ 40 * 2685239 * 2
def baseEnd_2685239 : Nat := 306404062044116605280737

theorem tailTrace_2685239 : CollatzResearch.WordTrace tailWord_2685239 prefixEnd_2685239 306404062044116605280737 := by
  unfold tailWord_2685239
  simp only [CollatzResearch.WordTrace]
  refine ⟨97938712318845180155114771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65292474879230120103409847 97938712318845180155114771)
  ·
    refine ⟨146908068478267770232672157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97938712318845180155114771 146908068478267770232672157)
    ·
      refine ⟨55090525679350413837252059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146908068478267770232672157 55090525679350413837252059)
      ·
        refine ⟨82635788519025620755878089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55090525679350413837252059 82635788519025620755878089)
        ·
          refine ⟨61976841389269215566908567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82635788519025620755878089 61976841389269215566908567)
          ·
            refine ⟨92965262083903823350362851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61976841389269215566908567 92965262083903823350362851)
            ·
              refine ⟨139447893125855735025544277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92965262083903823350362851 139447893125855735025544277)
              ·
                refine ⟨1634154997568621894830597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 139447893125855735025544277 1634154997568621894830597)
                ·
                  refine ⟨306404062044116605280737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634154997568621894830597 306404062044116605280737)
                  ·
                    rfl

theorem cell22_2685239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 4].length) (baseStart_2685239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685239 prefixEnd_2685239 := by exact prefixLift 2685239
  have htrace : WordTrace (prefixWord ++ tailWord_2685239) baseStart_2685239 baseEnd_2685239 := by
    simpa [prefixWord, tailWord_2685239, baseEnd_2685239] using wordTrace_append hprefix tailTrace_2685239
  have hstable : (prefixWord ++ tailWord_2685239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685239).length < 2 ^ (prefixWord ++ tailWord_2685239).sum := by decide
  have hdescent : baseEnd_2685239 < baseStart_2685239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685288 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_2685288 : Nat := 118140960795 + 2685288 * 2 ^ 59
def prefixEnd_2685288 : Nat := 4983230072969 + 3 ^ 40 * 2685288 * 2
def baseEnd_2685288 : Nat := 919228959833730021367061

theorem tailTrace_2685288 : CollatzResearch.WordTrace tailWord_2685288 prefixEnd_2685288 919228959833730021367061 := by
  unfold tailWord_2685288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970249747833830761824259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65293666330445107682432345 48970249747833830761824259)
  ·
    refine ⟨73455374621750746142736389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48970249747833830761824259 73455374621750746142736389)
    ·
      refine ⟨13772882741578264901763073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73455374621750746142736389 13772882741578264901763073)
      ·
        refine ⟨10329662056183698676322305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13772882741578264901763073 10329662056183698676322305)
        ·
          refine ⟨7747246542137774007241729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10329662056183698676322305 7747246542137774007241729)
          ·
            refine ⟨5810434906603330505431297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7747246542137774007241729 5810434906603330505431297)
            ·
              refine ⟨4357826179952497879073473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810434906603330505431297 4357826179952497879073473)
              ·
                refine ⟨3268369634964373409305105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357826179952497879073473 3268369634964373409305105)
                ·
                  refine ⟨2451277226223280056978829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268369634964373409305105 2451277226223280056978829)
                  ·
                    refine ⟨919228959833730021367061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451277226223280056978829 919228959833730021367061)
                    ·
                      rfl

theorem cell22_2685288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_2685288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685288 prefixEnd_2685288 := by exact prefixLift 2685288
  have htrace : WordTrace (prefixWord ++ tailWord_2685288) baseStart_2685288 baseEnd_2685288 := by
    simpa [prefixWord, tailWord_2685288, baseEnd_2685288] using wordTrace_append hprefix tailTrace_2685288
  have hstable : (prefixWord ++ tailWord_2685288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685288).length < 2 ^ (prefixWord ++ tailWord_2685288).sum := by decide
  have hdescent : baseEnd_2685288 < baseStart_2685288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685290 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_2685290 : Nat := 118140960795 + 2685290 * 2 ^ 59
def prefixEnd_2685290 : Nat := 4983230072969 + 3 ^ 40 * 2685290 * 2
def baseEnd_2685290 : Nat := 306409881491534227605685

theorem tailTrace_2685290 : CollatzResearch.WordTrace tailWord_2685290 prefixEnd_2685290 306409881491534227605685 := by
  unfold tailWord_2685290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485143110415103966305331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65293714961106943910147549 24485143110415103966305331)
  ·
    refine ⟨36727714665622655949457997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24485143110415103966305331 36727714665622655949457997)
    ·
      refine ⟨13772892999608495981046749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36727714665622655949457997 13772892999608495981046749)
      ·
        refine ⟨5164834874853185992892531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13772892999608495981046749 5164834874853185992892531)
        ·
          refine ⟨7747252312279778989338797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164834874853185992892531 7747252312279778989338797)
          ·
            refine ⟨2905219617104917121002049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7747252312279778989338797 2905219617104917121002049)
            ·
              refine ⟨2178914712828687840751537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905219617104917121002049 2178914712828687840751537)
              ·
                refine ⟨1634186034621515880563653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178914712828687840751537 1634186034621515880563653)
                ·
                  refine ⟨306409881491534227605685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634186034621515880563653 306409881491534227605685)
                  ·
                    rfl

theorem cell22_2685290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_2685290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685290 prefixEnd_2685290 := by exact prefixLift 2685290
  have htrace : WordTrace (prefixWord ++ tailWord_2685290) baseStart_2685290 baseEnd_2685290 := by
    simpa [prefixWord, tailWord_2685290, baseEnd_2685290] using wordTrace_append hprefix tailTrace_2685290
  have hstable : (prefixWord ++ tailWord_2685290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685290).length < 2 ^ (prefixWord ++ tailWord_2685290).sum := by decide
  have hdescent : baseEnd_2685290 < baseStart_2685290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685301 : List Nat := [1, 3, 4, 1, 2, 3, 1, 7]
def baseStart_2685301 : Nat := 118140960795 + 2685301 * 2 ^ 59
def prefixEnd_2685301 : Nat := 4983230072969 + 3 ^ 40 * 2685301 * 2
def baseEnd_2685301 : Nat := 102137045555489146754669

theorem tailTrace_2685301 : CollatzResearch.WordTrace tailWord_2685301 prefixEnd_2685301 102137045555489146754669 := by
  unfold tailWord_2685301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97940973644620564743871757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65293982429747043162581171 97940973644620564743871757)
  ·
    refine ⟨36727865116732711778951909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97940973644620564743871757 36727865116732711778951909)
    ·
      refine ⟨6886474709387383458553483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36727865116732711778951909 6886474709387383458553483)
      ·
        refine ⟨10329712064081075187830225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886474709387383458553483 10329712064081075187830225)
        ·
          refine ⟨7747284048060806390872669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10329712064081075187830225 7747284048060806390872669)
          ·
            refine ⟨2905231518022802396577251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7747284048060806390872669 2905231518022802396577251)
            ·
              refine ⟨4357847277034203594865877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905231518022802396577251 4357847277034203594865877)
              ·
                refine ⟨102137045555489146754669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4357847277034203594865877 102137045555489146754669)
                ·
                  rfl

theorem cell22_2685301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 7].length) (baseStart_2685301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685301 prefixEnd_2685301 := by exact prefixLift 2685301
  have htrace : WordTrace (prefixWord ++ tailWord_2685301) baseStart_2685301 baseEnd_2685301 := by
    simpa [prefixWord, tailWord_2685301, baseEnd_2685301] using wordTrace_append hprefix tailTrace_2685301
  have hstable : (prefixWord ++ tailWord_2685301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685301).length < 2 ^ (prefixWord ++ tailWord_2685301).sum := by decide
  have hdescent : baseEnd_2685301 < baseStart_2685301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685312 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 11]
def baseStart_2685312 : Nat := 118140960795 + 2685312 * 2 ^ 59
def prefixEnd_2685312 : Nat := 4983230072969 + 3 ^ 40 * 2685312 * 2
def baseEnd_2685312 : Nat := 306412391841400652922329

theorem tailTrace_2685312 : CollatzResearch.WordTrace tailWord_2685312 prefixEnd_2685312 306412391841400652922329 := by
  unfold tailWord_2685312
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970687423790356811261095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65294249898387142415014793 48970687423790356811261095)
  ·
    refine ⟨73456031135685535216891643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48970687423790356811261095 73456031135685535216891643)
    ·
      refine ⟨110184046703528302825337465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73456031135685535216891643 110184046703528302825337465)
      ·
        refine ⟨82638035027646227119003099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110184046703528302825337465 82638035027646227119003099)
        ·
          refine ⟨123957052541469340678504649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82638035027646227119003099 123957052541469340678504649)
          ·
            refine ⟨92967789406102005508878487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123957052541469340678504649 92967789406102005508878487)
            ·
              refine ⟨139451684109153008263317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92967789406102005508878487 139451684109153008263317731)
              ·
                refine ⟨209177526163729512394976597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139451684109153008263317731 209177526163729512394976597)
                ·
                  refine ⟨306412391841400652922329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 209177526163729512394976597 306412391841400652922329)
                  ·
                    rfl

theorem cell22_2685312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_2685312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685312 prefixEnd_2685312 := by exact prefixLift 2685312
  have htrace : WordTrace (prefixWord ++ tailWord_2685312) baseStart_2685312 baseEnd_2685312 := by
    simpa [prefixWord, tailWord_2685312, baseEnd_2685312] using wordTrace_append hprefix tailTrace_2685312
  have hstable : (prefixWord ++ tailWord_2685312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685312).length < 2 ^ (prefixWord ++ tailWord_2685312).sum := by decide
  have hdescent : baseEnd_2685312 < baseStart_2685312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685316 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2685316 : Nat := 118140960795 + 2685316 * 2 ^ 59
def prefixEnd_2685316 : Nat := 4983230072969 + 3 ^ 40 * 2685316 * 2
def baseEnd_2685316 : Nat := 919238544805947281666975

theorem tailTrace_2685316 : CollatzResearch.WordTrace tailWord_2685316 prefixEnd_2685316 919238544805947281666975 := by
  unfold tailWord_2685316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970760369783111152833901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65294347159710814870445201 48970760369783111152833901)
  ·
    refine ⟨18364035138668666682312713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48970760369783111152833901 18364035138668666682312713)
    ·
      refine ⟨13773026354001500011734535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18364035138668666682312713 13773026354001500011734535)
      ·
        refine ⟨20659539531002250017601803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13773026354001500011734535 20659539531002250017601803)
        ·
          refine ⟨30989309296503375026402705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20659539531002250017601803 30989309296503375026402705)
          ·
            refine ⟨23241981972377531269802029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30989309296503375026402705 23241981972377531269802029)
            ·
              refine ⟨8715743239641574226175761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23241981972377531269802029 8715743239641574226175761)
              ·
                refine ⟨6536807429731180669631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8715743239641574226175761 6536807429731180669631821)
                ·
                  refine ⟨2451302786149192751111933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6536807429731180669631821 2451302786149192751111933)
                  ·
                    refine ⟨919238544805947281666975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451302786149192751111933 919238544805947281666975)
                    ·
                      rfl

theorem cell22_2685316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2685316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685316 prefixEnd_2685316 := by exact prefixLift 2685316
  have htrace : WordTrace (prefixWord ++ tailWord_2685316) baseStart_2685316 baseEnd_2685316 := by
    simpa [prefixWord, tailWord_2685316, baseEnd_2685316] using wordTrace_append hprefix tailTrace_2685316
  have hstable : (prefixWord ++ tailWord_2685316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685316).length < 2 ^ (prefixWord ++ tailWord_2685316).sum := by decide
  have hdescent : baseEnd_2685316 < baseStart_2685316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685344 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_2685344 : Nat := 118140960795 + 2685344 * 2 ^ 59
def prefixEnd_2685344 : Nat := 4983230072969 + 3 ^ 40 * 2685344 * 2
def baseEnd_2685344 : Nat := 919248129778164541966889

theorem tailTrace_2685344 : CollatzResearch.WordTrace tailWord_2685344 prefixEnd_2685344 919248129778164541966889 := by
  unfold tailWord_2685344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48971270991732391543843543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65295027988976522058458057 48971270991732391543843543)
  ·
    refine ⟨73456906487598587315765315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48971270991732391543843543 73456906487598587315765315)
    ·
      refine ⟨110185359731397880973647973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73456906487598587315765315 110185359731397880973647973)
      ·
        refine ⟨20659754949637102682558995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110185359731397880973647973 20659754949637102682558995)
        ·
          refine ⟨30989632424455654023838493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20659754949637102682558995 30989632424455654023838493)
          ·
            refine ⟨11621112159170870258939435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30989632424455654023838493 11621112159170870258939435)
            ·
              refine ⟨17431668238756305388409153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11621112159170870258939435 17431668238756305388409153)
              ·
                refine ⟨13073751179067229041306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17431668238756305388409153 13073751179067229041306865)
                ·
                  refine ⟨9805313384300421780980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13073751179067229041306865 9805313384300421780980149)
                  ·
                    refine ⟨919248129778164541966889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9805313384300421780980149 919248129778164541966889)
                    ·
                      rfl

theorem cell22_2685344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_2685344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685344 prefixEnd_2685344 := by exact prefixLift 2685344
  have htrace : WordTrace (prefixWord ++ tailWord_2685344) baseStart_2685344 baseEnd_2685344 := by
    simpa [prefixWord, tailWord_2685344, baseEnd_2685344] using wordTrace_append hprefix tailTrace_2685344
  have hstable : (prefixWord ++ tailWord_2685344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685344).length < 2 ^ (prefixWord ++ tailWord_2685344).sum := by decide
  have hdescent : baseEnd_2685344 < baseStart_2685344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685408 : List Nat := [2, 1, 1, 3, 1, 1, 7, 2, 4]
def baseStart_2685408 : Nat := 118140960795 + 2685408 * 2 ^ 59
def prefixEnd_2685408 : Nat := 4983230072969 + 3 ^ 40 * 2685408 * 2
def baseEnd_2685408 : Nat := 306423346095363236122231

theorem tailTrace_2685408 : CollatzResearch.WordTrace tailWord_2685408 prefixEnd_2685408 306423346095363236122231 := by
  unfold tailWord_2685408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48972438127616461009008439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65296584170155281345344585 48972438127616461009008439)
  ·
    refine ⟨73458657191424691513512659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48972438127616461009008439 73458657191424691513512659)
    ·
      refine ⟨110187985787137037270268989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73458657191424691513512659 110187985787137037270268989)
      ·
        refine ⟨41320494670176388976350871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110187985787137037270268989 41320494670176388976350871)
        ·
          refine ⟨61980742005264583464526307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41320494670176388976350871 61980742005264583464526307)
          ·
            refine ⟨92971113007896875196789461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61980742005264583464526307 92971113007896875196789461)
            ·
              refine ⟨2179010461122583012424753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92971113007896875196789461 2179010461122583012424753)
              ·
                refine ⟨1634257845841937259318565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179010461122583012424753 1634257845841937259318565)
                ·
                  refine ⟨306423346095363236122231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634257845841937259318565 306423346095363236122231)
                  ·
                    rfl

theorem cell22_2685408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_2685408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685408 prefixEnd_2685408 := by exact prefixLift 2685408
  have htrace : WordTrace (prefixWord ++ tailWord_2685408) baseStart_2685408 baseEnd_2685408 := by
    simpa [prefixWord, tailWord_2685408, baseEnd_2685408] using wordTrace_append hprefix tailTrace_2685408
  have hstable : (prefixWord ++ tailWord_2685408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685408).length < 2 ^ (prefixWord ++ tailWord_2685408).sum := by decide
  have hdescent : baseEnd_2685408 < baseStart_2685408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685419 : List Nat := [1, 1, 1, 1, 2, 3, 6, 7]
def baseStart_2685419 : Nat := 118140960795 + 2685419 * 2 ^ 59
def prefixEnd_2685419 : Nat := 4983230072969 + 3 ^ 40 * 2685419 * 2
def baseEnd_2685419 : Nat := 102141533756765482926851

theorem tailTrace_2685419 : CollatzResearch.WordTrace tailWord_2685419 prefixEnd_2685419 102141533756765482926851 := by
  unfold tailWord_2685419
  simp only [CollatzResearch.WordTrace]
  refine ⟨97945277458193070896667311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65296851638795380597778207 97945277458193070896667311)
  ·
    refine ⟨146917916187289606345000967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97945277458193070896667311 146917916187289606345000967)
    ·
      refine ⟨220376874280934409517501451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146917916187289606345000967 220376874280934409517501451)
      ·
        refine ⟨330565311421401614276252177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220376874280934409517501451 330565311421401614276252177)
        ·
          refine ⟨247923983566051210707189133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330565311421401614276252177 247923983566051210707189133)
          ·
            refine ⟨92971493837269204015195925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247923983566051210707189133 92971493837269204015195925)
            ·
              refine ⟨4358038773621993938212309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92971493837269204015195925 4358038773621993938212309)
              ·
                refine ⟨102141533756765482926851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4358038773621993938212309 102141533756765482926851)
                ·
                  rfl

theorem cell22_2685419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 7].length) (baseStart_2685419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685419 prefixEnd_2685419 := by exact prefixLift 2685419
  have htrace : WordTrace (prefixWord ++ tailWord_2685419) baseStart_2685419 baseEnd_2685419 := by
    simpa [prefixWord, tailWord_2685419, baseEnd_2685419] using wordTrace_append hprefix tailTrace_2685419
  have hstable : (prefixWord ++ tailWord_2685419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685419).length < 2 ^ (prefixWord ++ tailWord_2685419).sum := by decide
  have hdescent : baseEnd_2685419 < baseStart_2685419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685453 : List Nat := [1, 7, 1, 1, 1, 11]
def baseStart_2685453 : Nat := 118140960795 + 2685453 * 2 ^ 59
def prefixEnd_2685453 : Nat := 4983230072969 + 3 ^ 40 * 2685453 * 2
def baseEnd_2685453 : Nat := 11349202996366970259155

theorem tailTrace_2685453 : CollatzResearch.WordTrace tailWord_2685453 prefixEnd_2685453 11349202996366970259155 := by
  unfold tailWord_2685453
  simp only [CollatzResearch.WordTrace]
  refine ⟨97946517540069894703405013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65297678360046596468936675 97946517540069894703405013)
  ·
    refine ⟨2295621504845388157111055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 97946517540069894703405013 2295621504845388157111055)
    ·
      refine ⟨3443432257268082235666583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2295621504845388157111055 3443432257268082235666583)
      ·
        refine ⟨5165148385902123353499875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443432257268082235666583 5165148385902123353499875)
        ·
          refine ⟨7747722578853185030249813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165148385902123353499875 7747722578853185030249813)
          ·
            refine ⟨11349202996366970259155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7747722578853185030249813 11349202996366970259155)
            ·
              rfl

theorem cell22_2685453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 11].length) (baseStart_2685453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685453 prefixEnd_2685453 := by exact prefixLift 2685453
  have htrace : WordTrace (prefixWord ++ tailWord_2685453) baseStart_2685453 baseEnd_2685453 := by
    simpa [prefixWord, tailWord_2685453, baseEnd_2685453] using wordTrace_append hprefix tailTrace_2685453
  have hstable : (prefixWord ++ tailWord_2685453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685453).length < 2 ^ (prefixWord ++ tailWord_2685453).sum := by decide
  have hdescent : baseEnd_2685453 < baseStart_2685453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685573 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2685573 : Nat := 118140960795 + 2685573 * 2 ^ 59
def prefixEnd_2685573 : Nat := 4983230072969 + 3 ^ 40 * 2685573 * 2
def baseEnd_2685573 : Nat := 919326521158084277991187

theorem tailTrace_2685573 : CollatzResearch.WordTrace tailWord_2685573 prefixEnd_2685573 919326521158084277991187 := by
  unfold tailWord_2685573
  simp only [CollatzResearch.WordTrace]
  refine ⟨97950894299635155197773373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65300596199756770131848915 97950894299635155197773373)
  ·
    refine ⟨36731585362363183199165015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97950894299635155197773373 36731585362363183199165015)
    ·
      refine ⟨55097378043544774798747523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36731585362363183199165015 55097378043544774798747523)
      ·
        refine ⟨82646067065317162198121285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55097378043544774798747523 82646067065317162198121285)
        ·
          refine ⟨15496137574746967912147741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82646067065317162198121285 15496137574746967912147741)
          ·
            refine ⟨5811051590530112967055403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15496137574746967912147741 5811051590530112967055403)
            ·
              refine ⟨8716577385795169450583105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811051590530112967055403 8716577385795169450583105)
              ·
                refine ⟨6537433039346377087937329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8716577385795169450583105 6537433039346377087937329)
                ·
                  refine ⟨4903074779509782815952997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537433039346377087937329 4903074779509782815952997)
                  ·
                    refine ⟨919326521158084277991187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903074779509782815952997 919326521158084277991187)
                    ·
                      rfl

theorem cell22_2685573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2685573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685573 prefixEnd_2685573 := by exact prefixLift 2685573
  have htrace : WordTrace (prefixWord ++ tailWord_2685573) baseStart_2685573 baseEnd_2685573 := by
    simpa [prefixWord, tailWord_2685573, baseEnd_2685573] using wordTrace_append hprefix tailTrace_2685573
  have hstable : (prefixWord ++ tailWord_2685573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685573).length < 2 ^ (prefixWord ++ tailWord_2685573).sum := by decide
  have hdescent : baseEnd_2685573 < baseStart_2685573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685588 : List Nat := [2, 4, 2, 2, 1, 1, 1, 9]
def baseStart_2685588 : Nat := 118140960795 + 2685588 * 2 ^ 59
def prefixEnd_2685588 : Nat := 4983230072969 + 3 ^ 40 * 2685588 * 2
def baseEnd_2685588 : Nat := 102147961773847693207349

theorem tailTrace_2685588 : CollatzResearch.WordTrace tailWord_2685588 prefixEnd_2685588 102147961773847693207349 := by
  unfold tailWord_2685588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975720697290406379784709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65300960929720541839712945 48975720697290406379784709)
  ·
    refine ⟨9182947630741951196209633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48975720697290406379784709 9182947630741951196209633)
    ·
      refine ⟨6887210723056463397157225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9182947630741951196209633 6887210723056463397157225)
      ·
        refine ⟨5165408042292347547867919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887210723056463397157225 5165408042292347547867919)
        ·
          refine ⟨7748112063438521321801879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165408042292347547867919 7748112063438521321801879)
          ·
            refine ⟨11622168095157781982702819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748112063438521321801879 11622168095157781982702819)
            ·
              refine ⟨17433252142736672974054229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11622168095157781982702819 17433252142736672974054229)
              ·
                refine ⟨102147961773847693207349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17433252142736672974054229 102147961773847693207349)
                ·
                  rfl

theorem cell22_2685588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 9].length) (baseStart_2685588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685588 prefixEnd_2685588 := by exact prefixLift 2685588
  have htrace : WordTrace (prefixWord ++ tailWord_2685588) baseStart_2685588 baseEnd_2685588 := by
    simpa [prefixWord, tailWord_2685588, baseEnd_2685588] using wordTrace_append hprefix tailTrace_2685588
  have hstable : (prefixWord ++ tailWord_2685588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685588).length < 2 ^ (prefixWord ++ tailWord_2685588).sum := by decide
  have hdescent : baseEnd_2685588 < baseStart_2685588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685607 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2685607 : Nat := 118140960795 + 2685607 * 2 ^ 59
def prefixEnd_2685607 : Nat := 4983230072969 + 3 ^ 40 * 2685607 * 2
def baseEnd_2685607 : Nat := 919338160052919522641083

theorem tailTrace_2685607 : CollatzResearch.WordTrace tailWord_2685607 prefixEnd_2685607 919338160052919522641083 := by
  unfold tailWord_2685607
  simp only [CollatzResearch.WordTrace]
  refine ⟨97952134381511979004511075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65301422921007986003007383 97952134381511979004511075)
  ·
    refine ⟨146928201572267968506766613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97952134381511979004511075 146928201572267968506766613)
    ·
      refine ⟨6887259448700061023754685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146928201572267968506766613 6887259448700061023754685)
      ·
        refine ⟨2582722293262522883908007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6887259448700061023754685 2582722293262522883908007)
        ·
          refine ⟨3874083439893784325862011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582722293262522883908007 3874083439893784325862011)
          ·
            refine ⟨5811125159840676488793017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874083439893784325862011 5811125159840676488793017)
            ·
              refine ⟨4358343869880507366594763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811125159840676488793017 4358343869880507366594763)
              ·
                refine ⟨6537515804820761049892145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358343869880507366594763 6537515804820761049892145)
                ·
                  refine ⟨4903136853615570787419109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537515804820761049892145 4903136853615570787419109)
                  ·
                    refine ⟨919338160052919522641083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903136853615570787419109 919338160052919522641083)
                    ·
                      rfl

theorem cell22_2685607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2685607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685607 prefixEnd_2685607 := by exact prefixLift 2685607
  have htrace : WordTrace (prefixWord ++ tailWord_2685607) baseStart_2685607 baseEnd_2685607 := by
    simpa [prefixWord, tailWord_2685607, baseEnd_2685607] using wordTrace_append hprefix tailTrace_2685607
  have hstable : (prefixWord ++ tailWord_2685607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685607).length < 2 ^ (prefixWord ++ tailWord_2685607).sum := by decide
  have hdescent : baseEnd_2685607 < baseStart_2685607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685663 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 3, 4]
def baseStart_2685663 : Nat := 118140960795 + 2685663 * 2 ^ 59
def prefixEnd_2685663 : Nat := 4983230072969 + 3 ^ 40 * 2685663 * 2
def baseEnd_2685663 : Nat := 919357329997354043240911

theorem tailTrace_2685663 : CollatzResearch.WordTrace tailWord_2685663 prefixEnd_2685663 919357329997354043240911 := by
  unfold tailWord_2685663
  simp only [CollatzResearch.WordTrace]
  refine ⟨97954176869309100568549643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65302784579539400379033095 97954176869309100568549643)
  ·
    refine ⟨146931265303963650852824465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97954176869309100568549643 146931265303963650852824465)
    ·
      refine ⟨110198448977972738139618349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146931265303963650852824465 110198448977972738139618349)
      ·
        refine ⟨41324418366739776802356881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110198448977972738139618349 41324418366739776802356881)
        ·
          refine ⟨30993313775054832601767661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41324418366739776802356881 30993313775054832601767661)
          ·
            refine ⟨11622492665645562225662873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30993313775054832601767661 11622492665645562225662873)
            ·
              refine ⟨8716869499234171669247155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11622492665645562225662873 8716869499234171669247155)
              ·
                refine ⟨13075304248851257503870733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8716869499234171669247155 13075304248851257503870733)
                ·
                  refine ⟨4903239093319221563951525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075304248851257503870733 4903239093319221563951525)
                  ·
                    refine ⟨919357329997354043240911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903239093319221563951525 919357329997354043240911)
                    ·
                      rfl

theorem cell22_2685663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_2685663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685663 prefixEnd_2685663 := by exact prefixLift 2685663
  have htrace : WordTrace (prefixWord ++ tailWord_2685663) baseStart_2685663 baseEnd_2685663 := by
    simpa [prefixWord, tailWord_2685663, baseEnd_2685663] using wordTrace_append hprefix tailTrace_2685663
  have hstable : (prefixWord ++ tailWord_2685663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685663).length < 2 ^ (prefixWord ++ tailWord_2685663).sum := by decide
  have hdescent : baseEnd_2685663 < baseStart_2685663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685714 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2685714 : Nat := 118140960795 + 2685714 * 2 ^ 59
def prefixEnd_2685714 : Nat := 4983230072969 + 3 ^ 40 * 2685714 * 2
def baseEnd_2685714 : Nat := 919374788339606910215755

theorem tailTrace_2685714 : CollatzResearch.WordTrace tailWord_2685714 prefixEnd_2685714 919374788339606910215755 := by
  unfold tailWord_2685714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489009248031084069664049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65304024661416224185770797 24489009248031084069664049)
  ·
    refine ⟨18366756936023313052248037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24489009248031084069664049 18366756936023313052248037)
    ·
      refine ⟨3443766925504371197296507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18366756936023313052248037 3443766925504371197296507)
      ·
        refine ⟨5165650388256556795944761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443766925504371197296507 5165650388256556795944761)
        ·
          refine ⟨3874237791192417596958571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5165650388256556795944761 3874237791192417596958571)
          ·
            refine ⟨5811356686788626395437857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874237791192417596958571 5811356686788626395437857)
            ·
              refine ⟨4358517515091469796578393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811356686788626395437857 4358517515091469796578393)
              ·
                refine ⟨3268888136318602347433795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358517515091469796578393 3268888136318602347433795)
                ·
                  refine ⟨4903332204477903521150693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268888136318602347433795 4903332204477903521150693)
                  ·
                    refine ⟨919374788339606910215755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903332204477903521150693 919374788339606910215755)
                    ·
                      rfl

theorem cell22_2685714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2685714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685714 prefixEnd_2685714 := by exact prefixLift 2685714
  have htrace : WordTrace (prefixWord ++ tailWord_2685714) baseStart_2685714 baseEnd_2685714 := by
    simpa [prefixWord, tailWord_2685714, baseEnd_2685714] using wordTrace_append hprefix tailTrace_2685714
  have hstable : (prefixWord ++ tailWord_2685714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685714).length < 2 ^ (prefixWord ++ tailWord_2685714).sum := by decide
  have hdescent : baseEnd_2685714 < baseStart_2685714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685742 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2685742 : Nat := 118140960795 + 2685742 * 2 ^ 59
def prefixEnd_2685742 : Nat := 4983230072969 + 3 ^ 40 * 2685742 * 2
def baseEnd_2685742 : Nat := 919384373311824170515669

theorem tailTrace_2685742 : CollatzResearch.WordTrace tailWord_2685742 prefixEnd_2685742 919384373311824170515669 := by
  unfold tailWord_2685742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244632279502862132584435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65304705490681931373783653 12244632279502862132584435)
  ·
    refine ⟨18366948419254293198876653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244632279502862132584435 18366948419254293198876653)
    ·
      refine ⟨6887605657220359949578745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18366948419254293198876653 6887605657220359949578745)
      ·
        refine ⟨5165704242915269962184059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887605657220359949578745 5165704242915269962184059)
        ·
          refine ⟨7748556364372904943276089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165704242915269962184059 7748556364372904943276089)
          ·
            refine ⟨5811417273279678707457067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7748556364372904943276089 5811417273279678707457067)
            ·
              refine ⟨8717125909919518061185601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811417273279678707457067 8717125909919518061185601)
              ·
                refine ⟨6537844432439638545889201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8717125909919518061185601 6537844432439638545889201)
                ·
                  refine ⟨4903383324329728909416901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537844432439638545889201 4903383324329728909416901)
                  ·
                    refine ⟨919384373311824170515669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903383324329728909416901 919384373311824170515669)
                    ·
                      rfl

theorem cell22_2685742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2685742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685742 prefixEnd_2685742 := by exact prefixLift 2685742
  have htrace : WordTrace (prefixWord ++ tailWord_2685742) baseStart_2685742 baseEnd_2685742 := by
    simpa [prefixWord, tailWord_2685742, baseEnd_2685742] using wordTrace_append hprefix tailTrace_2685742
  have hstable : (prefixWord ++ tailWord_2685742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685742).length < 2 ^ (prefixWord ++ tailWord_2685742).sum := by decide
  have hdescent : baseEnd_2685742 < baseStart_2685742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685806 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2685806 : Nat := 118140960795 + 2685806 * 2 ^ 59
def prefixEnd_2685806 : Nat := 4983230072969 + 3 ^ 40 * 2685806 * 2
def baseEnd_2685806 : Nat := 919406281819749336915473

theorem tailTrace_2685806 : CollatzResearch.WordTrace tailWord_2685806 prefixEnd_2685806 919406281819749336915473 := by
  unfold tailWord_2685806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244924063473879498875659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65306261671860690660670181 12244924063473879498875659)
  ·
    refine ⟨18367386095210819248313489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244924063473879498875659 18367386095210819248313489)
    ·
      refine ⟨13775539571408114436235117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18367386095210819248313489 13775539571408114436235117)
      ·
        refine ⟨5165827339278042913588169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13775539571408114436235117 5165827339278042913588169)
        ·
          refine ⟨3874370504458532185191127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5165827339278042913588169 3874370504458532185191127)
          ·
            refine ⟨5811555756687798277786691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874370504458532185191127 5811555756687798277786691)
            ·
              refine ⟨8717333635031697416680037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811555756687798277786691 8717333635031697416680037)
              ·
                refine ⟨1634500056568443265627507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8717333635031697416680037 1634500056568443265627507)
                ·
                  refine ⟨2451750084852664898441261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634500056568443265627507 2451750084852664898441261)
                  ·
                    refine ⟨919406281819749336915473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2451750084852664898441261 919406281819749336915473)
                    ·
                      rfl

theorem cell22_2685806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2685806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685806 prefixEnd_2685806 := by exact prefixLift 2685806
  have htrace : WordTrace (prefixWord ++ tailWord_2685806) baseStart_2685806 baseEnd_2685806 := by
    simpa [prefixWord, tailWord_2685806, baseEnd_2685806] using wordTrace_append hprefix tailTrace_2685806
  have hstable : (prefixWord ++ tailWord_2685806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685806).length < 2 ^ (prefixWord ++ tailWord_2685806).sum := by decide
  have hdescent : baseEnd_2685806 < baseStart_2685806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685845 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2685845 : Nat := 118140960795 + 2685845 * 2 ^ 59
def prefixEnd_2685845 : Nat := 4983230072969 + 3 ^ 40 * 2685845 * 2
def baseEnd_2685845 : Nat := 919419632316766235190353

theorem tailTrace_2685845 : CollatzResearch.WordTrace tailWord_2685845 prefixEnd_2685845 919419632316766235190353 := by
  unfold tailWord_2685845
  simp only [CollatzResearch.WordTrace]
  refine ⟨97960814954649745651674989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65307209969766497101116659 97960814954649745651674989)
  ·
    refine ⟨36735305607993654619378121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97960814954649745651674989 36735305607993654619378121)
    ·
      refine ⟨27551479205995240964533591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36735305607993654619378121 27551479205995240964533591)
      ·
        refine ⟨41327218808992861446800387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27551479205995240964533591 41327218808992861446800387)
        ·
          refine ⟨61990828213489292170200581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41327218808992861446800387 61990828213489292170200581)
          ·
            refine ⟨11623280290029242281912609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61990828213489292170200581 11623280290029242281912609)
            ·
              refine ⟨8717460217521931711434457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11623280290029242281912609 8717460217521931711434457)
              ·
                refine ⟨6538095163141448783575843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8717460217521931711434457 6538095163141448783575843)
                ·
                  refine ⟨9807142744712173175363765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538095163141448783575843 9807142744712173175363765)
                  ·
                    refine ⟨919419632316766235190353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9807142744712173175363765 919419632316766235190353)
                    ·
                      rfl

theorem cell22_2685845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2685845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685845 prefixEnd_2685845 := by exact prefixLift 2685845
  have htrace : WordTrace (prefixWord ++ tailWord_2685845) baseStart_2685845 baseEnd_2685845 := by
    simpa [prefixWord, tailWord_2685845, baseEnd_2685845] using wordTrace_append hprefix tailTrace_2685845
  have hstable : (prefixWord ++ tailWord_2685845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685845).length < 2 ^ (prefixWord ++ tailWord_2685845).sum := by decide
  have hdescent : baseEnd_2685845 < baseStart_2685845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685847 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 4]
def baseStart_2685847 : Nat := 118140960795 + 2685847 * 2 ^ 59
def prefixEnd_2685847 : Nat := 4983230072969 + 3 ^ 40 * 2685847 * 2
def baseEnd_2685847 : Nat := 306473438985879632213449

theorem tailTrace_2685847 : CollatzResearch.WordTrace tailWord_2685847 prefixEnd_2685847 306473438985879632213449 := by
  unfold tailWord_2685847
  simp only [CollatzResearch.WordTrace]
  refine ⟨97960887900642499993247795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65307258600428333328831863 97960887900642499993247795)
  ·
    refine ⟨146941331850963749989871693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97960887900642499993247795 146941331850963749989871693)
    ·
      refine ⟨55102999444111406246201885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146941331850963749989871693 55102999444111406246201885)
      ·
        refine ⟨20663624791541777342325707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55102999444111406246201885 20663624791541777342325707)
        ·
          refine ⟨30995437187312666013488561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20663624791541777342325707 30995437187312666013488561)
          ·
            refine ⟨23246577890484499510116421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30995437187312666013488561 23246577890484499510116421)
            ·
              refine ⟨4358733354465843658146829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23246577890484499510116421 4358733354465843658146829)
              ·
                refine ⟨1634525007924691371805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4358733354465843658146829 1634525007924691371805061)
                ·
                  refine ⟨306473438985879632213449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634525007924691371805061 306473438985879632213449)
                  ·
                    rfl

theorem cell22_2685847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 4].length) (baseStart_2685847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685847 prefixEnd_2685847 := by exact prefixLift 2685847
  have htrace : WordTrace (prefixWord ++ tailWord_2685847) baseStart_2685847 baseEnd_2685847 := by
    simpa [prefixWord, tailWord_2685847, baseEnd_2685847] using wordTrace_append hprefix tailTrace_2685847
  have hstable : (prefixWord ++ tailWord_2685847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685847).length < 2 ^ (prefixWord ++ tailWord_2685847).sum := by decide
  have hdescent : baseEnd_2685847 < baseStart_2685847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685860 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_2685860 : Nat := 118140960795 + 2685860 * 2 ^ 59
def prefixEnd_2685860 : Nat := 4983230072969 + 3 ^ 40 * 2685860 * 2
def baseEnd_2685860 : Nat := 919424767123311196065307

theorem tailTrace_2685860 : CollatzResearch.WordTrace tailWord_2685860 prefixEnd_2685860 919424767123311196065307 := by
  unfold tailWord_2685860
  simp only [CollatzResearch.WordTrace]
  refine ⟨48980681024797701606735517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65307574699730268808980689 48980681024797701606735517)
  ·
    refine ⟨18367755384299138102525819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48980681024797701606735517 18367755384299138102525819)
    ·
      refine ⟨27551633076448707153788729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18367755384299138102525819 27551633076448707153788729)
      ·
        refine ⟨20663724807336530365341547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27551633076448707153788729 20663724807336530365341547)
        ·
          refine ⟨30995587211004795548012321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20663724807336530365341547 30995587211004795548012321)
          ·
            refine ⟨23246690408253596661009241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30995587211004795548012321 23246690408253596661009241)
            ·
              refine ⟨17435017806190197495756931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23246690408253596661009241 17435017806190197495756931)
              ·
                refine ⟨26152526709285296243635397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17435017806190197495756931 26152526709285296243635397)
                ·
                  refine ⟨4903598757990993045681637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26152526709285296243635397 4903598757990993045681637)
                  ·
                    refine ⟨919424767123311196065307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903598757990993045681637 919424767123311196065307)
                    ·
                      rfl

theorem cell22_2685860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_2685860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685860 prefixEnd_2685860 := by exact prefixLift 2685860
  have htrace : WordTrace (prefixWord ++ tailWord_2685860) baseStart_2685860 baseEnd_2685860 := by
    simpa [prefixWord, tailWord_2685860, baseEnd_2685860] using wordTrace_append hprefix tailTrace_2685860
  have hstable : (prefixWord ++ tailWord_2685860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685860).length < 2 ^ (prefixWord ++ tailWord_2685860).sum := by decide
  have hdescent : baseEnd_2685860 < baseStart_2685860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685937 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 5]
def baseStart_2685937 : Nat := 118140960795 + 2685937 * 2 ^ 59
def prefixEnd_2685937 : Nat := 4983230072969 + 3 ^ 40 * 2685937 * 2
def baseEnd_2685937 : Nat := 306483708598969553963357

theorem tailTrace_2685937 : CollatzResearch.WordTrace tailWord_2685937 prefixEnd_2685937 306483708598969553963357 := by
  unfold tailWord_2685937
  simp only [CollatzResearch.WordTrace]
  refine ⟨97964170470316445364024065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65309446980210963576016043 97964170470316445364024065)
  ·
    refine ⟨73473127852737334023018049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97964170470316445364024065 73473127852737334023018049)
    ·
      refine ⟨55104845889553000517263537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73473127852737334023018049 55104845889553000517263537)
      ·
        refine ⟨41328634417164750387947653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55104845889553000517263537 41328634417164750387947653)
        ·
          refine ⟨7749118953218390697740185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41328634417164750387947653 7749118953218390697740185)
          ·
            refine ⟨5811839214913793023305139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7749118953218390697740185 5811839214913793023305139)
            ·
              refine ⟨8717758822370689534957709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811839214913793023305139 8717758822370689534957709)
              ·
                refine ⟨3269159558389008575609141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8717758822370689534957709 3269159558389008575609141)
                ·
                  refine ⟨306483708598969553963357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3269159558389008575609141 306483708598969553963357)
                  ·
                    rfl

theorem cell22_2685937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 5].length) (baseStart_2685937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685937 prefixEnd_2685937 := by exact prefixLift 2685937
  have htrace : WordTrace (prefixWord ++ tailWord_2685937) baseStart_2685937 baseEnd_2685937 := by
    simpa [prefixWord, tailWord_2685937, baseEnd_2685937] using wordTrace_append hprefix tailTrace_2685937
  have hstable : (prefixWord ++ tailWord_2685937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685937).length < 2 ^ (prefixWord ++ tailWord_2685937).sum := by decide
  have hdescent : baseEnd_2685937 < baseStart_2685937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685995 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 6]
def baseStart_2685995 : Nat := 118140960795 + 2685995 * 2 ^ 59
def prefixEnd_2685995 : Nat := 4983230072969 + 3 ^ 40 * 2685995 * 2
def baseEnd_2685995 : Nat := 919470980382215843939893

theorem tailTrace_2685995 : CollatzResearch.WordTrace tailWord_2685995 prefixEnd_2685995 919470980382215843939893 := by
  unfold tailWord_2685995
  simp only [CollatzResearch.WordTrace]
  refine ⟨97966285904106321269635439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65310857269404214179756959 97966285904106321269635439)
  ·
    refine ⟨146949428856159481904453159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97966285904106321269635439 146949428856159481904453159)
    ·
      refine ⟨220424143284239222856679739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146949428856159481904453159 220424143284239222856679739)
      ·
        refine ⟨330636214926358834285019609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220424143284239222856679739 330636214926358834285019609)
        ·
          refine ⟨247977161194769125713764707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330636214926358834285019609 247977161194769125713764707)
          ·
            refine ⟨371965741792153688570647061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247977161194769125713764707 371965741792153688570647061)
            ·
              refine ⟨17435894146507204151749081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 371965741792153688570647061 17435894146507204151749081)
              ·
                refine ⟨13076920609880403113811811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17435894146507204151749081 13076920609880403113811811)
                ·
                  refine ⟨19615380914820604670717717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13076920609880403113811811 19615380914820604670717717)
                  ·
                    refine ⟨919470980382215843939893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19615380914820604670717717 919470980382215843939893)
                    ·
                      rfl

theorem cell22_2685995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_2685995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2685995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2685995 prefixEnd_2685995 := by exact prefixLift 2685995
  have htrace : WordTrace (prefixWord ++ tailWord_2685995) baseStart_2685995 baseEnd_2685995 := by
    simpa [prefixWord, tailWord_2685995, baseEnd_2685995] using wordTrace_append hprefix tailTrace_2685995
  have hstable : (prefixWord ++ tailWord_2685995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685995).length < 2 ^ (prefixWord ++ tailWord_2685995).sum := by decide
  have hdescent : baseEnd_2685995 < baseStart_2685995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686010 : List Nat := [3, 1, 1, 1, 3, 1, 2, 10]
def baseStart_2686010 : Nat := 118140960795 + 2686010 * 2 ^ 59
def prefixEnd_2686010 : Nat := 4983230072969 + 3 ^ 40 * 2686010 * 2
def baseEnd_2686010 : Nat := 102164012798751200534983

theorem tailTrace_2686010 : CollatzResearch.WordTrace tailWord_2686010 prefixEnd_2686010 102164012798751200534983 := by
  unfold tailWord_2686010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24491708249762994707857871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65311221999367985887620989 24491708249762994707857871)
  ·
    refine ⟨36737562374644492061786807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24491708249762994707857871 36737562374644492061786807)
    ·
      refine ⟨55106343561966738092680211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36737562374644492061786807 55106343561966738092680211)
      ·
        refine ⟨82659515342950107139020317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55106343561966738092680211 82659515342950107139020317)
        ·
          refine ⟨30997318253606290177132619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82659515342950107139020317 30997318253606290177132619)
          ·
            refine ⟨46495977380409435265698929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30997318253606290177132619 46495977380409435265698929)
            ·
              refine ⟨34871983035307076449274197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46495977380409435265698929 34871983035307076449274197)
              ·
                refine ⟨102164012798751200534983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34871983035307076449274197 102164012798751200534983)
                ·
                  rfl

theorem cell22_2686010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_2686010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686010 prefixEnd_2686010 := by exact prefixLift 2686010
  have htrace : WordTrace (prefixWord ++ tailWord_2686010) baseStart_2686010 baseEnd_2686010 := by
    simpa [prefixWord, tailWord_2686010, baseEnd_2686010] using wordTrace_append hprefix tailTrace_2686010
  have hstable : (prefixWord ++ tailWord_2686010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686010).length < 2 ^ (prefixWord ++ tailWord_2686010).sum := by decide
  have hdescent : baseEnd_2686010 < baseStart_2686010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686012 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2686012 : Nat := 118140960795 + 2686012 * 2 ^ 59
def prefixEnd_2686012 : Nat := 4983230072969 + 3 ^ 40 * 2686012 * 2
def baseEnd_2686012 : Nat := 919476799829633466264841

theorem tailTrace_2686012 : CollatzResearch.WordTrace tailWord_2686012 prefixEnd_2686012 919476799829633466264841 := by
  unfold tailWord_2686012
  simp only [CollatzResearch.WordTrace]
  refine ⟨48983452972522366586502145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65311270630029822115336193 48983452972522366586502145)
  ·
    refine ⟨36737589729391774939876609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48983452972522366586502145 36737589729391774939876609)
    ·
      refine ⟨27553192297043831204907457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36737589729391774939876609 27553192297043831204907457)
      ·
        refine ⟨20664894222782873403680593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27553192297043831204907457 20664894222782873403680593)
        ·
          refine ⟨15498670667087155052760445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20664894222782873403680593 15498670667087155052760445)
          ·
            refine ⟨5812001500157683144785167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15498670667087155052760445 5812001500157683144785167)
            ·
              refine ⟨8718002250236524717177751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812001500157683144785167 8718002250236524717177751)
              ·
                refine ⟨13077003375354787075766627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718002250236524717177751 13077003375354787075766627)
                ·
                  refine ⟨19615505063032180613649941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13077003375354787075766627 19615505063032180613649941)
                  ·
                    refine ⟨919476799829633466264841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19615505063032180613649941 919476799829633466264841)
                    ·
                      rfl

theorem cell22_2686012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2686012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686012 prefixEnd_2686012 := by exact prefixLift 2686012
  have htrace : WordTrace (prefixWord ++ tailWord_2686012) baseStart_2686012 baseEnd_2686012 := by
    simpa [prefixWord, tailWord_2686012, baseEnd_2686012] using wordTrace_append hprefix tailTrace_2686012
  have hstable : (prefixWord ++ tailWord_2686012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686012).length < 2 ^ (prefixWord ++ tailWord_2686012).sum := by decide
  have hdescent : baseEnd_2686012 < baseStart_2686012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686014 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2686014 : Nat := 118140960795 + 2686014 * 2 ^ 59
def prefixEnd_2686014 : Nat := 4983230072969 + 3 ^ 40 * 2686014 * 2
def baseEnd_2686014 : Nat := 919477484470506127714835

theorem tailTrace_2686014 : CollatzResearch.WordTrace tailWord_2686014 prefixEnd_2686014 919477484470506127714835 := by
  unfold tailWord_2686014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245872361379685939322137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65311319260691658343051397 12245872361379685939322137)
  ·
    refine ⟨9184404271034764454491603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245872361379685939322137 9184404271034764454491603)
    ·
      refine ⟨13776606406552146681737405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184404271034764454491603 13776606406552146681737405)
      ·
        refine ⟨5166227402457055005651527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13776606406552146681737405 5166227402457055005651527)
        ·
          refine ⟨7749341103685582508477291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166227402457055005651527 7749341103685582508477291)
          ·
            refine ⟨11624011655528373762715937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749341103685582508477291 11624011655528373762715937)
            ·
              refine ⟨8718008741646280322036953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11624011655528373762715937 8718008741646280322036953)
              ·
                refine ⟨6538506556234710241527715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718008741646280322036953 6538506556234710241527715)
                ·
                  refine ⟨9807759834352065362291573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538506556234710241527715 9807759834352065362291573)
                  ·
                    refine ⟨919477484470506127714835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9807759834352065362291573 919477484470506127714835)
                    ·
                      rfl

theorem cell22_2686014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2686014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686014 prefixEnd_2686014 := by exact prefixLift 2686014
  have htrace : WordTrace (prefixWord ++ tailWord_2686014) baseStart_2686014 baseEnd_2686014 := by
    simpa [prefixWord, tailWord_2686014, baseEnd_2686014] using wordTrace_append hprefix tailTrace_2686014
  have hstable : (prefixWord ++ tailWord_2686014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686014).length < 2 ^ (prefixWord ++ tailWord_2686014).sum := by decide
  have hdescent : baseEnd_2686014 < baseStart_2686014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686046 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2686046 : Nat := 118140960795 + 2686046 * 2 ^ 59
def prefixEnd_2686046 : Nat := 4983230072969 + 3 ^ 40 * 2686046 * 2
def baseEnd_2686046 : Nat := 919488438724468710914737

theorem tailTrace_2686046 : CollatzResearch.WordTrace tailWord_2686046 prefixEnd_2686046 919488438724468710914737 := by
  unfold tailWord_2686046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246018253365194622467749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65312097351281037986494661 12246018253365194622467749)
  ·
    refine ⟨2296128422505973991712703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12246018253365194622467749 2296128422505973991712703)
    ·
      refine ⟨3444192633758960987569055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2296128422505973991712703 3444192633758960987569055)
      ·
        refine ⟨5166288950638441481353583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444192633758960987569055 5166288950638441481353583)
        ·
          refine ⟨7749433425957662222030375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166288950638441481353583 7749433425957662222030375)
          ·
            refine ⟨11624150138936493333045563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749433425957662222030375 11624150138936493333045563)
            ·
              refine ⟨17436225208404739999568345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11624150138936493333045563 17436225208404739999568345)
              ·
                refine ⟨13077168906303554999676259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17436225208404739999568345 13077168906303554999676259)
                ·
                  refine ⟨19615753359455332499514389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13077168906303554999676259 19615753359455332499514389)
                  ·
                    refine ⟨919488438724468710914737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19615753359455332499514389 919488438724468710914737)
                    ·
                      rfl

theorem cell22_2686046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2686046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686046 prefixEnd_2686046 := by exact prefixLift 2686046
  have htrace : WordTrace (prefixWord ++ tailWord_2686046) baseStart_2686046 baseEnd_2686046 := by
    simpa [prefixWord, tailWord_2686046, baseEnd_2686046] using wordTrace_append hprefix tailTrace_2686046
  have hstable : (prefixWord ++ tailWord_2686046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686046).length < 2 ^ (prefixWord ++ tailWord_2686046).sum := by decide
  have hdescent : baseEnd_2686046 < baseStart_2686046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686078 : List Nat := [4, 2, 4, 1, 1, 2, 8]
def baseStart_2686078 : Nat := 118140960795 + 2686078 * 2 ^ 59
def prefixEnd_2686078 : Nat := 4983230072969 + 3 ^ 40 * 2686078 * 2
def baseEnd_2686078 : Nat := 34055533073275233115357

theorem tailTrace_2686078 : CollatzResearch.WordTrace tailWord_2686078 prefixEnd_2686078 34055533073275233115357 := by
  unfold tailWord_2686078
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246164145350703305613361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65312875441870417629937925 12246164145350703305613361)
  ·
    refine ⟨9184623109013027479210021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12246164145350703305613361 9184623109013027479210021)
    ·
      refine ⟨1722116832939942652351879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9184623109013027479210021 1722116832939942652351879)
      ·
        refine ⟨2583175249409913978527819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722116832939942652351879 2583175249409913978527819)
        ·
          refine ⟨3874762874114870967791729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583175249409913978527819 3874762874114870967791729)
          ·
            refine ⟨2906072155586153225843797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874762874114870967791729 2906072155586153225843797)
            ·
              refine ⟨34055533073275233115357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2906072155586153225843797 34055533073275233115357)
              ·
                rfl

theorem cell22_2686078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 8].length) (baseStart_2686078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686078 prefixEnd_2686078 := by exact prefixLift 2686078
  have htrace : WordTrace (prefixWord ++ tailWord_2686078) baseStart_2686078 baseEnd_2686078 := by
    simpa [prefixWord, tailWord_2686078, baseEnd_2686078] using wordTrace_append hprefix tailTrace_2686078
  have hstable : (prefixWord ++ tailWord_2686078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686078).length < 2 ^ (prefixWord ++ tailWord_2686078).sum := by decide
  have hdescent : baseEnd_2686078 < baseStart_2686078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686106 : List Nat := [3, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_2686106 : Nat := 118140960795 + 2686106 * 2 ^ 59
def prefixEnd_2686106 : Nat := 4983230072969 + 3 ^ 40 * 2686106 * 2
def baseEnd_2686106 : Nat := 306502992650216184804851

theorem tailTrace_2686106 : CollatzResearch.WordTrace tailWord_2686106 prefixEnd_2686106 306502992650216184804851 := by
  unfold tailWord_2686106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492583601676046806731543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65313556271136124817950781 24492583601676046806731543)
  ·
    refine ⟨36738875402514070210097315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24492583601676046806731543 36738875402514070210097315)
    ·
      refine ⟨55108313103771105315145973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36738875402514070210097315 55108313103771105315145973)
      ·
        refine ⟨5166404353478541123294935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55108313103771105315145973 5166404353478541123294935)
        ·
          refine ⟨7749606530217811684942403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166404353478541123294935 7749606530217811684942403)
          ·
            refine ⟨11624409795326717527413605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749606530217811684942403 11624409795326717527413605)
            ·
              refine ⟨2179576836623759536390051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11624409795326717527413605 2179576836623759536390051)
              ·
                refine ⟨3269365254935639304585077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179576836623759536390051 3269365254935639304585077)
                ·
                  refine ⟨306502992650216184804851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3269365254935639304585077 306502992650216184804851)
                  ·
                    rfl

theorem cell22_2686106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_2686106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686106 prefixEnd_2686106 := by exact prefixLift 2686106
  have htrace : WordTrace (prefixWord ++ tailWord_2686106) baseStart_2686106 baseEnd_2686106 := by
    simpa [prefixWord, tailWord_2686106, baseEnd_2686106] using wordTrace_append hprefix tailTrace_2686106
  have hstable : (prefixWord ++ tailWord_2686106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686106).length < 2 ^ (prefixWord ++ tailWord_2686106).sum := by decide
  have hdescent : baseEnd_2686106 < baseStart_2686106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 4, 4]
def baseStart_2686147 : Nat := 118140960795 + 2686147 * 2 ^ 59
def prefixEnd_2686147 : Nat := 4983230072969 + 3 ^ 40 * 2686147 * 2
def baseEnd_2686147 : Nat := 919523013088538114139427

theorem tailTrace_2686147 : CollatzResearch.WordTrace tailWord_2686147 prefixEnd_2686147 919523013088538114139427 := by
  unfold tailWord_2686147
  simp only [CollatzResearch.WordTrace]
  refine ⟨97971829799555651229168695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65314553199703767486112463 97971829799555651229168695)
  ·
    refine ⟨146957744699333476843753043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97971829799555651229168695 146957744699333476843753043)
    ·
      refine ⟨220436617049000215265629565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146957744699333476843753043 220436617049000215265629565)
      ·
        refine ⟨82663731393375080724611087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220436617049000215265629565 82663731393375080724611087)
        ·
          refine ⟨123995597090062621086916631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82663731393375080724611087 123995597090062621086916631)
          ·
            refine ⟨185993395635093931630374947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123995597090062621086916631 185993395635093931630374947)
            ·
              refine ⟨278990093452640897445562421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185993395635093931630374947 278990093452640897445562421)
              ·
                refine ⟨26155321261185084135521477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278990093452640897445562421 26155321261185084135521477)
                ·
                  refine ⟨4904122736472203275410277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26155321261185084135521477 4904122736472203275410277)
                  ·
                    refine ⟨919523013088538114139427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904122736472203275410277 919523013088538114139427)
                    ·
                      rfl

theorem cell22_2686147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 4].length) (baseStart_2686147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686147 prefixEnd_2686147 := by exact prefixLift 2686147
  have htrace : WordTrace (prefixWord ++ tailWord_2686147) baseStart_2686147 baseEnd_2686147 := by
    simpa [prefixWord, tailWord_2686147, baseEnd_2686147] using wordTrace_append hprefix tailTrace_2686147
  have hstable : (prefixWord ++ tailWord_2686147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686147).length < 2 ^ (prefixWord ++ tailWord_2686147).sum := by decide
  have hdescent : baseEnd_2686147 < baseStart_2686147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686211 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 3, 3]
def baseStart_2686211 : Nat := 118140960795 + 2686211 * 2 ^ 59
def prefixEnd_2686211 : Nat := 4983230072969 + 3 ^ 40 * 2686211 * 2
def baseEnd_2686211 : Nat := 919544921596463280539231

theorem tailTrace_2686211 : CollatzResearch.WordTrace tailWord_2686211 prefixEnd_2686211 919544921596463280539231 := by
  unfold tailWord_2686211
  simp only [CollatzResearch.WordTrace]
  refine ⟨97974164071323790159498487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65316109380882526772998991 97974164071323790159498487)
  ·
    refine ⟨146961246106985685239247731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97974164071323790159498487 146961246106985685239247731)
    ·
      refine ⟨220441869160478527858871597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146961246106985685239247731 220441869160478527858871597)
      ·
        refine ⟨82665700935179447947076849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220441869160478527858871597 82665700935179447947076849)
        ·
          refine ⟨61999275701384585960307637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82665700935179447947076849 61999275701384585960307637)
          ·
            refine ⟨5812432097004804933778841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61999275701384585960307637 5812432097004804933778841)
            ·
              refine ⟨4359324072753603700334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812432097004804933778841 4359324072753603700334131)
              ·
                refine ⟨6538986109130405550501197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359324072753603700334131 6538986109130405550501197)
                ·
                  refine ⟨2452119790923902081437949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6538986109130405550501197 2452119790923902081437949)
                  ·
                    refine ⟨919544921596463280539231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452119790923902081437949 919544921596463280539231)
                    ·
                      rfl

theorem cell22_2686211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 3].length) (baseStart_2686211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686211 prefixEnd_2686211 := by exact prefixLift 2686211
  have htrace : WordTrace (prefixWord ++ tailWord_2686211) baseStart_2686211 baseEnd_2686211 := by
    simpa [prefixWord, tailWord_2686211, baseEnd_2686211] using wordTrace_append hprefix tailTrace_2686211
  have hstable : (prefixWord ++ tailWord_2686211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686211).length < 2 ^ (prefixWord ++ tailWord_2686211).sum := by decide
  have hdescent : baseEnd_2686211 < baseStart_2686211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686245 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_2686245 : Nat := 118140960795 + 2686245 * 2 ^ 59
def prefixEnd_2686245 : Nat := 4983230072969 + 3 ^ 40 * 2686245 * 2
def baseEnd_2686245 : Nat := 919556560491298525189127

theorem tailTrace_2686245 : CollatzResearch.WordTrace tailWord_2686245 prefixEnd_2686245 919556560491298525189127 := by
  unfold tailWord_2686245
  simp only [CollatzResearch.WordTrace]
  refine ⟨97975404153200613966236189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65316936102133742644157459 97975404153200613966236189)
  ·
    refine ⟨36740776557450230237338571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97975404153200613966236189 36740776557450230237338571)
    ·
      refine ⟨55111164836175345356007857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36740776557450230237338571 55111164836175345356007857)
      ·
        refine ⟨41333373627131509017005893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55111164836175345356007857 41333373627131509017005893)
        ·
          refine ⟨7750007555087157940688605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41333373627131509017005893 7750007555087157940688605)
          ·
            refine ⟨2906252833157684227758227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7750007555087157940688605 2906252833157684227758227)
            ·
              refine ⟨4359379249736526341637341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906252833157684227758227 4359379249736526341637341)
              ·
                refine ⟨1634767218651197378114003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4359379249736526341637341 1634767218651197378114003)
                ·
                  refine ⟨2452150827976796067171005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634767218651197378114003 2452150827976796067171005)
                  ·
                    refine ⟨919556560491298525189127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452150827976796067171005 919556560491298525189127)
                    ·
                      rfl

theorem cell22_2686245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_2686245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686245 prefixEnd_2686245 := by exact prefixLift 2686245
  have htrace : WordTrace (prefixWord ++ tailWord_2686245) baseStart_2686245 baseEnd_2686245 := by
    simpa [prefixWord, tailWord_2686245, baseEnd_2686245] using wordTrace_append hprefix tailTrace_2686245
  have hstable : (prefixWord ++ tailWord_2686245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686245).length < 2 ^ (prefixWord ++ tailWord_2686245).sum := by decide
  have hdescent : baseEnd_2686245 < baseStart_2686245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686262 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2686262 : Nat := 118140960795 + 2686262 * 2 ^ 59
def prefixEnd_2686262 : Nat := 4983230072969 + 3 ^ 40 * 2686262 * 2
def baseEnd_2686262 : Nat := 919562379938716147514075

theorem tailTrace_2686262 : CollatzResearch.WordTrace tailWord_2686262 prefixEnd_2686262 919562379938716147514075 := by
  unfold tailWord_2686262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123501512133689116850315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65317349462759350579736693 6123501512133689116850315)
  ·
    refine ⟨9185252268200533675275473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123501512133689116850315 9185252268200533675275473)
    ·
      refine ⟨6888939201150400256456605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9185252268200533675275473 6888939201150400256456605)
      ·
        refine ⟨2583352200431400096171227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6888939201150400256456605 2583352200431400096171227)
        ·
          refine ⟨3875028300647100144256841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583352200431400096171227 3875028300647100144256841)
          ·
            refine ⟨2906271225485325108192631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875028300647100144256841 2906271225485325108192631)
            ·
              refine ⟨4359406838227987662288947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906271225485325108192631 4359406838227987662288947)
              ·
                refine ⟨6539110257341981493433421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359406838227987662288947 6539110257341981493433421)
                ·
                  refine ⟨2452166346503243060037533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6539110257341981493433421 2452166346503243060037533)
                  ·
                    refine ⟨919562379938716147514075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452166346503243060037533 919562379938716147514075)
                    ·
                      rfl

theorem cell22_2686262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2686262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686262 prefixEnd_2686262 := by exact prefixLift 2686262
  have htrace : WordTrace (prefixWord ++ tailWord_2686262) baseStart_2686262 baseEnd_2686262 := by
    simpa [prefixWord, tailWord_2686262, baseEnd_2686262] using wordTrace_append hprefix tailTrace_2686262
  have hstable : (prefixWord ++ tailWord_2686262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686262).length < 2 ^ (prefixWord ++ tailWord_2686262).sum := by decide
  have hdescent : baseEnd_2686262 < baseStart_2686262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686314 : List Nat := [3, 1, 3, 3, 12]
def baseStart_2686314 : Nat := 118140960795 + 2686314 * 2 ^ 59
def prefixEnd_2686314 : Nat := 4983230072969 + 3 ^ 40 * 2686314 * 2
def baseEnd_2686314 : Nat := 3784280578606606358905

theorem tailTrace_2686314 : CollatzResearch.WordTrace tailWord_2686314 prefixEnd_2686314 3784280578606606358905 := by
  unfold tailWord_2686314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24494480197487659687624499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65318613859967092500331997 24494480197487659687624499)
  ·
    refine ⟨36741720296231489531436749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24494480197487659687624499 36741720296231489531436749)
    ·
      refine ⟨13778145111086808574288781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36741720296231489531436749 13778145111086808574288781)
      ·
        refine ⟨5166804416657553215358293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13778145111086808574288781 5166804416657553215358293)
        ·
          refine ⟨3784280578606606358905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5166804416657553215358293 3784280578606606358905)
          ·
            rfl

theorem cell22_2686314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 12].length) (baseStart_2686314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686314 prefixEnd_2686314 := by exact prefixLift 2686314
  have htrace : WordTrace (prefixWord ++ tailWord_2686314) baseStart_2686314 baseEnd_2686314 := by
    simpa [prefixWord, tailWord_2686314, baseEnd_2686314] using wordTrace_append hprefix tailTrace_2686314
  have hstable : (prefixWord ++ tailWord_2686314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686314).length < 2 ^ (prefixWord ++ tailWord_2686314).sum := by decide
  have hdescent : baseEnd_2686314 < baseStart_2686314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686316 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_2686316 : Nat := 118140960795 + 2686316 * 2 ^ 59
def prefixEnd_2686316 : Nat := 4983230072969 + 3 ^ 40 * 2686316 * 2
def baseEnd_2686316 : Nat := 919580865242278006663909

theorem tailTrace_2686316 : CollatzResearch.WordTrace tailWord_2686316 prefixEnd_2686316 919580865242278006663909 := by
  unfold tailWord_2686316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48988996867971696546035401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65318662490628928728047201 48988996867971696546035401)
  ·
    refine ⟨36741747650978772409526551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48988996867971696546035401 36741747650978772409526551)
    ·
      refine ⟨55112621476468158614289827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36741747650978772409526551 55112621476468158614289827)
      ·
        refine ⟨82668932214702237921434741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55112621476468158614289827 82668932214702237921434741)
        ·
          refine ⟨7750212395128334805134507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82668932214702237921434741 7750212395128334805134507)
          ·
            refine ⟨11625318592692502207701761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7750212395128334805134507 11625318592692502207701761)
            ·
              refine ⟨8718988944519376655776321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11625318592692502207701761 8718988944519376655776321)
              ·
                refine ⟨6539241708389532491832241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718988944519376655776321 6539241708389532491832241)
                ·
                  refine ⟨4904431281292149368874181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539241708389532491832241 4904431281292149368874181)
                  ·
                    refine ⟨919580865242278006663909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904431281292149368874181 919580865242278006663909)
                    ·
                      rfl

theorem cell22_2686316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_2686316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686316 prefixEnd_2686316 := by exact prefixLift 2686316
  have htrace : WordTrace (prefixWord ++ tailWord_2686316) baseStart_2686316 baseEnd_2686316 := by
    simpa [prefixWord, tailWord_2686316, baseEnd_2686316] using wordTrace_append hprefix tailTrace_2686316
  have hstable : (prefixWord ++ tailWord_2686316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686316).length < 2 ^ (prefixWord ++ tailWord_2686316).sum := by decide
  have hdescent : baseEnd_2686316 < baseStart_2686316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686350 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_2686350 : Nat := 118140960795 + 2686350 * 2 ^ 59
def prefixEnd_2686350 : Nat := 4983230072969 + 3 ^ 40 * 2686350 * 2
def baseEnd_2686350 : Nat := 919592504137113251313805

theorem tailTrace_2686350 : CollatzResearch.WordTrace tailWord_2686350 prefixEnd_2686350 919592504137113251313805 := by
  unfold tailWord_2686350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247404227227527112351063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65319489211880144599205669 12247404227227527112351063)
  ·
    refine ⟨18371106340841290668526595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12247404227227527112351063 18371106340841290668526595)
    ·
      refine ⟨27556659511261936002789893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18371106340841290668526595 27556659511261936002789893)
      ·
        refine ⟨5166873658361613000523105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27556659511261936002789893 5166873658361613000523105)
        ·
          refine ⟨3875155243771209750392329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166873658361613000523105 3875155243771209750392329)
          ·
            refine ⟨2906366432828407312794247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875155243771209750392329 2906366432828407312794247)
            ·
              refine ⟨4359549649242610969191371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906366432828407312794247 4359549649242610969191371)
              ·
                refine ⟨6539324473863916453787057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359549649242610969191371 6539324473863916453787057)
                ·
                  refine ⟨4904493355397937340340293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539324473863916453787057 4904493355397937340340293)
                  ·
                    refine ⟨919592504137113251313805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904493355397937340340293 919592504137113251313805)
                    ·
                      rfl

theorem cell22_2686350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_2686350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686350 prefixEnd_2686350 := by exact prefixLift 2686350
  have htrace : WordTrace (prefixWord ++ tailWord_2686350) baseStart_2686350 baseEnd_2686350 := by
    simpa [prefixWord, tailWord_2686350, baseEnd_2686350] using wordTrace_append hprefix tailTrace_2686350
  have hstable : (prefixWord ++ tailWord_2686350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686350).length < 2 ^ (prefixWord ++ tailWord_2686350).sum := by decide
  have hdescent : baseEnd_2686350 < baseStart_2686350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686359 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 7]
def baseStart_2686359 : Nat := 118140960795 + 2686359 * 2 ^ 59
def prefixEnd_2686359 : Nat := 4983230072969 + 3 ^ 40 * 2686359 * 2
def baseEnd_2686359 : Nat := 306531861673680075946259

theorem tailTrace_2686359 : CollatzResearch.WordTrace tailWord_2686359 prefixEnd_2686359 306531861673680075946259 := by
  unfold tailWord_2686359
  simp only [CollatzResearch.WordTrace]
  refine ⟨97979562074787611435886131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65319708049858407623924087 97979562074787611435886131)
  ·
    refine ⟨146969343112181417153829197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97979562074787611435886131 146969343112181417153829197)
    ·
      refine ⟨55113503667068031432685949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146969343112181417153829197 55113503667068031432685949)
      ·
        refine ⟨20667563875150511787257231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55113503667068031432685949 20667563875150511787257231)
        ·
          refine ⟨31001345812725767680885847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20667563875150511787257231 31001345812725767680885847)
          ·
            refine ⟨46502018719088651521328771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31001345812725767680885847 46502018719088651521328771)
            ·
              refine ⟨69753028078632977281993157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46502018719088651521328771 69753028078632977281993157)
              ·
                refine ⟨13078692764743683240373717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69753028078632977281993157 13078692764743683240373717)
                ·
                  refine ⟨306531861673680075946259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13078692764743683240373717 306531861673680075946259)
                  ·
                    rfl

theorem cell22_2686359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_2686359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686359 prefixEnd_2686359 := by exact prefixLift 2686359
  have htrace : WordTrace (prefixWord ++ tailWord_2686359) baseStart_2686359 baseEnd_2686359 := by
    simpa [prefixWord, tailWord_2686359, baseEnd_2686359] using wordTrace_append hprefix tailTrace_2686359
  have hstable : (prefixWord ++ tailWord_2686359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686359).length < 2 ^ (prefixWord ++ tailWord_2686359).sum := by decide
  have hdescent : baseEnd_2686359 < baseStart_2686359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686601 : List Nat := [1, 2, 1, 1, 4, 1, 12]
def baseStart_2686601 : Nat := 118140960795 + 2686601 * 2 ^ 59
def prefixEnd_2686601 : Nat := 4983230072969 + 3 ^ 40 * 2686601 * 2
def baseEnd_2686601 : Nat := 34062163946912306047705

theorem tailTrace_2686601 : CollatzResearch.WordTrace tailWord_2686601 prefixEnd_2686601 34062163946912306047705 := by
  unfold tailWord_2686601
  simp only [CollatzResearch.WordTrace]
  refine ⟨97988388539910886766195657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65325592359940591177463771 97988388539910886766195657)
  ·
    refine ⟨73491291404933165074646743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97988388539910886766195657 73491291404933165074646743)
    ·
      refine ⟨110236937107399747611970115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73491291404933165074646743 110236937107399747611970115)
      ·
        refine ⟨165355405661099621417955173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110236937107399747611970115 165355405661099621417955173)
        ·
          refine ⟨31004138561456179015866595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165355405661099621417955173 31004138561456179015866595)
          ·
            refine ⟨46506207842184268523799893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31004138561456179015866595 46506207842184268523799893)
            ·
              refine ⟨34062163946912306047705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46506207842184268523799893 34062163946912306047705)
              ·
                rfl

theorem cell22_2686601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 12].length) (baseStart_2686601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686601 prefixEnd_2686601 := by exact prefixLift 2686601
  have htrace : WordTrace (prefixWord ++ tailWord_2686601) baseStart_2686601 baseEnd_2686601 := by
    simpa [prefixWord, tailWord_2686601, baseEnd_2686601] using wordTrace_append hprefix tailTrace_2686601
  have hstable : (prefixWord ++ tailWord_2686601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686601).length < 2 ^ (prefixWord ++ tailWord_2686601).sum := by decide
  have hdescent : baseEnd_2686601 < baseStart_2686601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686603 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_2686603 : Nat := 118140960795 + 2686603 * 2 ^ 59
def prefixEnd_2686603 : Nat := 4983230072969 + 3 ^ 40 * 2686603 * 2
def baseEnd_2686603 : Nat := 919679111207504924738029

theorem tailTrace_2686603 : CollatzResearch.WordTrace tailWord_2686603 prefixEnd_2686603 919679111207504924738029 := by
  unfold tailWord_2686603
  simp only [CollatzResearch.WordTrace]
  refine ⟨97988461485903641107768463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65325640990602427405178975 97988461485903641107768463)
  ·
    refine ⟨146982692228855461661652695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97988461485903641107768463 146982692228855461661652695)
    ·
      refine ⟨220474038343283192492479043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146982692228855461661652695 220474038343283192492479043)
      ·
        refine ⟨330711057514924788738718565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220474038343283192492479043 330711057514924788738718565)
        ·
          refine ⟨62008323284048397888509731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330711057514924788738718565 62008323284048397888509731)
          ·
            refine ⟨93012484926072596832764597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62008323284048397888509731 93012484926072596832764597)
            ·
              refine ⟨8719920461819305953071681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93012484926072596832764597 8719920461819305953071681)
              ·
                refine ⟨6539940346364479464803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719920461819305953071681 6539940346364479464803761)
                ·
                  refine ⟨4904955259773359598602821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539940346364479464803761 4904955259773359598602821)
                  ·
                    refine ⟨919679111207504924738029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904955259773359598602821 919679111207504924738029)
                    ·
                      rfl

theorem cell22_2686603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_2686603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686603 prefixEnd_2686603 := by exact prefixLift 2686603
  have htrace : WordTrace (prefixWord ++ tailWord_2686603) baseStart_2686603 baseEnd_2686603 := by
    simpa [prefixWord, tailWord_2686603, baseEnd_2686603] using wordTrace_append hprefix tailTrace_2686603
  have hstable : (prefixWord ++ tailWord_2686603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686603).length < 2 ^ (prefixWord ++ tailWord_2686603).sum := by decide
  have hdescent : baseEnd_2686603 < baseStart_2686603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686626 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2686626 : Nat := 118140960795 + 2686626 * 2 ^ 59
def prefixEnd_2686626 : Nat := 4983230072969 + 3 ^ 40 * 2686626 * 2
def baseEnd_2686626 : Nat := 919686984577540531412959

theorem tailTrace_2686626 : CollatzResearch.WordTrace tailWord_2686626 prefixEnd_2686626 919686984577540531412959 := by
  unfold tailWord_2686626
  simp only [CollatzResearch.WordTrace]
  refine ⟨24497325091205079008963933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65326200243213544023903821 24497325091205079008963933)
  ·
    refine ⟨9186496909201904628361475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24497325091205079008963933 9186496909201904628361475)
    ·
      refine ⟨13779745363802856942542213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9186496909201904628361475 13779745363802856942542213)
      ·
        refine ⟨2583702255713035676726665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13779745363802856942542213 2583702255713035676726665)
        ·
          refine ⟨1937776691784776757544999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2583702255713035676726665 1937776691784776757544999)
          ·
            refine ⟨2906665037677165136317499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937776691784776757544999 2906665037677165136317499)
            ·
              refine ⟨4359997556515747704476249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906665037677165136317499 4359997556515747704476249)
              ·
                refine ⟨3269998167386810778357187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359997556515747704476249 3269998167386810778357187)
                ·
                  refine ⟨4904997251080216167535781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269998167386810778357187 4904997251080216167535781)
                  ·
                    refine ⟨919686984577540531412959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904997251080216167535781 919686984577540531412959)
                    ·
                      rfl

theorem cell22_2686626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2686626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686626 prefixEnd_2686626 := by exact prefixLift 2686626
  have htrace : WordTrace (prefixWord ++ tailWord_2686626) baseStart_2686626 baseEnd_2686626 := by
    simpa [prefixWord, tailWord_2686626, baseEnd_2686626] using wordTrace_append hprefix tailTrace_2686626
  have hstable : (prefixWord ++ tailWord_2686626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686626).length < 2 ^ (prefixWord ++ tailWord_2686626).sum := by decide
  have hdescent : baseEnd_2686626 < baseStart_2686626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686684 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2686684 : Nat := 118140960795 + 2686684 * 2 ^ 59
def prefixEnd_2686684 : Nat := 4983230072969 + 3 ^ 40 * 2686684 * 2
def baseEnd_2686684 : Nat := 919706839162847713462781

theorem tailTrace_2686684 : CollatzResearch.WordTrace tailWord_2686684 prefixEnd_2686684 919706839162847713462781 := by
  unfold tailWord_2686684
  simp only [CollatzResearch.WordTrace]
  refine ⟨48995707899305095970733553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65327610532406794627644737 48995707899305095970733553)
  ·
    refine ⟨36746780924478821978050165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48995707899305095970733553 36746780924478821978050165)
    ·
      refine ⟨3445010711669889560442203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36746780924478821978050165 3445010711669889560442203)
      ·
        refine ⟨5167516067504834340663305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445010711669889560442203 5167516067504834340663305)
        ·
          refine ⟨3875637050628625755497479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5167516067504834340663305 3875637050628625755497479)
          ·
            refine ⟨5813455575942938633246219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3875637050628625755497479 5813455575942938633246219)
            ·
              refine ⟨8720183363914407949869329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813455575942938633246219 8720183363914407949869329)
              ·
                refine ⟨6540137522935805962401997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8720183363914407949869329 6540137522935805962401997)
                ·
                  refine ⟨2452551571100927235900749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6540137522935805962401997 2452551571100927235900749)
                  ·
                    refine ⟨919706839162847713462781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452551571100927235900749 919706839162847713462781)
                    ·
                      rfl

theorem cell22_2686684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2686684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686684 prefixEnd_2686684 := by exact prefixLift 2686684
  have htrace : WordTrace (prefixWord ++ tailWord_2686684) baseStart_2686684 baseEnd_2686684 := by
    simpa [prefixWord, tailWord_2686684, baseEnd_2686684] using wordTrace_append hprefix tailTrace_2686684
  have hstable : (prefixWord ++ tailWord_2686684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686684).length < 2 ^ (prefixWord ++ tailWord_2686684).sum := by decide
  have hdescent : baseEnd_2686684 < baseStart_2686684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686723 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_2686723 : Nat := 118140960795 + 2686723 * 2 ^ 59
def prefixEnd_2686723 : Nat := 4983230072969 + 3 ^ 40 * 2686723 * 2
def baseEnd_2686723 : Nat := 919720189659864611737661

theorem tailTrace_2686723 : CollatzResearch.WordTrace tailWord_2686723 prefixEnd_2686723 919720189659864611737661 := by
  unfold tailWord_2686723
  simp only [CollatzResearch.WordTrace]
  refine ⟨97992838245468901602136823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65328558830312601068091215 97992838245468901602136823)
  ·
    refine ⟨146989257368203352403205235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97992838245468901602136823 146989257368203352403205235)
    ·
      refine ⟨220483886052305028604807853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146989257368203352403205235 220483886052305028604807853)
      ·
        refine ⟨82681457269614385726802945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220483886052305028604807853 82681457269614385726802945)
        ·
          refine ⟨62011092952210789295102209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82681457269614385726802945 62011092952210789295102209)
          ·
            refine ⟨46508319714158091971326657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62011092952210789295102209 46508319714158091971326657)
            ·
              refine ⟨34881239785618568978494993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46508319714158091971326657 34881239785618568978494993)
              ·
                refine ⟨26160929839213926733871245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34881239785618568978494993 26160929839213926733871245)
                ·
                  refine ⟨9810348689705222525201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26160929839213926733871245 9810348689705222525201717)
                  ·
                    refine ⟨919720189659864611737661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9810348689705222525201717 919720189659864611737661)
                    ·
                      rfl

theorem cell22_2686723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_2686723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686723 prefixEnd_2686723 := by exact prefixLift 2686723
  have htrace : WordTrace (prefixWord ++ tailWord_2686723) baseStart_2686723 baseEnd_2686723 := by
    simpa [prefixWord, tailWord_2686723, baseEnd_2686723] using wordTrace_append hprefix tailTrace_2686723
  have hstable : (prefixWord ++ tailWord_2686723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686723).length < 2 ^ (prefixWord ++ tailWord_2686723).sum := by decide
  have hdescent : baseEnd_2686723 < baseStart_2686723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686770 : List Nat := [3, 2, 1, 1, 3, 4, 8]
def baseStart_2686770 : Nat := 118140960795 + 2686770 * 2 ^ 59
def prefixEnd_2686770 : Nat := 4983230072969 + 3 ^ 40 * 2686770 * 2
def baseEnd_2686770 : Nat := 34064306619273042807871

theorem tailTrace_2686770 : CollatzResearch.WordTrace tailWord_2686770 prefixEnd_2686770 34064306619273042807871 := by
  unfold tailWord_2686770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24498638119074657157274441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65329701650865752419398509 24498638119074657157274441)
  ·
    refine ⟨18373978589305992867955831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24498638119074657157274441 18373978589305992867955831)
    ·
      refine ⟨27560967883958989301933747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18373978589305992867955831 27560967883958989301933747)
      ·
        refine ⟨41341451825938483952900621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27560967883958989301933747 41341451825938483952900621)
        ·
          refine ⟨15503044434726931482337733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41341451825938483952900621 15503044434726931482337733)
          ·
            refine ⟨2906820831511299652938325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15503044434726931482337733 2906820831511299652938325)
            ·
              refine ⟨34064306619273042807871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2906820831511299652938325 34064306619273042807871)
              ·
                rfl

theorem cell22_2686770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 8].length) (baseStart_2686770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686770 prefixEnd_2686770 := by exact prefixLift 2686770
  have htrace : WordTrace (prefixWord ++ tailWord_2686770) baseStart_2686770 baseEnd_2686770 := by
    simpa [prefixWord, tailWord_2686770, baseEnd_2686770] using wordTrace_append hprefix tailTrace_2686770
  have hstable : (prefixWord ++ tailWord_2686770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686770).length < 2 ^ (prefixWord ++ tailWord_2686770).sum := by decide
  have hdescent : baseEnd_2686770 < baseStart_2686770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686772 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2686772 : Nat := 118140960795 + 2686772 * 2 ^ 59
def prefixEnd_2686772 : Nat := 4983230072969 + 3 ^ 40 * 2686772 * 2
def baseEnd_2686772 : Nat := 919736963361244817262511

theorem tailTrace_2686772 : CollatzResearch.WordTrace tailWord_2686772 prefixEnd_2686772 919736963361244817262511 := by
  unfold tailWord_2686772
  simp only [CollatzResearch.WordTrace]
  refine ⟨48997312711145691485335285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65329750281527588647113713 48997312711145691485335285)
  ·
    refine ⟨4593498066669908576750183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48997312711145691485335285 4593498066669908576750183)
    ·
      refine ⟨6890247100004862865125275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593498066669908576750183 6890247100004862865125275)
      ·
        refine ⟨10335370650007294297687913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890247100004862865125275 10335370650007294297687913)
        ·
          refine ⟨7751527987505470723265935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10335370650007294297687913 7751527987505470723265935)
          ·
            refine ⟨11627291981258206084898903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7751527987505470723265935 11627291981258206084898903)
            ·
              refine ⟨17440937971887309127348355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627291981258206084898903 17440937971887309127348355)
              ·
                refine ⟨26161406957830963691022533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17440937971887309127348355 26161406957830963691022533)
                ·
                  refine ⟨4905263804593305692066725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26161406957830963691022533 4905263804593305692066725)
                  ·
                    refine ⟨919736963361244817262511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905263804593305692066725 919736963361244817262511)
                    ·
                      rfl

theorem cell22_2686772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2686772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686772 prefixEnd_2686772 := by exact prefixLift 2686772
  have htrace : WordTrace (prefixWord ++ tailWord_2686772) baseStart_2686772 baseEnd_2686772 := by
    simpa [prefixWord, tailWord_2686772, baseEnd_2686772] using wordTrace_append hprefix tailTrace_2686772
  have hstable : (prefixWord ++ tailWord_2686772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686772).length < 2 ^ (prefixWord ++ tailWord_2686772).sum := by decide
  have hdescent : baseEnd_2686772 < baseStart_2686772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686774 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2686774 : Nat := 118140960795 + 2686774 * 2 ^ 59
def prefixEnd_2686774 : Nat := 4983230072969 + 3 ^ 40 * 2686774 * 2
def baseEnd_2686774 : Nat := 919737648002117478712505

theorem tailTrace_2686774 : CollatzResearch.WordTrace tailWord_2686774 prefixEnd_2686774 919737648002117478712505 := by
  unfold tailWord_2686774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124668648017758582015211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65329798912189424874828917 6124668648017758582015211)
  ·
    refine ⟨9187002972026637873022817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124668648017758582015211 9187002972026637873022817)
    ·
      refine ⟨6890252229019978404767113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9187002972026637873022817 6890252229019978404767113)
      ·
        refine ⟨5167689171764983803575335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6890252229019978404767113 5167689171764983803575335)
        ·
          refine ⟨7751533757647475705363003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167689171764983803575335 7751533757647475705363003)
          ·
            refine ⟨11627300636471213558044505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7751533757647475705363003 11627300636471213558044505)
            ·
              refine ⟨8720475477353410168533379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11627300636471213558044505 8720475477353410168533379)
              ·
                refine ⟨13080713216030115252800069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8720475477353410168533379 13080713216030115252800069)
                ·
                  refine ⟨2452633728005646609900013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13080713216030115252800069 2452633728005646609900013)
                  ·
                    refine ⟨919737648002117478712505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452633728005646609900013 919737648002117478712505)
                    ·
                      rfl

theorem cell22_2686774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2686774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686774 prefixEnd_2686774 := by exact prefixLift 2686774
  have htrace : WordTrace (prefixWord ++ tailWord_2686774) baseStart_2686774 baseEnd_2686774 := by
    simpa [prefixWord, tailWord_2686774, baseEnd_2686774] using wordTrace_append hprefix tailTrace_2686774
  have hstable : (prefixWord ++ tailWord_2686774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686774).length < 2 ^ (prefixWord ++ tailWord_2686774).sum := by decide
  have hdescent : baseEnd_2686774 < baseStart_2686774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686879 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 1, 4]
def baseStart_2686879 : Nat := 118140960795 + 2686879 * 2 ^ 59
def prefixEnd_2686879 : Nat := 4983230072969 + 3 ^ 40 * 2686879 * 2
def baseEnd_2686879 : Nat := 919773591647932204837183

theorem tailTrace_2686879 : CollatzResearch.WordTrace tailWord_2686879 prefixEnd_2686879 919773591647932204837183 := by
  unfold tailWord_2686879
  simp only [CollatzResearch.WordTrace]
  refine ⟨97998528032903740244815691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65332352021935826829877127 97998528032903740244815691)
  ·
    refine ⟨146997792049355610367223537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97998528032903740244815691 146997792049355610367223537)
    ·
      refine ⟨110248344037016707775417653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146997792049355610367223537 110248344037016707775417653)
      ·
        refine ⟨10335782253470316353945405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110248344037016707775417653 10335782253470316353945405)
        ·
          refine ⟨3875918345051368632729527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10335782253470316353945405 3875918345051368632729527)
          ·
            refine ⟨5813877517577052949094291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3875918345051368632729527 5813877517577052949094291)
            ·
              refine ⟨8720816276365579423641437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813877517577052949094291 8720816276365579423641437)
              ·
                refine ⟨3270306103637092283865539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8720816276365579423641437 3270306103637092283865539)
                ·
                  refine ⟨4905459155455638425798309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270306103637092283865539 4905459155455638425798309)
                  ·
                    refine ⟨919773591647932204837183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905459155455638425798309 919773591647932204837183)
                    ·
                      rfl

theorem cell22_2686879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_2686879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686879 prefixEnd_2686879 := by exact prefixLift 2686879
  have htrace : WordTrace (prefixWord ++ tailWord_2686879) baseStart_2686879 baseEnd_2686879 := by
    simpa [prefixWord, tailWord_2686879, baseEnd_2686879] using wordTrace_append hprefix tailTrace_2686879
  have hstable : (prefixWord ++ tailWord_2686879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686879).length < 2 ^ (prefixWord ++ tailWord_2686879).sum := by decide
  have hdescent : baseEnd_2686879 < baseStart_2686879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686905 : List Nat := [1, 2, 1, 4, 2, 1, 2, 9]
def baseStart_2686905 : Nat := 118140960795 + 2686905 * 2 ^ 59
def prefixEnd_2686905 : Nat := 4983230072969 + 3 ^ 40 * 2686905 * 2
def baseEnd_2686905 : Nat := 102198054664364089298567

theorem tailTrace_2686905 : CollatzResearch.WordTrace tailWord_2686905 prefixEnd_2686905 102198054664364089298567 := by
  unfold tailWord_2686905
  simp only [CollatzResearch.WordTrace]
  refine ⟨97999476330809546685262169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65332984220539697790174779 97999476330809546685262169)
  ·
    refine ⟨73499607248107160013946627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97999476330809546685262169 73499607248107160013946627)
    ·
      refine ⟨110249410872160740020919941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73499607248107160013946627 110249410872160740020919941)
      ·
        refine ⟨20671764538530138753922489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110249410872160740020919941 20671764538530138753922489)
        ·
          refine ⟨15503823403897604065441867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20671764538530138753922489 15503823403897604065441867)
          ·
            refine ⟨23255735105846406098162801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15503823403897604065441867 23255735105846406098162801)
            ·
              refine ⟨17441801329384804573622101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23255735105846406098162801 17441801329384804573622101)
              ·
                refine ⟨102198054664364089298567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17441801329384804573622101 102198054664364089298567)
                ·
                  rfl

theorem cell22_2686905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 9].length) (baseStart_2686905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686905 prefixEnd_2686905 := by exact prefixLift 2686905
  have htrace : WordTrace (prefixWord ++ tailWord_2686905) baseStart_2686905 baseEnd_2686905 := by
    simpa [prefixWord, tailWord_2686905, baseEnd_2686905] using wordTrace_append hprefix tailTrace_2686905
  have hstable : (prefixWord ++ tailWord_2686905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686905).length < 2 ^ (prefixWord ++ tailWord_2686905).sum := by decide
  have hdescent : baseEnd_2686905 < baseStart_2686905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686909 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_2686909 : Nat := 118140960795 + 2686909 * 2 ^ 59
def prefixEnd_2686909 : Nat := 4983230072969 + 3 ^ 40 * 2686909 * 2
def baseEnd_2686909 : Nat := 919783861261022126587091

theorem tailTrace_2686909 : CollatzResearch.WordTrace tailWord_2686909 prefixEnd_2686909 919783861261022126587091 := by
  unfold tailWord_2686909
  simp only [CollatzResearch.WordTrace]
  refine ⟨97999622222795055368407781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65333081481863370245605187 97999622222795055368407781)
  ·
    refine ⟨18374929166774072881576459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97999622222795055368407781 18374929166774072881576459)
    ·
      refine ⟨27562393750161109322364689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18374929166774072881576459 27562393750161109322364689)
      ·
        refine ⟨20671795312620831991773517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27562393750161109322364689 20671795312620831991773517)
        ·
          refine ⟨7751923242232811996915069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20671795312620831991773517 7751923242232811996915069)
          ·
            refine ⟨2906971215837304498843151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7751923242232811996915069 2906971215837304498843151)
            ·
              refine ⟨4360456823755956748264727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906971215837304498843151 4360456823755956748264727)
              ·
                refine ⟨6540685235633935122397091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360456823755956748264727 6540685235633935122397091)
                ·
                  refine ⟨9811027853450902683595637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540685235633935122397091 9811027853450902683595637)
                  ·
                    refine ⟨919783861261022126587091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9811027853450902683595637 919783861261022126587091)
                    ·
                      rfl

theorem cell22_2686909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_2686909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686909 prefixEnd_2686909 := by exact prefixLift 2686909
  have htrace : WordTrace (prefixWord ++ tailWord_2686909) baseStart_2686909 baseEnd_2686909 := by
    simpa [prefixWord, tailWord_2686909, baseEnd_2686909] using wordTrace_append hprefix tailTrace_2686909
  have hstable : (prefixWord ++ tailWord_2686909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686909).length < 2 ^ (prefixWord ++ tailWord_2686909).sum := by decide
  have hdescent : baseEnd_2686909 < baseStart_2686909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686922 : List Nat := [3, 1, 2, 1, 2, 1, 6, 6]
def baseStart_2686922 : Nat := 118140960795 + 2686922 * 2 ^ 59
def prefixEnd_2686922 : Nat := 4983230072969 + 3 ^ 40 * 2686922 * 2
def baseEnd_2686922 : Nat := 102198701269632714001339

theorem tailTrace_2686922 : CollatzResearch.WordTrace tailWord_2686922 prefixEnd_2686922 102198701269632714001339 := by
  unfold tailWord_2686922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500024092936989647157755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65333397581165305725754013 24500024092936989647157755)
  ·
    refine ⟨36750036139405484470736633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24500024092936989647157755 36750036139405484470736633)
    ·
      refine ⟨27562527104554113353052475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36750036139405484470736633 27562527104554113353052475)
      ·
        refine ⟨41343790656831170029578713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27562527104554113353052475 41343790656831170029578713)
        ·
          refine ⟨31007842992623377522184035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41343790656831170029578713 31007842992623377522184035)
          ·
            refine ⟨46511764488935066283276053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31007842992623377522184035 46511764488935066283276053)
            ·
              refine ⟨2180238960418831232028565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46511764488935066283276053 2180238960418831232028565)
              ·
                refine ⟨102198701269632714001339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2180238960418831232028565 102198701269632714001339)
                ·
                  rfl

theorem cell22_2686922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_2686922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2686922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2686922 prefixEnd_2686922 := by exact prefixLift 2686922
  have htrace : WordTrace (prefixWord ++ tailWord_2686922) baseStart_2686922 baseEnd_2686922 := by
    simpa [prefixWord, tailWord_2686922, baseEnd_2686922] using wordTrace_append hprefix tailTrace_2686922
  have hstable : (prefixWord ++ tailWord_2686922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686922).length < 2 ^ (prefixWord ++ tailWord_2686922).sum := by decide
  have hdescent : baseEnd_2686922 < baseStart_2686922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687005 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2687005 : Nat := 118140960795 + 2687005 * 2 ^ 59
def prefixEnd_2687005 : Nat := 4983230072969 + 3 ^ 40 * 2687005 * 2
def baseEnd_2687005 : Nat := 919816724022909876186797

theorem tailTrace_2687005 : CollatzResearch.WordTrace tailWord_2687005 prefixEnd_2687005 919816724022909876186797 := by
  unfold tailWord_2687005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98003123630447263763902469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65335415753631509175934979 98003123630447263763902469)
  ·
    refine ⟨18375585680708861955731713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98003123630447263763902469 18375585680708861955731713)
    ·
      refine ⟨13781689260531646466798785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18375585680708861955731713 13781689260531646466798785)
      ·
        refine ⟨10336266945398734850099089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13781689260531646466798785 10336266945398734850099089)
        ·
          refine ⟨7752200209049051137574317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336266945398734850099089 7752200209049051137574317)
          ·
            refine ⟨2907075078393394176590369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7752200209049051137574317 2907075078393394176590369)
            ·
              refine ⟨2180306308795045632442777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907075078393394176590369 2180306308795045632442777)
              ·
                refine ⟨1635229731596284224332083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180306308795045632442777 1635229731596284224332083)
                ·
                  refine ⟨2452844597394426336498125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635229731596284224332083 2452844597394426336498125)
                  ·
                    refine ⟨919816724022909876186797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452844597394426336498125 919816724022909876186797)
                    ·
                      rfl

theorem cell22_2687005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2687005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687005 prefixEnd_2687005 := by exact prefixLift 2687005
  have htrace : WordTrace (prefixWord ++ tailWord_2687005) baseStart_2687005 baseEnd_2687005 := by
    simpa [prefixWord, tailWord_2687005, baseEnd_2687005] using wordTrace_append hprefix tailTrace_2687005
  have hstable : (prefixWord ++ tailWord_2687005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687005).length < 2 ^ (prefixWord ++ tailWord_2687005).sum := by decide
  have hdescent : baseEnd_2687005 < baseStart_2687005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687016 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2687016 : Nat := 118140960795 + 2687016 * 2 ^ 59
def prefixEnd_2687016 : Nat := 4983230072969 + 3 ^ 40 * 2687016 * 2
def baseEnd_2687016 : Nat := 919820489547709514161763

theorem tailTrace_2687016 : CollatzResearch.WordTrace tailWord_2687016 prefixEnd_2687016 919820489547709514161763 := by
  unfold tailWord_2687016
  simp only [CollatzResearch.WordTrace]
  refine ⟨49001762416703706321276451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65335683222271608428368601 49001762416703706321276451)
  ·
    refine ⟨73502643625055559481914677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49001762416703706321276451 73502643625055559481914677)
    ·
      refine ⟨6890872839848958701429501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73502643625055559481914677 6890872839848958701429501)
      ·
        refine ⟨2584077314943359513036063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6890872839848958701429501 2584077314943359513036063)
        ·
          refine ⟨3876115972415039269554095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584077314943359513036063 3876115972415039269554095)
          ·
            refine ⟨5814173958622558904331143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876115972415039269554095 5814173958622558904331143)
            ·
              refine ⟨8721260937933838356496715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5814173958622558904331143 8721260937933838356496715)
              ·
                refine ⟨13081891406900757534745073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8721260937933838356496715 13081891406900757534745073)
                ·
                  refine ⟨9811418555175568151058805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13081891406900757534745073 9811418555175568151058805)
                  ·
                    refine ⟨919820489547709514161763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9811418555175568151058805 919820489547709514161763)
                    ·
                      rfl

theorem cell22_2687016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2687016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687016 prefixEnd_2687016 := by exact prefixLift 2687016
  have htrace : WordTrace (prefixWord ++ tailWord_2687016) baseStart_2687016 baseEnd_2687016 := by
    simpa [prefixWord, tailWord_2687016, baseEnd_2687016] using wordTrace_append hprefix tailTrace_2687016
  have hstable : (prefixWord ++ tailWord_2687016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687016).length < 2 ^ (prefixWord ++ tailWord_2687016).sum := by decide
  have hdescent : baseEnd_2687016 < baseStart_2687016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687027 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_2687027 : Nat := 118140960795 + 2687027 * 2 ^ 59
def prefixEnd_2687027 : Nat := 4983230072969 + 3 ^ 40 * 2687027 * 2
def baseEnd_2687027 : Nat := 919824255072509152136729

theorem tailTrace_2687027 : CollatzResearch.WordTrace tailWord_2687027 prefixEnd_2687027 919824255072509152136729 := by
  unfold tailWord_2687027
  simp only [CollatzResearch.WordTrace]
  refine ⟨98003926036367561521203335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65335950690911707680802223 98003926036367561521203335)
  ·
    refine ⟨147005889054551342281805003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98003926036367561521203335 147005889054551342281805003)
    ·
      refine ⟨220508833581827013422707505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147005889054551342281805003 220508833581827013422707505)
      ·
        refine ⟨165381625186370260067030629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220508833581827013422707505 165381625186370260067030629)
        ·
          refine ⟨31009054722444423762568243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165381625186370260067030629 31009054722444423762568243)
          ·
            refine ⟨46513582083666635643852365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31009054722444423762568243 46513582083666635643852365)
            ·
              refine ⟨17442593281374988366444637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46513582083666635643852365 17442593281374988366444637)
              ·
                refine ⟨6540972480515620637416739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17442593281374988366444637 6540972480515620637416739)
                ·
                  refine ⟨9811458720773430956125109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540972480515620637416739 9811458720773430956125109)
                  ·
                    refine ⟨919824255072509152136729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9811458720773430956125109 919824255072509152136729)
                    ·
                      rfl

theorem cell22_2687027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_2687027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687027 prefixEnd_2687027 := by exact prefixLift 2687027
  have htrace : WordTrace (prefixWord ++ tailWord_2687027) baseStart_2687027 baseEnd_2687027 := by
    simpa [prefixWord, tailWord_2687027, baseEnd_2687027] using wordTrace_append hprefix tailTrace_2687027
  have hstable : (prefixWord ++ tailWord_2687027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687027).length < 2 ^ (prefixWord ++ tailWord_2687027).sum := by decide
  have hdescent : baseEnd_2687027 < baseStart_2687027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687061 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2687061 : Nat := 118140960795 + 2687061 * 2 ^ 59
def prefixEnd_2687061 : Nat := 4983230072969 + 3 ^ 40 * 2687061 * 2
def baseEnd_2687061 : Nat := 919835893967344396786625

theorem tailTrace_2687061 : CollatzResearch.WordTrace tailWord_2687061 prefixEnd_2687061 919835893967344396786625 := by
  unfold tailWord_2687061
  simp only [CollatzResearch.WordTrace]
  refine ⟨98005166118244385327941037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65336777412162923551960691 98005166118244385327941037)
  ·
    refine ⟨36751937294341644497977889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98005166118244385327941037 36751937294341644497977889)
    ·
      refine ⟨27563952970756233373483417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36751937294341644497977889 27563952970756233373483417)
      ·
        refine ⟨20672964728067175030112563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27563952970756233373483417 20672964728067175030112563)
        ·
          refine ⟨31009447092100762545168845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20672964728067175030112563 31009447092100762545168845)
          ·
            refine ⟨11628542659537785954438317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31009447092100762545168845 11628542659537785954438317)
            ·
              refine ⟨4360703497326669732914369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11628542659537785954438317 4360703497326669732914369)
              ·
                refine ⟨3270527622995002299685777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4360703497326669732914369 3270527622995002299685777)
                ·
                  refine ⟨2452895717246251724764333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3270527622995002299685777 2452895717246251724764333)
                  ·
                    refine ⟨919835893967344396786625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452895717246251724764333 919835893967344396786625)
                    ·
                      rfl

theorem cell22_2687061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2687061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687061 prefixEnd_2687061 := by exact prefixLift 2687061
  have htrace : WordTrace (prefixWord ++ tailWord_2687061) baseStart_2687061 baseEnd_2687061 := by
    simpa [prefixWord, tailWord_2687061, baseEnd_2687061] using wordTrace_append hprefix tailTrace_2687061
  have hstable : (prefixWord ++ tailWord_2687061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687061).length < 2 ^ (prefixWord ++ tailWord_2687061).sum := by decide
  have hdescent : baseEnd_2687061 < baseStart_2687061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687089 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 3, 3]
def baseStart_2687089 : Nat := 118140960795 + 2687089 * 2 ^ 59
def prefixEnd_2687089 : Nat := 4983230072969 + 3 ^ 40 * 2687089 * 2
def baseEnd_2687089 : Nat := 919845478939561657086539

theorem tailTrace_2687089 : CollatzResearch.WordTrace tailWord_2687089 prefixEnd_2687089 919845478939561657086539 := by
  unfold tailWord_2687089
  simp only [CollatzResearch.WordTrace]
  refine ⟨98006187362142946109960321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65337458241428630739973547 98006187362142946109960321)
  ·
    refine ⟨73504640521607209582470241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98006187362142946109960321 73504640521607209582470241)
    ·
      refine ⟨55128480391205407186852681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73504640521607209582470241 55128480391205407186852681)
      ·
        refine ⟨41346360293404055390139511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55128480391205407186852681 41346360293404055390139511)
        ·
          refine ⟨62019540440106083085209267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41346360293404055390139511 62019540440106083085209267)
          ·
            refine ⟨93029310660159124627813901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62019540440106083085209267 93029310660159124627813901)
            ·
              refine ⟨34885991497559671735430213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93029310660159124627813901 34885991497559671735430213)
              ·
                refine ⟨6541123405792438450393165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34885991497559671735430213 6541123405792438450393165)
                ·
                  refine ⟨2452921277172164418897437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6541123405792438450393165 2452921277172164418897437)
                  ·
                    refine ⟨919845478939561657086539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2452921277172164418897437 919845478939561657086539)
                    ·
                      rfl

theorem cell22_2687089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_2687089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687089 prefixEnd_2687089 := by exact prefixLift 2687089
  have htrace : WordTrace (prefixWord ++ tailWord_2687089) baseStart_2687089 baseEnd_2687089 := by
    simpa [prefixWord, tailWord_2687089, baseEnd_2687089] using wordTrace_append hprefix tailTrace_2687089
  have hstable : (prefixWord ++ tailWord_2687089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687089).length < 2 ^ (prefixWord ++ tailWord_2687089).sum := by decide
  have hdescent : baseEnd_2687089 < baseStart_2687089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687136 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_2687136 : Nat := 118140960795 + 2687136 * 2 ^ 59
def prefixEnd_2687136 : Nat := 4983230072969 + 3 ^ 40 * 2687136 * 2
def baseEnd_2687136 : Nat := 306620522666689733720465

theorem tailTrace_2687136 : CollatzResearch.WordTrace tailWord_2687136 prefixEnd_2687136 306620522666689733720465 := by
  unfold tailWord_2687136
  simp only [CollatzResearch.WordTrace]
  refine ⟨49003950796486336568460631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65338601061981782091280841 49003950796486336568460631)
  ·
    refine ⟨73505926194729504852690947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49003950796486336568460631 73505926194729504852690947)
    ·
      refine ⟨110258889292094257279036421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73505926194729504852690947 110258889292094257279036421)
      ·
        refine ⟨20673541742267673239819329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110258889292094257279036421 20673541742267673239819329)
        ·
          refine ⟨15505156306700754929864497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20673541742267673239819329 15505156306700754929864497)
          ·
            refine ⟨11628867230025566197398373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15505156306700754929864497 11628867230025566197398373)
            ·
              refine ⟨2180412605629793662012195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11628867230025566197398373 2180412605629793662012195)
              ·
                refine ⟨3270618908444690493018293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180412605629793662012195 3270618908444690493018293)
                ·
                  refine ⟨306620522666689733720465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270618908444690493018293 306620522666689733720465)
                  ·
                    rfl

theorem cell22_2687136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_2687136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687136 prefixEnd_2687136 := by exact prefixLift 2687136
  have htrace : WordTrace (prefixWord ++ tailWord_2687136) baseStart_2687136 baseEnd_2687136 := by
    simpa [prefixWord, tailWord_2687136, baseEnd_2687136] using wordTrace_append hprefix tailTrace_2687136
  have hstable : (prefixWord ++ tailWord_2687136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687136).length < 2 ^ (prefixWord ++ tailWord_2687136).sum := by decide
  have hdescent : baseEnd_2687136 < baseStart_2687136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687170 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2687170 : Nat := 118140960795 + 2687170 * 2 ^ 59
def prefixEnd_2687170 : Nat := 4983230072969 + 3 ^ 40 * 2687170 * 2
def baseEnd_2687170 : Nat := 306624402298301481937097

theorem tailTrace_2687170 : CollatzResearch.WordTrace tailWord_2687170 prefixEnd_2687170 306624402298301481937097 := by
  unfold tailWord_2687170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24502285418712374235914741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65339427783232997962439309 24502285418712374235914741)
  ·
    refine ⟨2297089258004285084617007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24502285418712374235914741 2297089258004285084617007)
    ·
      refine ⟨3445633887006427626925511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297089258004285084617007 3445633887006427626925511)
      ·
        refine ⟨5168450830509641440388267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3445633887006427626925511 5168450830509641440388267)
        ·
          refine ⟨7752676245764462160582401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168450830509641440388267 7752676245764462160582401)
          ·
            refine ⟨5814507184323346620436801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7752676245764462160582401 5814507184323346620436801)
            ·
              refine ⟨4360880388242509965327601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5814507184323346620436801 4360880388242509965327601)
              ·
                refine ⟨3270660291181882473995701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4360880388242509965327601 3270660291181882473995701)
                ·
                  refine ⟨306624402298301481937097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270660291181882473995701 306624402298301481937097)
                  ·
                    rfl

theorem cell22_2687170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2687170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687170 prefixEnd_2687170 := by exact prefixLift 2687170
  have htrace : WordTrace (prefixWord ++ tailWord_2687170) baseStart_2687170 baseEnd_2687170 := by
    simpa [prefixWord, tailWord_2687170, baseEnd_2687170] using wordTrace_append hprefix tailTrace_2687170
  have hstable : (prefixWord ++ tailWord_2687170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687170).length < 2 ^ (prefixWord ++ tailWord_2687170).sum := by decide
  have hdescent : baseEnd_2687170 < baseStart_2687170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687194 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2687194 : Nat := 118140960795 + 2687194 * 2 ^ 59
def prefixEnd_2687194 : Nat := 4983230072969 + 3 ^ 40 * 2687194 * 2
def baseEnd_2687194 : Nat := 919881422585376383211217

theorem tailTrace_2687194 : CollatzResearch.WordTrace tailWord_2687194 prefixEnd_2687194 919881422585376383211217 := by
  unfold tailWord_2687194
  simp only [CollatzResearch.WordTrace]
  refine ⟨24502504256690637260633159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65340011351175032695021757 24502504256690637260633159)
  ·
    refine ⟨36753756385035955890949739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24502504256690637260633159 36753756385035955890949739)
    ·
      refine ⟨55130634577553933836424609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36753756385035955890949739 55130634577553933836424609)
      ·
        refine ⟨41347975933165450377318457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55130634577553933836424609 41347975933165450377318457)
        ·
          refine ⟨31010981949874087782988843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41347975933165450377318457 31010981949874087782988843)
          ·
            refine ⟨46516472924811131674483265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31010981949874087782988843 46516472924811131674483265)
            ·
              refine ⟨34887354693608348755862449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46516472924811131674483265 34887354693608348755862449)
              ·
                refine ⟨26165516020206261566896837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34887354693608348755862449 26165516020206261566896837)
                ·
                  refine ⟨4906034253788674043793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26165516020206261566896837 4906034253788674043793157)
                  ·
                    refine ⟨919881422585376383211217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4906034253788674043793157 919881422585376383211217)
                    ·
                      rfl

theorem cell22_2687194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2687194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687194 prefixEnd_2687194 := by exact prefixLift 2687194
  have htrace : WordTrace (prefixWord ++ tailWord_2687194) baseStart_2687194 baseEnd_2687194 := by
    simpa [prefixWord, tailWord_2687194, baseEnd_2687194] using wordTrace_append hprefix tailTrace_2687194
  have hstable : (prefixWord ++ tailWord_2687194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687194).length < 2 ^ (prefixWord ++ tailWord_2687194).sum := by decide
  have hdescent : baseEnd_2687194 < baseStart_2687194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687241 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_2687241 : Nat := 118140960795 + 2687241 * 2 ^ 59
def prefixEnd_2687241 : Nat := 4983230072969 + 3 ^ 40 * 2687241 * 2
def baseEnd_2687241 : Nat := 919897511645883927286073

theorem tailTrace_2687241 : CollatzResearch.WordTrace tailWord_2687241 prefixEnd_2687241 919897511645883927286073 := by
  unfold tailWord_2687241
  simp only [CollatzResearch.WordTrace]
  refine ⟨98011731257592276069493577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65341154171728184046329051 98011731257592276069493577)
  ·
    refine ⟨73508798443194207052120183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98011731257592276069493577 73508798443194207052120183)
    ·
      refine ⟨110263197664791310578180275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73508798443194207052120183 110263197664791310578180275)
      ·
        refine ⟨165394796497186965867270413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110263197664791310578180275 165394796497186965867270413)
        ·
          refine ⟨62023048686445112200226405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165394796497186965867270413 62023048686445112200226405)
          ·
            refine ⟨11629321628708458537542451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62023048686445112200226405 11629321628708458537542451)
            ·
              refine ⟨17443982443062687806313677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629321628708458537542451 17443982443062687806313677)
              ·
                refine ⟨6541493416148507927367629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17443982443062687806313677 6541493416148507927367629)
                ·
                  refine ⟨2453060031055690472762861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6541493416148507927367629 2453060031055690472762861)
                  ·
                    refine ⟨919897511645883927286073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453060031055690472762861 919897511645883927286073)
                    ·
                      rfl

theorem cell22_2687241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_2687241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687241 prefixEnd_2687241 := by exact prefixLift 2687241
  have htrace : WordTrace (prefixWord ++ tailWord_2687241) baseStart_2687241 baseEnd_2687241 := by
    simpa [prefixWord, tailWord_2687241, baseEnd_2687241] using wordTrace_append hprefix tailTrace_2687241
  have hstable : (prefixWord ++ tailWord_2687241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687241).length < 2 ^ (prefixWord ++ tailWord_2687241).sum := by decide
  have hdescent : baseEnd_2687241 < baseStart_2687241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687331 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_2687331 : Nat := 118140960795 + 2687331 * 2 ^ 59
def prefixEnd_2687331 : Nat := 4983230072969 + 3 ^ 40 * 2687331 * 2
def baseEnd_2687331 : Nat := 919928320485153692535797

theorem tailTrace_2687331 : CollatzResearch.WordTrace tailWord_2687331 prefixEnd_2687331 919928320485153692535797 := by
  unfold tailWord_2687331
  simp only [CollatzResearch.WordTrace]
  refine ⟨98015013827266221440269847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65343342551510814293513231 98015013827266221440269847)
  ·
    refine ⟨147022520740899332160404771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98015013827266221440269847 147022520740899332160404771)
    ·
      refine ⟨220533781111348998240607157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147022520740899332160404771 220533781111348998240607157)
      ·
        refine ⟨20675041979188968585056921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220533781111348998240607157 20675041979188968585056921)
        ·
          refine ⟨15506281484391726438792691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20675041979188968585056921 15506281484391726438792691)
          ·
            refine ⟨23259422226587589658189037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15506281484391726438792691 23259422226587589658189037)
            ·
              refine ⟨8722283334970346121820889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23259422226587589658189037 8722283334970346121820889)
              ·
                refine ⟨6541712501227759591365667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8722283334970346121820889 6541712501227759591365667)
                ·
                  refine ⟨9812568751841639387048501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541712501227759591365667 9812568751841639387048501)
                  ·
                    refine ⟨919928320485153692535797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9812568751841639387048501 919928320485153692535797)
                    ·
                      rfl

theorem cell22_2687331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_2687331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687331 prefixEnd_2687331 := by exact prefixLift 2687331
  have htrace : WordTrace (prefixWord ++ tailWord_2687331) baseStart_2687331 baseEnd_2687331 := by
    simpa [prefixWord, tailWord_2687331, baseEnd_2687331] using wordTrace_append hprefix tailTrace_2687331
  have hstable : (prefixWord ++ tailWord_2687331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687331).length < 2 ^ (prefixWord ++ tailWord_2687331).sum := by decide
  have hdescent : baseEnd_2687331 < baseStart_2687331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687335 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2687335 : Nat := 118140960795 + 2687335 * 2 ^ 59
def prefixEnd_2687335 : Nat := 4983230072969 + 3 ^ 40 * 2687335 * 2
def baseEnd_2687335 : Nat := 919929689766899015435785

theorem tailTrace_2687335 : CollatzResearch.WordTrace tailWord_2687335 prefixEnd_2687335 919929689766899015435785 := by
  unfold tailWord_2687335
  simp only [CollatzResearch.WordTrace]
  refine ⟨98015159719251730123415459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65343439812834486748943639 98015159719251730123415459)
  ·
    refine ⟨147022739578877595185123189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98015159719251730123415459 147022739578877595185123189)
    ·
      refine ⟨13783381835519774548605299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147022739578877595185123189 13783381835519774548605299)
      ·
        refine ⟨20675072753279661822907949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783381835519774548605299 20675072753279661822907949)
        ·
          refine ⟨7753152282479873183590481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20675072753279661822907949 7753152282479873183590481)
          ·
            refine ⟨5814864211859904887692861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7753152282479873183590481 5814864211859904887692861)
            ·
              refine ⟨2180574079447464332884823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5814864211859904887692861 2180574079447464332884823)
              ·
                refine ⟨3270861119171196499327235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180574079447464332884823 3270861119171196499327235)
                ·
                  refine ⟨4906291678756794748990853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270861119171196499327235 4906291678756794748990853)
                  ·
                    refine ⟨919929689766899015435785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4906291678756794748990853 919929689766899015435785)
                    ·
                      rfl

theorem cell22_2687335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2687335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687335 prefixEnd_2687335 := by exact prefixLift 2687335
  have htrace : WordTrace (prefixWord ++ tailWord_2687335) baseStart_2687335 baseEnd_2687335 := by
    simpa [prefixWord, tailWord_2687335, baseEnd_2687335] using wordTrace_append hprefix tailTrace_2687335
  have hstable : (prefixWord ++ tailWord_2687335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687335).length < 2 ^ (prefixWord ++ tailWord_2687335).sum := by decide
  have hdescent : baseEnd_2687335 < baseStart_2687335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687344 : List Nat := [2, 1, 1, 1, 4, 13]
def baseStart_2687344 : Nat := 118140960795 + 2687344 * 2 ^ 59
def prefixEnd_2687344 : Nat := 4983230072969 + 3 ^ 40 * 2687344 * 2
def baseEnd_2687344 : Nat := 11357194699392913480997

theorem tailTrace_2687344 : CollatzResearch.WordTrace tailWord_2687344 prefixEnd_2687344 11357194699392913480997 := by
  unfold tailWord_2687344
  simp only [CollatzResearch.WordTrace]
  refine ⟨49007743988109562330246543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65343658650812749773662057 49007743988109562330246543)
  ·
    refine ⟨73511615982164343495369815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49007743988109562330246543 73511615982164343495369815)
    ·
      refine ⟨110267423973246515243054723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73511615982164343495369815 110267423973246515243054723)
      ·
        refine ⟨165401135959869772864582085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110267423973246515243054723 165401135959869772864582085)
        ·
          refine ⟨31012712992475582412109141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165401135959869772864582085 31012712992475582412109141)
          ·
            refine ⟨11357194699392913480997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31012712992475582412109141 11357194699392913480997)
            ·
              rfl

theorem cell22_2687344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 13].length) (baseStart_2687344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687344 prefixEnd_2687344 := by exact prefixLift 2687344
  have htrace : WordTrace (prefixWord ++ tailWord_2687344) baseStart_2687344 baseEnd_2687344 := by
    simpa [prefixWord, tailWord_2687344, baseEnd_2687344] using wordTrace_append hprefix tailTrace_2687344
  have hstable : (prefixWord ++ tailWord_2687344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687344).length < 2 ^ (prefixWord ++ tailWord_2687344).sum := by decide
  have hdescent : baseEnd_2687344 < baseStart_2687344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687410 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_2687410 : Nat := 118140960795 + 2687410 * 2 ^ 59
def prefixEnd_2687410 : Nat := 4983230072969 + 3 ^ 40 * 2687410 * 2
def baseEnd_2687410 : Nat := 919955363799623819810555

theorem tailTrace_2687410 : CollatzResearch.WordTrace tailWord_2687410 prefixEnd_2687410 919955363799623819810555 := by
  unfold tailWord_2687410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24504473798495004483098921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65345263462653345288263789 24504473798495004483098921)
  ·
    refine ⟨18378355348871253362324191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24504473798495004483098921 18378355348871253362324191)
    ·
      refine ⟨27567533023306880043486287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18378355348871253362324191 27567533023306880043486287)
      ·
        refine ⟨41351299534960320065229431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27567533023306880043486287 41351299534960320065229431)
        ·
          refine ⟨62026949302440480097844147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41351299534960320065229431 62026949302440480097844147)
          ·
            refine ⟨93040423953660720146766221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62026949302440480097844147 93040423953660720146766221)
            ·
              refine ⟨34890158982622770055037333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93040423953660720146766221 34890158982622770055037333)
              ·
                refine ⟨1635476202310442346329875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34890158982622770055037333 1635476202310442346329875)
                ·
                  refine ⟨2453214303465663519494813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635476202310442346329875 2453214303465663519494813)
                  ·
                    refine ⟨919955363799623819810555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453214303465663519494813 919955363799623819810555)
                    ·
                      rfl

theorem cell22_2687410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_2687410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687410 prefixEnd_2687410 := by exact prefixLift 2687410
  have htrace : WordTrace (prefixWord ++ tailWord_2687410) baseStart_2687410 baseEnd_2687410 := by
    simpa [prefixWord, tailWord_2687410, baseEnd_2687410] using wordTrace_append hprefix tailTrace_2687410
  have hstable : (prefixWord ++ tailWord_2687410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687410).length < 2 ^ (prefixWord ++ tailWord_2687410).sum := by decide
  have hdescent : baseEnd_2687410 < baseStart_2687410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687444 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_2687444 : Nat := 118140960795 + 2687444 * 2 ^ 59
def prefixEnd_2687444 : Nat := 4983230072969 + 3 ^ 40 * 2687444 * 2
def baseEnd_2687444 : Nat := 919967002694459064460451

theorem tailTrace_2687444 : CollatzResearch.WordTrace tailWord_2687444 prefixEnd_2687444 919967002694459064460451 := by
  unfold tailWord_2687444
  simp only [CollatzResearch.WordTrace]
  refine ⟨49009567637928420869566693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65346090183904561159422257 49009567637928420869566693)
  ·
    refine ⟨9189293932111578913043755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49009567637928420869566693 9189293932111578913043755)
    ·
      refine ⟨13783940898167368369565633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189293932111578913043755 13783940898167368369565633)
      ·
        refine ⟨10337955673625526277174225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13783940898167368369565633 10337955673625526277174225)
        ·
          refine ⟨7753466755219144707880669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10337955673625526277174225 7753466755219144707880669)
          ·
            refine ⟨2907550033207179265455251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7753466755219144707880669 2907550033207179265455251)
            ·
              refine ⟨4361325049810768898182877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907550033207179265455251 4361325049810768898182877)
              ·
                refine ⟨1635496893679038336818579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4361325049810768898182877 1635496893679038336818579)
                ·
                  refine ⟨2453245340518557505227869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635496893679038336818579 2453245340518557505227869)
                  ·
                    refine ⟨919967002694459064460451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453245340518557505227869 919967002694459064460451)
                    ·
                      rfl

theorem cell22_2687444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_2687444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687444 prefixEnd_2687444 := by exact prefixLift 2687444
  have htrace : WordTrace (prefixWord ++ tailWord_2687444) baseStart_2687444 baseEnd_2687444 := by
    simpa [prefixWord, tailWord_2687444, baseEnd_2687444] using wordTrace_append hprefix tailTrace_2687444
  have hstable : (prefixWord ++ tailWord_2687444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687444).length < 2 ^ (prefixWord ++ tailWord_2687444).sum := by decide
  have hdescent : baseEnd_2687444 < baseStart_2687444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687474 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_2687474 : Nat := 118140960795 + 2687474 * 2 ^ 59
def prefixEnd_2687474 : Nat := 4983230072969 + 3 ^ 40 * 2687474 * 2
def baseEnd_2687474 : Nat := 306659090769182995403453

theorem tailTrace_2687474 : CollatzResearch.WordTrace tailWord_2687474 prefixEnd_2687474 306659090769182995403453 := by
  unfold tailWord_2687474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505057366437039215681369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65346819643832104575150317 24505057366437039215681369)
  ·
    refine ⟨18378793024827779411761027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24505057366437039215681369 18378793024827779411761027)
    ·
      refine ⟨27568189537241669117641541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18378793024827779411761027 27568189537241669117641541)
      ·
        refine ⟨5169035538232812959557789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27568189537241669117641541 5169035538232812959557789)
        ·
          refine ⟨1938388326837304859834171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5169035538232812959557789 1938388326837304859834171)
          ·
            refine ⟨2907582490255957289751257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938388326837304859834171 2907582490255957289751257)
            ·
              refine ⟨2180686867691967967313443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907582490255957289751257 2180686867691967967313443)
              ·
                refine ⟨3271030301537951950970165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180686867691967967313443 3271030301537951950970165)
                ·
                  refine ⟨306659090769182995403453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3271030301537951950970165 306659090769182995403453)
                  ·
                    rfl

theorem cell22_2687474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_2687474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687474 prefixEnd_2687474 := by exact prefixLift 2687474
  have htrace : WordTrace (prefixWord ++ tailWord_2687474) baseStart_2687474 baseEnd_2687474 := by
    simpa [prefixWord, tailWord_2687474, baseEnd_2687474] using wordTrace_append hprefix tailTrace_2687474
  have hstable : (prefixWord ++ tailWord_2687474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687474).length < 2 ^ (prefixWord ++ tailWord_2687474).sum := by decide
  have hdescent : baseEnd_2687474 < baseStart_2687474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687481 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2687481 : Nat := 118140960795 + 2687481 * 2 ^ 59
def prefixEnd_2687481 : Nat := 4983230072969 + 3 ^ 40 * 2687481 * 2
def baseEnd_2687481 : Nat := 919979668550603301285337

theorem tailTrace_2687481 : CollatzResearch.WordTrace tailWord_2687481 prefixEnd_2687481 919979668550603301285337 := by
  unfold tailWord_2687481
  simp only [CollatzResearch.WordTrace]
  refine ⟨98020484776722797058230297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65346989851148531372153531 98020484776722797058230297)
  ·
    refine ⟨73515363582542097793672723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98020484776722797058230297 73515363582542097793672723)
    ·
      refine ⟨110273045373813146690509085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73515363582542097793672723 110273045373813146690509085)
      ·
        refine ⟨41352392015179930008940907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110273045373813146690509085 41352392015179930008940907)
        ·
          refine ⟨62028588022769895013411361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41352392015179930008940907 62028588022769895013411361)
          ·
            refine ⟨46521441017077421260058521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62028588022769895013411361 46521441017077421260058521)
            ·
              refine ⟨34891080762808065945043891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46521441017077421260058521 34891080762808065945043891)
              ·
                refine ⟨52336621144212098917565837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34891080762808065945043891 52336621144212098917565837)
                ·
                  refine ⟨19626232929079537094087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52336621144212098917565837 19626232929079537094087189)
                  ·
                    refine ⟨919979668550603301285337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19626232929079537094087189 919979668550603301285337)
                    ·
                      rfl

theorem cell22_2687481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2687481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687481 prefixEnd_2687481 := by exact prefixLift 2687481
  have htrace : WordTrace (prefixWord ++ tailWord_2687481) baseStart_2687481 baseEnd_2687481 := by
    simpa [prefixWord, tailWord_2687481, baseEnd_2687481] using wordTrace_append hprefix tailTrace_2687481
  have hstable : (prefixWord ++ tailWord_2687481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687481).length < 2 ^ (prefixWord ++ tailWord_2687481).sum := by decide
  have hdescent : baseEnd_2687481 < baseStart_2687481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687517 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2687517 : Nat := 118140960795 + 2687517 * 2 ^ 59
def prefixEnd_2687517 : Nat := 4983230072969 + 3 ^ 40 * 2687517 * 2
def baseEnd_2687517 : Nat := 919991992086311207385227

theorem tailTrace_2687517 : CollatzResearch.WordTrace tailWord_2687517 prefixEnd_2687517 919991992086311207385227 := by
  unfold tailWord_2687517
  simp only [CollatzResearch.WordTrace]
  refine ⟨98021797804592375206540805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65347865203061583471027203 98021797804592375206540805)
  ·
    refine ⟨18379087088361070351226401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98021797804592375206540805 18379087088361070351226401)
    ·
      refine ⟨13784315316270802763419801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18379087088361070351226401 13784315316270802763419801)
      ·
        refine ⟨10338236487203102072564851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13784315316270802763419801 10338236487203102072564851)
        ·
          refine ⟨15507354730804653108847277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338236487203102072564851 15507354730804653108847277)
          ·
            refine ⟨5815258024051744915817729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15507354730804653108847277 5815258024051744915817729)
            ·
              refine ⟨4361443518038808686863297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5815258024051744915817729 4361443518038808686863297)
              ·
                refine ⟨3271082638529106515147473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361443518038808686863297 3271082638529106515147473)
                ·
                  refine ⟨2453311978896829886360605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271082638529106515147473 2453311978896829886360605)
                  ·
                    refine ⟨919991992086311207385227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453311978896829886360605 919991992086311207385227)
                    ·
                      rfl

theorem cell22_2687517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2687517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687517 prefixEnd_2687517 := by exact prefixLift 2687517
  have htrace : WordTrace (prefixWord ++ tailWord_2687517) baseStart_2687517 baseEnd_2687517 := by
    simpa [prefixWord, tailWord_2687517, baseEnd_2687517] using wordTrace_append hprefix tailTrace_2687517
  have hstable : (prefixWord ++ tailWord_2687517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687517).length < 2 ^ (prefixWord ++ tailWord_2687517).sum := by decide
  have hdescent : baseEnd_2687517 < baseStart_2687517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687530 : List Nat := [3, 1, 4, 1, 1, 4, 1, 7]
def baseStart_2687530 : Nat := 118140960795 + 2687530 * 2 ^ 59
def prefixEnd_2687530 : Nat := 4983230072969 + 3 ^ 40 * 2687530 * 2
def baseEnd_2687530 : Nat := 102221826916887056312243

theorem tailTrace_2687530 : CollatzResearch.WordTrace tailWord_2687530 prefixEnd_2687530 102221826916887056312243 := by
  unfold tailWord_2687530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505567988386319606691011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65348181302363518951176029 24505567988386319606691011)
  ·
    refine ⟨36758351982579479410036517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24505567988386319606691011 36758351982579479410036517)
    ·
      refine ⟨6892190996733652389381847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36758351982579479410036517 6892190996733652389381847)
      ·
        refine ⟨10338286495100478584072771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892190996733652389381847 10338286495100478584072771)
        ·
          refine ⟨15507429742650717876109157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338286495100478584072771 15507429742650717876109157)
          ·
            refine ⟨2907643076747009601770467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15507429742650717876109157 2907643076747009601770467)
            ·
              refine ⟨4361464615120514402655701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907643076747009601770467 4361464615120514402655701)
              ·
                refine ⟨102221826916887056312243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4361464615120514402655701 102221826916887056312243)
                ·
                  rfl

theorem cell22_2687530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_2687530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687530 prefixEnd_2687530 := by exact prefixLift 2687530
  have htrace : WordTrace (prefixWord ++ tailWord_2687530) baseStart_2687530 baseEnd_2687530 := by
    simpa [prefixWord, tailWord_2687530, baseEnd_2687530] using wordTrace_append hprefix tailTrace_2687530
  have hstable : (prefixWord ++ tailWord_2687530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687530).length < 2 ^ (prefixWord ++ tailWord_2687530).sum := by decide
  have hdescent : baseEnd_2687530 < baseStart_2687530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687545 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 3, 3]
def baseStart_2687545 : Nat := 118140960795 + 2687545 * 2 ^ 59
def prefixEnd_2687545 : Nat := 4983230072969 + 3 ^ 40 * 2687545 * 2
def baseEnd_2687545 : Nat := 920001577058528467685141

theorem tailTrace_2687545 : CollatzResearch.WordTrace tailWord_2687545 prefixEnd_2687545 920001577058528467685141 := by
  unfold tailWord_2687545
  simp only [CollatzResearch.WordTrace]
  refine ⟨98022819048490935988560089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65348546032327290659040059 98022819048490935988560089)
  ·
    refine ⟨73517114286368201991420067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98022819048490935988560089 73517114286368201991420067)
    ·
      refine ⟨110275671429552302987130101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73517114286368201991420067 110275671429552302987130101)
      ·
        refine ⟨10338344196520528405043447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110275671429552302987130101 10338344196520528405043447)
        ·
          refine ⟨15507516294780792607565171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338344196520528405043447 15507516294780792607565171)
          ·
            refine ⟨23261274442171188911347757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15507516294780792607565171 23261274442171188911347757)
            ·
              refine ⟨8722977915814195841755409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23261274442171188911347757 8722977915814195841755409)
              ·
                refine ⟨6542233436860646881316557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8722977915814195841755409 6542233436860646881316557)
                ·
                  refine ⟨2453337538822742580493709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6542233436860646881316557 2453337538822742580493709)
                  ·
                    refine ⟨920001577058528467685141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453337538822742580493709 920001577058528467685141)
                    ·
                      rfl

theorem cell22_2687545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 3].length) (baseStart_2687545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687545 prefixEnd_2687545 := by exact prefixLift 2687545
  have htrace : WordTrace (prefixWord ++ tailWord_2687545) baseStart_2687545 baseEnd_2687545 := by
    simpa [prefixWord, tailWord_2687545, baseEnd_2687545] using wordTrace_append hprefix tailTrace_2687545
  have hstable : (prefixWord ++ tailWord_2687545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687545).length < 2 ^ (prefixWord ++ tailWord_2687545).sum := by decide
  have hdescent : baseEnd_2687545 < baseStart_2687545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687562 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2687562 : Nat := 118140960795 + 2687562 * 2 ^ 59
def prefixEnd_2687562 : Nat := 4983230072969 + 3 ^ 40 * 2687562 * 2
def baseEnd_2687562 : Nat := 920007396505946090010089

theorem tailTrace_2687562 : CollatzResearch.WordTrace tailWord_2687562 prefixEnd_2687562 920007396505946090010089 := by
  unfold tailWord_2687562
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505859772357336972982235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65348959392952898594619293 24505859772357336972982235)
  ·
    refine ⟨36758789658536005459473353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24505859772357336972982235 36758789658536005459473353)
    ·
      refine ⟨27569092243902004094605015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36758789658536005459473353 27569092243902004094605015)
      ·
        refine ⟨41353638365853006141907523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27569092243902004094605015 41353638365853006141907523)
        ·
          refine ⟨62030457548779509212861285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41353638365853006141907523 62030457548779509212861285)
          ·
            refine ⟨11630710790396157977411491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62030457548779509212861285 11630710790396157977411491)
            ·
              refine ⟨17446066185594236966117237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11630710790396157977411491 17446066185594236966117237)
              ·
                refine ⟨1635568704899459715573491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17446066185594236966117237 1635568704899459715573491)
                ·
                  refine ⟨2453353057349189573360237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635568704899459715573491 2453353057349189573360237)
                  ·
                    refine ⟨920007396505946090010089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453353057349189573360237 920007396505946090010089)
                    ·
                      rfl

theorem cell22_2687562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2687562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687562 prefixEnd_2687562 := by exact prefixLift 2687562
  have htrace : WordTrace (prefixWord ++ tailWord_2687562) baseStart_2687562 baseEnd_2687562 := by
    simpa [prefixWord, tailWord_2687562, baseEnd_2687562] using wordTrace_append hprefix tailTrace_2687562
  have hstable : (prefixWord ++ tailWord_2687562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687562).length < 2 ^ (prefixWord ++ tailWord_2687562).sum := by decide
  have hdescent : baseEnd_2687562 < baseStart_2687562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687573 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2687573 : Nat := 118140960795 + 2687573 * 2 ^ 59
def prefixEnd_2687573 : Nat := 4983230072969 + 3 ^ 40 * 2687573 * 2
def baseEnd_2687573 : Nat := 920011162030745727985055

theorem tailTrace_2687573 : CollatzResearch.WordTrace tailWord_2687573 prefixEnd_2687573 920011162030745727985055 := by
  unfold tailWord_2687573
  simp only [CollatzResearch.WordTrace]
  refine ⟨98023840292389496770579373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65349226861592997847052915 98023840292389496770579373)
  ·
    refine ⟨36758940109646061288967265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98023840292389496770579373 36758940109646061288967265)
    ·
      refine ⟨27569205082234545966725449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36758940109646061288967265 27569205082234545966725449)
      ·
        refine ⟨20676903811675909475044087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27569205082234545966725449 20676903811675909475044087)
        ·
          refine ⟨31015355717513864212566131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20676903811675909475044087 31015355717513864212566131)
          ·
            refine ⟨46523033576270796318849197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31015355717513864212566131 46523033576270796318849197)
            ·
              refine ⟨17446137591101548619568449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46523033576270796318849197 17446137591101548619568449)
              ·
                refine ⟨13084603193326161464676337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17446137591101548619568449 13084603193326161464676337)
                ·
                  refine ⟨9813452394994621098507253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13084603193326161464676337 9813452394994621098507253)
                  ·
                    refine ⟨920011162030745727985055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9813452394994621098507253 920011162030745727985055)
                    ·
                      rfl

theorem cell22_2687573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2687573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687573 prefixEnd_2687573 := by exact prefixLift 2687573
  have htrace : WordTrace (prefixWord ++ tailWord_2687573) baseStart_2687573 baseEnd_2687573 := by
    simpa [prefixWord, tailWord_2687573, baseEnd_2687573] using wordTrace_append hprefix tailTrace_2687573
  have hstable : (prefixWord ++ tailWord_2687573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687573).length < 2 ^ (prefixWord ++ tailWord_2687573).sum := by decide
  have hdescent : baseEnd_2687573 < baseStart_2687573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687652 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_2687652 : Nat := 118140960795 + 2687652 * 2 ^ 59
def prefixEnd_2687652 : Nat := 4983230072969 + 3 ^ 40 * 2687652 * 2
def baseEnd_2687652 : Nat := 920038205345215855259813

theorem tailTrace_2687652 : CollatzResearch.WordTrace tailWord_2687652 prefixEnd_2687652 920038205345215855259813 := by
  unfold tailWord_2687652
  simp only [CollatzResearch.WordTrace]
  refine ⟨49013360829551646631352605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65351147772735528841803473 49013360829551646631352605)
  ·
    refine ⟨18380010311081867486757227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49013360829551646631352605 18380010311081867486757227)
    ·
      refine ⟨27570015466622801230135841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18380010311081867486757227 27570015466622801230135841)
      ·
        refine ⟨20677511599967100922601881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27570015466622801230135841 20677511599967100922601881)
        ·
          refine ⟨15508133699975325691951411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20677511599967100922601881 15508133699975325691951411)
          ·
            refine ⟨23262200549962988537927117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15508133699975325691951411 23262200549962988537927117)
            ·
              refine ⟨8723325206236120701722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23262200549962988537927117 8723325206236120701722669)
              ·
                refine ⟨3271246952338545263146001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8723325206236120701722669 3271246952338545263146001)
                ·
                  refine ⟨2453435214253908947359501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271246952338545263146001 2453435214253908947359501)
                  ·
                    refine ⟨920038205345215855259813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453435214253908947359501 920038205345215855259813)
                    ·
                      rfl

theorem cell22_2687652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_2687652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687652 prefixEnd_2687652 := by exact prefixLift 2687652
  have htrace : WordTrace (prefixWord ++ tailWord_2687652) baseStart_2687652 baseEnd_2687652 := by
    simpa [prefixWord, tailWord_2687652, baseEnd_2687652] using wordTrace_append hprefix tailTrace_2687652
  have hstable : (prefixWord ++ tailWord_2687652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687652).length < 2 ^ (prefixWord ++ tailWord_2687652).sum := by decide
  have hdescent : baseEnd_2687652 < baseStart_2687652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687725 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2687725 : Nat := 118140960795 + 2687725 * 2 ^ 59
def prefixEnd_2687725 : Nat := 4983230072969 + 3 ^ 40 * 2687725 * 2
def baseEnd_2687725 : Nat := 920063194737067998184589

theorem tailTrace_2687725 : CollatzResearch.WordTrace tailWord_2687725 prefixEnd_2687725 920063194737067998184589 := by
  unfold tailWord_2687725
  simp only [CollatzResearch.WordTrace]
  refine ⟨98029384187838826730112629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65352922791892551153408419 98029384187838826730112629)
  ·
    refine ⟨9190254767609890005948059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98029384187838826730112629 9190254767609890005948059)
    ·
      refine ⟨13785382151414835008922089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190254767609890005948059 13785382151414835008922089)
      ·
        refine ⟨10339036613561126256691567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13785382151414835008922089 10339036613561126256691567)
        ·
          refine ⟨15508554920341689385037351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10339036613561126256691567 15508554920341689385037351)
          ·
            refine ⟨23262832380512534077556027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15508554920341689385037351 23262832380512534077556027)
            ·
              refine ⟨34894248570768801116334041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23262832380512534077556027 34894248570768801116334041)
              ·
                refine ⟨26170686428076600837250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34894248570768801116334041 26170686428076600837250531)
                ·
                  refine ⟨39256029642114901255875797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26170686428076600837250531 39256029642114901255875797)
                  ·
                    refine ⟨920063194737067998184589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39256029642114901255875797 920063194737067998184589)
                    ·
                      rfl

theorem cell22_2687725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2687725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687725 prefixEnd_2687725 := by exact prefixLift 2687725
  have htrace : WordTrace (prefixWord ++ tailWord_2687725) baseStart_2687725 baseEnd_2687725 := by
    simpa [prefixWord, tailWord_2687725, baseEnd_2687725] using wordTrace_append hprefix tailTrace_2687725
  have hstable : (prefixWord ++ tailWord_2687725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687725).length < 2 ^ (prefixWord ++ tailWord_2687725).sum := by decide
  have hdescent : baseEnd_2687725 < baseStart_2687725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687742 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2687742 : Nat := 118140960795 + 2687742 * 2 ^ 59
def prefixEnd_2687742 : Nat := 4983230072969 + 3 ^ 40 * 2687742 * 2
def baseEnd_2687742 : Nat := 920069014184485620509537

theorem tailTrace_2687742 : CollatzResearch.WordTrace tailWord_2687742 prefixEnd_2687742 920069014184485620509537 := by
  unfold tailWord_2687742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12253750528597154829185185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65353336152518159088987653 12253750528597154829185185)
  ·
    refine ⟨9190312896447866121888889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12253750528597154829185185 9190312896447866121888889)
    ·
      refine ⟨6892734672335899591416667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9190312896447866121888889 6892734672335899591416667)
      ·
        refine ⟨10339102008503849387125001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892734672335899591416667 10339102008503849387125001)
        ·
          refine ⟨7754326506377887040343751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10339102008503849387125001 7754326506377887040343751)
          ·
            refine ⟨11631489759566830560515627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754326506377887040343751 11631489759566830560515627)
            ·
              refine ⟨17447234639350245840773441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11631489759566830560515627 17447234639350245840773441)
              ·
                refine ⟨13085425979512684380580081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17447234639350245840773441 13085425979512684380580081)
                ·
                  refine ⟨9814069484634513285435061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13085425979512684380580081 9814069484634513285435061)
                  ·
                    refine ⟨920069014184485620509537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9814069484634513285435061 920069014184485620509537)
                    ·
                      rfl

theorem cell22_2687742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2687742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687742 prefixEnd_2687742 := by exact prefixLift 2687742
  have htrace : WordTrace (prefixWord ++ tailWord_2687742) baseStart_2687742 baseEnd_2687742 := by
    simpa [prefixWord, tailWord_2687742, baseEnd_2687742] using wordTrace_append hprefix tailTrace_2687742
  have hstable : (prefixWord ++ tailWord_2687742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687742).length < 2 ^ (prefixWord ++ tailWord_2687742).sum := by decide
  have hdescent : baseEnd_2687742 < baseStart_2687742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687806 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2687806 : Nat := 118140960795 + 2687806 * 2 ^ 59
def prefixEnd_2687806 : Nat := 4983230072969 + 3 ^ 40 * 2687806 * 2
def baseEnd_2687806 : Nat := 306696974230803595636447

theorem tailTrace_2687806 : CollatzResearch.WordTrace tailWord_2687806 prefixEnd_2687806 306696974230803595636447 := by
  unfold tailWord_2687806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254042312568172195476409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65354892333696918375874181 12254042312568172195476409)
  ·
    refine ⟨9190531734426129146607307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254042312568172195476409 9190531734426129146607307)
    ·
      refine ⟨13785797601639193719910961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190531734426129146607307 13785797601639193719910961)
      ·
        refine ⟨10339348201229395289933221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13785797601639193719910961 10339348201229395289933221)
        ·
          refine ⟨1938627787730511616862479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10339348201229395289933221 1938627787730511616862479)
          ·
            refine ⟨2907941681595767425293719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938627787730511616862479 2907941681595767425293719)
            ·
              refine ⟨4361912522393651137940579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907941681595767425293719 4361912522393651137940579)
              ·
                refine ⟨6542868783590476706910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361912522393651137940579 6542868783590476706910869)
                ·
                  refine ⟨306696974230803595636447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6542868783590476706910869 306696974230803595636447)
                  ·
                    rfl

theorem cell22_2687806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2687806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687806 prefixEnd_2687806 := by exact prefixLift 2687806
  have htrace : WordTrace (prefixWord ++ tailWord_2687806) baseStart_2687806 baseEnd_2687806 := by
    simpa [prefixWord, tailWord_2687806, baseEnd_2687806] using wordTrace_append hprefix tailTrace_2687806
  have hstable : (prefixWord ++ tailWord_2687806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687806).length < 2 ^ (prefixWord ++ tailWord_2687806).sum := by decide
  have hdescent : baseEnd_2687806 < baseStart_2687806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687832 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_2687832 : Nat := 118140960795 + 2687832 * 2 ^ 59
def prefixEnd_2687832 : Nat := 4983230072969 + 3 ^ 40 * 2687832 * 2
def baseEnd_2687832 : Nat := 920099823023755385759261

theorem tailTrace_2687832 : CollatzResearch.WordTrace tailWord_2687832 prefixEnd_2687832 920099823023755385759261 := by
  unfold tailWord_2687832
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016643399225592002128875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65355524532300789336171833 49016643399225592002128875)
  ·
    refine ⟨73524965098838388003193313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49016643399225592002128875 73524965098838388003193313)
    ·
      refine ⟨55143723824128791002394985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73524965098838388003193313 55143723824128791002394985)
      ·
        refine ⟨41357792868096593251796239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55143723824128791002394985 41357792868096593251796239)
        ·
          refine ⟨62036689302144889877694359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41357792868096593251796239 62036689302144889877694359)
          ·
            refine ⟨93055033953217334816541539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62036689302144889877694359 93055033953217334816541539)
            ·
              refine ⟨139582550929826002224812309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93055033953217334816541539 139582550929826002224812309)
              ·
                refine ⟨6542932074835593854288077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139582550929826002224812309 6542932074835593854288077)
                ·
                  refine ⟨2453599528063347695358029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6542932074835593854288077 2453599528063347695358029)
                  ·
                    refine ⟨920099823023755385759261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453599528063347695358029 920099823023755385759261)
                    ·
                      rfl

theorem cell22_2687832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_2687832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687832 prefixEnd_2687832 := by exact prefixLift 2687832
  have htrace : WordTrace (prefixWord ++ tailWord_2687832) baseStart_2687832 baseEnd_2687832 := by
    simpa [prefixWord, tailWord_2687832, baseEnd_2687832] using wordTrace_append hprefix tailTrace_2687832
  have hstable : (prefixWord ++ tailWord_2687832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687832).length < 2 ^ (prefixWord ++ tailWord_2687832).sum := by decide
  have hdescent : baseEnd_2687832 < baseStart_2687832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687845 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 9]
def baseStart_2687845 : Nat := 118140960795 + 2687845 * 2 ^ 59
def prefixEnd_2687845 : Nat := 4983230072969 + 3 ^ 40 * 2687845 * 2
def baseEnd_2687845 : Nat := 306701424396475895061407

theorem tailTrace_2687845 : CollatzResearch.WordTrace tailWord_2687845 prefixEnd_2687845 306701424396475895061407 := by
  unfold tailWord_2687845
  simp only [CollatzResearch.WordTrace]
  refine ⟨98033760947404087224480989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65355840631602724816320659 98033760947404087224480989)
  ·
    refine ⟨36762660355276532709180371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98033760947404087224480989 36762660355276532709180371)
    ·
      refine ⟨55143990532914799063770557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36762660355276532709180371 55143990532914799063770557)
      ·
        refine ⟨20678996449843049648913959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55143990532914799063770557 20678996449843049648913959)
        ·
          refine ⟨31018494674764574473370939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20678996449843049648913959 31018494674764574473370939)
          ·
            refine ⟨46527742012146861710056409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31018494674764574473370939 46527742012146861710056409)
            ·
              refine ⟨34895806509110146282542307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46527742012146861710056409 34895806509110146282542307)
              ·
                refine ⟨52343709763665219423813461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34895806509110146282542307 52343709763665219423813461)
                ·
                  refine ⟨306701424396475895061407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52343709763665219423813461 306701424396475895061407)
                  ·
                    rfl

theorem cell22_2687845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_2687845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687845 prefixEnd_2687845 := by exact prefixLift 2687845
  have htrace : WordTrace (prefixWord ++ tailWord_2687845) baseStart_2687845 baseEnd_2687845 := by
    simpa [prefixWord, tailWord_2687845, baseEnd_2687845] using wordTrace_append hprefix tailTrace_2687845
  have hstable : (prefixWord ++ tailWord_2687845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687845).length < 2 ^ (prefixWord ++ tailWord_2687845).sum := by decide
  have hdescent : baseEnd_2687845 < baseStart_2687845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687877 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2687877 : Nat := 118140960795 + 2687877 * 2 ^ 59
def prefixEnd_2687877 : Nat := 4983230072969 + 3 ^ 40 * 2687877 * 2
def baseEnd_2687877 : Nat := 920115227443390268384123

theorem tailTrace_2687877 : CollatzResearch.WordTrace tailWord_2687877 prefixEnd_2687877 920115227443390268384123 := by
  unfold tailWord_2687877
  simp only [CollatzResearch.WordTrace]
  refine ⟨98034928083288156689645885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65356618722192104459763923 98034928083288156689645885)
  ·
    refine ⟨36763098031233058758617207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98034928083288156689645885 36763098031233058758617207)
    ·
      refine ⟨55144647046849588137925811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36763098031233058758617207 55144647046849588137925811)
      ·
        refine ⟨82716970570274382206888717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55144647046849588137925811 82716970570274382206888717)
        ·
          refine ⟨31018863963852893327583269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82716970570274382206888717 31018863963852893327583269)
          ·
            refine ⟨5816036993222417498921863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31018863963852893327583269 5816036993222417498921863)
            ·
              refine ⟨8724055489833626248382795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816036993222417498921863 8724055489833626248382795)
              ·
                refine ⟨13086083234750439372574193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724055489833626248382795 13086083234750439372574193)
                ·
                  refine ⟨9814562426062829529430645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13086083234750439372574193 9814562426062829529430645)
                  ·
                    refine ⟨920115227443390268384123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9814562426062829529430645 920115227443390268384123)
                    ·
                      rfl

theorem cell22_2687877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2687877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687877 prefixEnd_2687877 := by exact prefixLift 2687877
  have htrace : WordTrace (prefixWord ++ tailWord_2687877) baseStart_2687877 baseEnd_2687877 := by
    simpa [prefixWord, tailWord_2687877, baseEnd_2687877] using wordTrace_append hprefix tailTrace_2687877
  have hstable : (prefixWord ++ tailWord_2687877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687877).length < 2 ^ (prefixWord ++ tailWord_2687877).sum := by decide
  have hdescent : baseEnd_2687877 < baseStart_2687877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687954 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2687954 : Nat := 118140960795 + 2687954 * 2 ^ 59
def prefixEnd_2687954 : Nat := 4983230072969 + 3 ^ 40 * 2687954 * 2
def baseEnd_2687954 : Nat := 920141586116987734208887

theorem tailTrace_2687954 : CollatzResearch.WordTrace tailWord_2687954 prefixEnd_2687954 920141586116987734208887 := by
  unfold tailWord_2687954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509434126002299710049729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65358491002672799226799277 24509434126002299710049729)
  ·
    refine ⟨18382075594501724782537297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24509434126002299710049729 18382075594501724782537297)
    ·
      refine ⟨13786556695876293586902973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18382075594501724782537297 13786556695876293586902973)
      ·
        refine ⟨5169958760953610095088615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13786556695876293586902973 5169958760953610095088615)
        ·
          refine ⟨7754938141430415142632923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169958760953610095088615 7754938141430415142632923)
          ·
            refine ⟨11632407212145622713949385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754938141430415142632923 11632407212145622713949385)
            ·
              refine ⟨8724305409109217035462039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11632407212145622713949385 8724305409109217035462039)
              ·
                refine ⟨13086458113663825553193059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724305409109217035462039 13086458113663825553193059)
                ·
                  refine ⟨19629687170495738329789589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13086458113663825553193059 19629687170495738329789589)
                  ·
                    refine ⟨920141586116987734208887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19629687170495738329789589 920141586116987734208887)
                    ·
                      rfl

theorem cell22_2687954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2687954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687954 prefixEnd_2687954 := by exact prefixLift 2687954
  have htrace : WordTrace (prefixWord ++ tailWord_2687954) baseStart_2687954 baseEnd_2687954 := by
    simpa [prefixWord, tailWord_2687954, baseEnd_2687954] using wordTrace_append hprefix tailTrace_2687954
  have hstable : (prefixWord ++ tailWord_2687954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687954).length < 2 ^ (prefixWord ++ tailWord_2687954).sum := by decide
  have hdescent : baseEnd_2687954 < baseStart_2687954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687958 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2687958 : Nat := 118140960795 + 2687958 * 2 ^ 59
def prefixEnd_2687958 : Nat := 4983230072969 + 3 ^ 40 * 2687958 * 2
def baseEnd_2687958 : Nat := 306714318466244352369625

theorem tailTrace_2687958 : CollatzResearch.WordTrace tailWord_2687958 prefixEnd_2687958 306714318466244352369625 := by
  unfold tailWord_2687958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127367649749669220209033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65358588263996471682229685 6127367649749669220209033)
  ·
    refine ⟨4595525737312251915156775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6127367649749669220209033 4595525737312251915156775)
    ·
      refine ⟨6893288605968377872735163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595525737312251915156775 6893288605968377872735163)
      ·
        refine ⟨10339932908952566809102745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6893288605968377872735163 10339932908952566809102745)
        ·
          refine ⟨7754949681714425106827059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10339932908952566809102745 7754949681714425106827059)
          ·
            refine ⟨11632424522571637660240589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754949681714425106827059 11632424522571637660240589)
            ·
              refine ⟨4362159195964364122590221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11632424522571637660240589 4362159195964364122590221)
              ·
                refine ⟨1635809698486636545971333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4362159195964364122590221 1635809698486636545971333)
                ·
                  refine ⟨306714318466244352369625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635809698486636545971333 306714318466244352369625)
                  ·
                    rfl

theorem cell22_2687958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2687958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687958 prefixEnd_2687958 := by exact prefixLift 2687958
  have htrace : WordTrace (prefixWord ++ tailWord_2687958) baseStart_2687958 baseEnd_2687958 := by
    simpa [prefixWord, tailWord_2687958, baseEnd_2687958] using wordTrace_append hprefix tailTrace_2687958
  have hstable : (prefixWord ++ tailWord_2687958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687958).length < 2 ^ (prefixWord ++ tailWord_2687958).sum := by decide
  have hdescent : baseEnd_2687958 < baseStart_2687958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687986 : List Nat := [3, 2, 1, 5, 1, 1, 2, 7]
def baseStart_2687986 : Nat := 118140960795 + 2687986 * 2 ^ 59
def prefixEnd_2687986 : Nat := 4983230072969 + 3 ^ 40 * 2687986 * 2
def baseEnd_2687986 : Nat := 102239171152327813045421

theorem tailTrace_2687986 : CollatzResearch.WordTrace tailWord_2687986 prefixEnd_2687986 102239171152327813045421 := by
  unfold tailWord_2687986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24509725909973317076340953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65359269093262178870242541 24509725909973317076340953)
  ·
    refine ⟨18382294432479987807255715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24509725909973317076340953 18382294432479987807255715)
    ·
      refine ⟨27573441648719981710883573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18382294432479987807255715 27573441648719981710883573)
      ·
        refine ⟨2585010154567498285395335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27573441648719981710883573 2585010154567498285395335)
        ·
          refine ⟨3877515231851247428093003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585010154567498285395335 3877515231851247428093003)
          ·
            refine ⟨5816272847776871142139505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877515231851247428093003 5816272847776871142139505)
            ·
              refine ⟨4362204635832653356604629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816272847776871142139505 4362204635832653356604629)
              ·
                refine ⟨102239171152327813045421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4362204635832653356604629 102239171152327813045421)
                ·
                  rfl

theorem cell22_2687986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_2687986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687986 prefixEnd_2687986 := by exact prefixLift 2687986
  have htrace : WordTrace (prefixWord ++ tailWord_2687986) baseStart_2687986 baseEnd_2687986 := by
    simpa [prefixWord, tailWord_2687986, baseEnd_2687986] using wordTrace_append hprefix tailTrace_2687986
  have hstable : (prefixWord ++ tailWord_2687986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687986).length < 2 ^ (prefixWord ++ tailWord_2687986).sum := by decide
  have hdescent : baseEnd_2687986 < baseStart_2687986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2687990 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2687990 : Nat := 118140960795 + 2687990 * 2 ^ 59
def prefixEnd_2687990 : Nat := 4983230072969 + 3 ^ 40 * 2687990 * 2
def baseEnd_2687990 : Nat := 920153909652695640308777

theorem tailTrace_2687990 : CollatzResearch.WordTrace tailWord_2687990 prefixEnd_2687990 920153909652695640308777 := by
  unfold tailWord_2687990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127440595742423561781839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65359366354585851325672949 6127440595742423561781839)
  ·
    refine ⟨9191160893613635342672759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6127440595742423561781839 9191160893613635342672759)
    ·
      refine ⟨13786741340420453014009139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191160893613635342672759 13786741340420453014009139)
      ·
        refine ⟨20680112010630679521013709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786741340420453014009139 20680112010630679521013709)
        ·
          refine ⟨7755042003986504820380141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20680112010630679521013709 7755042003986504820380141)
          ·
            refine ⟨2908140751494939307642553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7755042003986504820380141 2908140751494939307642553)
            ·
              refine ⟨2181105563621204480731915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908140751494939307642553 2181105563621204480731915)
              ·
                refine ⟨3271658345431806721097873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181105563621204480731915 3271658345431806721097873)
                ·
                  refine ⟨2453743759073855040823405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271658345431806721097873 2453743759073855040823405)
                  ·
                    refine ⟨920153909652695640308777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453743759073855040823405 920153909652695640308777)
                    ·
                      rfl

theorem cell22_2687990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2687990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2687990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2687990 prefixEnd_2687990 := by exact prefixLift 2687990
  have htrace : WordTrace (prefixWord ++ tailWord_2687990) baseStart_2687990 baseEnd_2687990 := by
    simpa [prefixWord, tailWord_2687990, baseEnd_2687990] using wordTrace_append hprefix tailTrace_2687990
  have hstable : (prefixWord ++ tailWord_2687990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2687990).length < 2 ^ (prefixWord ++ tailWord_2687990).sum := by decide
  have hdescent : baseEnd_2687990 < baseStart_2687990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2687990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688035 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 1, 3]
def baseStart_2688035 : Nat := 118140960795 + 2688035 * 2 ^ 59
def prefixEnd_2688035 : Nat := 4983230072969 + 3 ^ 40 * 2688035 * 2
def baseEnd_2688035 : Nat := 920169314072330522933639

theorem tailTrace_2688035 : CollatzResearch.WordTrace tailWord_2688035 prefixEnd_2688035 920169314072330522933639 := by
  unfold tailWord_2688035
  simp only [CollatzResearch.WordTrace]
  refine ⟨98040690816715749673897559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65360460544477166449265039 98040690816715749673897559)
  ·
    refine ⟨147061036225073624510846339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98040690816715749673897559 147061036225073624510846339)
    ·
      refine ⟨220591554337610436766269509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147061036225073624510846339 220591554337610436766269509)
      ·
        refine ⟨41360916438301956893675533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220591554337610436766269509 41360916438301956893675533)
        ·
          refine ⟨15510343664363233835128325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41360916438301956893675533 15510343664363233835128325)
          ·
            refine ⟨2908189437068106344086561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15510343664363233835128325 2908189437068106344086561)
            ·
              refine ⟨2181142077801079758064921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908189437068106344086561 2181142077801079758064921)
              ·
                refine ⟨1635856558350809818548691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181142077801079758064921 1635856558350809818548691)
                ·
                  refine ⟨2453784837526214727823037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1635856558350809818548691 2453784837526214727823037)
                  ·
                    refine ⟨920169314072330522933639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453784837526214727823037 920169314072330522933639)
                    ·
                      rfl

theorem cell22_2688035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 1, 3].length) (baseStart_2688035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688035 prefixEnd_2688035 := by exact prefixLift 2688035
  have htrace : WordTrace (prefixWord ++ tailWord_2688035) baseStart_2688035 baseEnd_2688035 := by
    simpa [prefixWord, tailWord_2688035, baseEnd_2688035] using wordTrace_append hprefix tailTrace_2688035
  have hstable : (prefixWord ++ tailWord_2688035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688035).length < 2 ^ (prefixWord ++ tailWord_2688035).sum := by decide
  have hdescent : baseEnd_2688035 < baseStart_2688035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688074 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2688074 : Nat := 118140960795 + 2688074 * 2 ^ 59
def prefixEnd_2688074 : Nat := 4983230072969 + 3 ^ 40 * 2688074 * 2
def baseEnd_2688074 : Nat := 920182664569347421208519

theorem tailTrace_2688074 : CollatzResearch.WordTrace tailWord_2688074 prefixEnd_2688074 920182664569347421208519 := by
  unfold tailWord_2688074
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510528315893614833641819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65361408842382972889711517 24510528315893614833641819)
  ·
    refine ⟨36765792473840422250462729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24510528315893614833641819 36765792473840422250462729)
    ·
      refine ⟨27574344355380316687847047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36765792473840422250462729 27574344355380316687847047)
      ·
        refine ⟨41361516533070475031770571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27574344355380316687847047 41361516533070475031770571)
        ·
          refine ⟨62042274799605712547655857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41361516533070475031770571 62042274799605712547655857)
          ·
            refine ⟨46531706099704284410741893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62042274799605712547655857 46531706099704284410741893)
            ·
              refine ⟨8724694893694553327014105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46531706099704284410741893 8724694893694553327014105)
              ·
                refine ⟨6543521170270914995260579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8724694893694553327014105 6543521170270914995260579)
                ·
                  refine ⟨9815281755406372492890869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543521170270914995260579 9815281755406372492890869)
                  ·
                    refine ⟨920182664569347421208519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9815281755406372492890869 920182664569347421208519)
                    ·
                      rfl

theorem cell22_2688074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2688074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688074 prefixEnd_2688074 := by exact prefixLift 2688074
  have htrace : WordTrace (prefixWord ++ tailWord_2688074) baseStart_2688074 baseEnd_2688074 := by
    simpa [prefixWord, tailWord_2688074, baseEnd_2688074] using wordTrace_append hprefix tailTrace_2688074
  have hstable : (prefixWord ++ tailWord_2688074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688074).length < 2 ^ (prefixWord ++ tailWord_2688074).sum := by decide
  have hdescent : baseEnd_2688074 < baseStart_2688074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688093 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2688093 : Nat := 118140960795 + 2688093 * 2 ^ 59
def prefixEnd_2688093 : Nat := 4983230072969 + 3 ^ 40 * 2688093 * 2
def baseEnd_2688093 : Nat := 306729722885879234994487

theorem tailTrace_2688093 : CollatzResearch.WordTrace tailWord_2688093 prefixEnd_2688093 306729722885879234994487 := by
  unfold tailWord_2688093
  simp only [CollatzResearch.WordTrace]
  refine ⟨98042806250505625579508933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65361870833670417053005955 98042806250505625579508933)
  ·
    refine ⟨18383026171969804796157925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98042806250505625579508933 18383026171969804796157925)
    ·
      refine ⟨3446817407244338399279611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18383026171969804796157925 3446817407244338399279611)
      ·
        refine ⟨5170226110866507598919417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446817407244338399279611 5170226110866507598919417)
        ·
          refine ⟨3877669583149880699189563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170226110866507598919417 3877669583149880699189563)
          ·
            refine ⟨5816504374724821048784345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877669583149880699189563 5816504374724821048784345)
            ·
              refine ⟨4362378281043615786588259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816504374724821048784345 4362378281043615786588259)
              ·
                refine ⟨6543567421565423679882389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362378281043615786588259 6543567421565423679882389)
                ·
                  refine ⟨306729722885879234994487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6543567421565423679882389 306729722885879234994487)
                  ·
                    rfl

theorem cell22_2688093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2688093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688093 prefixEnd_2688093 := by exact prefixLift 2688093
  have htrace : WordTrace (prefixWord ++ tailWord_2688093) baseStart_2688093 baseEnd_2688093 := by
    simpa [prefixWord, tailWord_2688093, baseEnd_2688093] using wordTrace_append hprefix tailTrace_2688093
  have hstable : (prefixWord ++ tailWord_2688093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688093).length < 2 ^ (prefixWord ++ tailWord_2688093).sum := by decide
  have hdescent : baseEnd_2688093 < baseStart_2688093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688108 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_2688108 : Nat := 118140960795 + 2688108 * 2 ^ 59
def prefixEnd_2688108 : Nat := 4983230072969 + 3 ^ 40 * 2688108 * 2
def baseEnd_2688108 : Nat := 920194303464182665858415

theorem tailTrace_2688108 : CollatzResearch.WordTrace tailWord_2688108 prefixEnd_2688108 920194303464182665858415 := by
  unfold tailWord_2688108
  simp only [CollatzResearch.WordTrace]
  refine ⟨49021676672725641570652489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65362235563634188760869985 49021676672725641570652489)
  ·
    refine ⟨36766257504544231177989367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49021676672725641570652489 36766257504544231177989367)
    ·
      refine ⟨55149386256816346766984051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36766257504544231177989367 55149386256816346766984051)
      ·
        refine ⟨82724079385224520150476077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55149386256816346766984051 82724079385224520150476077)
        ·
          refine ⟨31021529769459195056428529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82724079385224520150476077 31021529769459195056428529)
          ·
            refine ⟨23266147327094396292321397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31021529769459195056428529 23266147327094396292321397)
            ·
              refine ⟨2181201311915099652405131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23266147327094396292321397 2181201311915099652405131)
              ·
                refine ⟨3271801967872649478607697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181201311915099652405131 3271801967872649478607697)
                ·
                  refine ⟨2453851475904487108955773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271801967872649478607697 2453851475904487108955773)
                  ·
                    refine ⟨920194303464182665858415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453851475904487108955773 920194303464182665858415)
                    ·
                      rfl

theorem cell22_2688108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_2688108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688108 prefixEnd_2688108 := by exact prefixLift 2688108
  have htrace : WordTrace (prefixWord ++ tailWord_2688108) baseStart_2688108 baseEnd_2688108 := by
    simpa [prefixWord, tailWord_2688108, baseEnd_2688108] using wordTrace_append hprefix tailTrace_2688108
  have hstable : (prefixWord ++ tailWord_2688108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688108).length < 2 ^ (prefixWord ++ tailWord_2688108).sum := by decide
  have hdescent : baseEnd_2688108 < baseStart_2688108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688209 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_2688209 : Nat := 118140960795 + 2688209 * 2 ^ 59
def prefixEnd_2688209 : Nat := 4983230072969 + 3 ^ 40 * 2688209 * 2
def baseEnd_2688209 : Nat := 920228877828252069083105

theorem tailTrace_2688209 : CollatzResearch.WordTrace tailWord_2688209 prefixEnd_2688209 920228877828252069083105 := by
  unfold tailWord_2688209
  simp only [CollatzResearch.WordTrace]
  refine ⟨98047037118085377390731681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65364691412056918260487787 98047037118085377390731681)
  ·
    refine ⟨73535277838564033043048761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98047037118085377390731681 73535277838564033043048761)
    ·
      refine ⟨55151458378923024782286571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73535277838564033043048761 55151458378923024782286571)
      ·
        refine ⟨82727187568384537173429857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55151458378923024782286571 82727187568384537173429857)
        ·
          refine ⟨62045390676288402880072393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82727187568384537173429857 62045390676288402880072393)
          ·
            refine ⟨46534043007216302160054295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62045390676288402880072393 46534043007216302160054295)
            ·
              refine ⟨69801064510824453240081443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46534043007216302160054295 69801064510824453240081443)
              ·
                refine ⟨104701596766236679860122165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69801064510824453240081443 104701596766236679860122165)
                ·
                  refine ⟨9815774696834688736886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104701596766236679860122165 9815774696834688736886453)
                  ·
                    refine ⟨920228877828252069083105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9815774696834688736886453 920228877828252069083105)
                    ·
                      rfl

theorem cell22_2688209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_2688209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688209 prefixEnd_2688209 := by exact prefixLift 2688209
  have htrace : WordTrace (prefixWord ++ tailWord_2688209) baseStart_2688209 baseEnd_2688209 := by
    simpa [prefixWord, tailWord_2688209, baseEnd_2688209] using wordTrace_append hprefix tailTrace_2688209
  have hstable : (prefixWord ++ tailWord_2688209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688209).length < 2 ^ (prefixWord ++ tailWord_2688209).sum := by decide
  have hdescent : baseEnd_2688209 < baseStart_2688209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688211 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 4]
def baseStart_2688211 : Nat := 118140960795 + 2688211 * 2 ^ 59
def prefixEnd_2688211 : Nat := 4983230072969 + 3 ^ 40 * 2688211 * 2
def baseEnd_2688211 : Nat := 306743187489708243511033

theorem tailTrace_2688211 : CollatzResearch.WordTrace tailWord_2688211 prefixEnd_2688211 306743187489708243511033 := by
  unfold tailWord_2688211
  simp only [CollatzResearch.WordTrace]
  refine ⟨98047110064078131732304487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65364740042718754488202991 98047110064078131732304487)
  ·
    refine ⟨147070665096117197598456731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98047110064078131732304487 147070665096117197598456731)
    ·
      refine ⟨220605997644175796397685097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147070665096117197598456731 220605997644175796397685097)
      ·
        refine ⟨165454498233131847298263823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220605997644175796397685097 165454498233131847298263823)
        ·
          refine ⟨248181747349697770947395735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165454498233131847298263823 248181747349697770947395735)
          ·
            refine ⟨372272621024546656421093603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248181747349697770947395735 372272621024546656421093603)
            ·
              refine ⟨558408931536819984631640405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372272621024546656421093603 558408931536819984631640405)
              ·
                refine ⟨1635963666611777298725509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 558408931536819984631640405 1635963666611777298725509)
                ·
                  refine ⟨306743187489708243511033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635963666611777298725509 306743187489708243511033)
                  ·
                    rfl

theorem cell22_2688211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 4].length) (baseStart_2688211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688211 prefixEnd_2688211 := by exact prefixLift 2688211
  have htrace : WordTrace (prefixWord ++ tailWord_2688211) baseStart_2688211 baseEnd_2688211 := by
    simpa [prefixWord, tailWord_2688211, baseEnd_2688211] using wordTrace_append hprefix tailTrace_2688211
  have hstable : (prefixWord ++ tailWord_2688211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688211).length < 2 ^ (prefixWord ++ tailWord_2688211).sum := by decide
  have hdescent : baseEnd_2688211 < baseStart_2688211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688260 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_2688260 : Nat := 118140960795 + 2688260 * 2 ^ 59
def prefixEnd_2688260 : Nat := 4983230072969 + 3 ^ 40 * 2688260 * 2
def baseEnd_2688260 : Nat := 920246336170504936057949

theorem tailTrace_2688260 : CollatzResearch.WordTrace tailWord_2688260 prefixEnd_2688260 920246336170504936057949 := by
  unfold tailWord_2688260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49024448620450306550419117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65365931493933742067225489 49024448620450306550419117)
  ·
    refine ⟨18384168232668864956407169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49024448620450306550419117 18384168232668864956407169)
    ·
      refine ⟨13788126174501648717305377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18384168232668864956407169 13788126174501648717305377)
      ·
        refine ⟨10341094630876236537979033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13788126174501648717305377 10341094630876236537979033)
        ·
          refine ⟨7755820973157177403484275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10341094630876236537979033 7755820973157177403484275)
          ·
            refine ⟨11633731459735766105226413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755820973157177403484275 11633731459735766105226413)
            ·
              refine ⟨4362649297400912289459905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11633731459735766105226413 4362649297400912289459905)
              ·
                refine ⟨3271986973050684217094929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4362649297400912289459905 3271986973050684217094929)
                ·
                  refine ⟨2453990229788013162821197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3271986973050684217094929 2453990229788013162821197)
                  ·
                    refine ⟨920246336170504936057949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2453990229788013162821197 920246336170504936057949)
                    ·
                      rfl

theorem cell22_2688260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_2688260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688260 prefixEnd_2688260 := by exact prefixLift 2688260
  have htrace : WordTrace (prefixWord ++ tailWord_2688260) baseStart_2688260 baseEnd_2688260 := by
    simpa [prefixWord, tailWord_2688260, baseEnd_2688260] using wordTrace_append hprefix tailTrace_2688260
  have hstable : (prefixWord ++ tailWord_2688260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688260).length < 2 ^ (prefixWord ++ tailWord_2688260).sum := by decide
  have hdescent : baseEnd_2688260 < baseStart_2688260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688290 : List Nat := [3, 3, 1, 1, 4, 2, 2, 6]
def baseStart_2688290 : Nat := 118140960795 + 2688290 * 2 ^ 59
def prefixEnd_2688290 : Nat := 4983230072969 + 3 ^ 40 * 2688290 * 2
def baseEnd_2688290 : Nat := 102250733975954984200873

theorem tailTrace_2688290 : CollatzResearch.WordTrace tailWord_2688290 prefixEnd_2688290 102250733975954984200873 := by
  unfold tailWord_2688290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24512497857697982056107581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65366660953861285482953549 24512497857697982056107581)
  ·
    refine ⟨9192186696636743271040343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24512497857697982056107581 9192186696636743271040343)
    ·
      refine ⟨13788280044955114906560515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192186696636743271040343 13788280044955114906560515)
      ·
        refine ⟨20682420067432672359840773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13788280044955114906560515 20682420067432672359840773)
        ·
          refine ⟨3877953762643626067470145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20682420067432672359840773 3877953762643626067470145)
          ·
            refine ⟨2908465321982719550602609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3877953762643626067470145 2908465321982719550602609)
            ·
              refine ⟨2181348991487039662951957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908465321982719550602609 2181348991487039662951957)
              ·
                refine ⟨102250733975954984200873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2181348991487039662951957 102250733975954984200873)
                ·
                  rfl

theorem cell22_2688290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_2688290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688290 prefixEnd_2688290 := by exact prefixLift 2688290
  have htrace : WordTrace (prefixWord ++ tailWord_2688290) baseStart_2688290 baseEnd_2688290 := by
    simpa [prefixWord, tailWord_2688290, baseEnd_2688290] using wordTrace_append hprefix tailTrace_2688290
  have hstable : (prefixWord ++ tailWord_2688290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688290).length < 2 ^ (prefixWord ++ tailWord_2688290).sum := by decide
  have hdescent : baseEnd_2688290 < baseStart_2688290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688318 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_2688318 : Nat := 118140960795 + 2688318 * 2 ^ 59
def prefixEnd_2688318 : Nat := 4983230072969 + 3 ^ 40 * 2688318 * 2
def baseEnd_2688318 : Nat := 306755396918604039369257

theorem tailTrace_2688318 : CollatzResearch.WordTrace tailWord_2688318 prefixEnd_2688318 306755396918604039369257 := by
  unfold tailWord_2688318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256376584336311125806201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65367341783126992670966405 12256376584336311125806201)
  ·
    refine ⟨9192282438252233344354651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12256376584336311125806201 9192282438252233344354651)
    ·
      refine ⟨13788423657378350016531977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192282438252233344354651 13788423657378350016531977)
      ·
        refine ⟨10341317743033762512398983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13788423657378350016531977 10341317743033762512398983)
        ·
          refine ⟨15511976614550643768598475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10341317743033762512398983 15511976614550643768598475)
          ·
            refine ⟨23267964921825965652897713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511976614550643768598475 23267964921825965652897713)
            ·
              refine ⟨17450973691369474239673285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23267964921825965652897713 17450973691369474239673285)
              ·
                refine ⟨3272057567131776419938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17450973691369474239673285 3272057567131776419938741)
                ·
                  refine ⟨306755396918604039369257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3272057567131776419938741 306755396918604039369257)
                  ·
                    rfl

theorem cell22_2688318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_2688318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688318 prefixEnd_2688318 := by exact prefixLift 2688318
  have htrace : WordTrace (prefixWord ++ tailWord_2688318) baseStart_2688318 baseEnd_2688318 := by
    simpa [prefixWord, tailWord_2688318, baseEnd_2688318] using wordTrace_append hprefix tailTrace_2688318
  have hstable : (prefixWord ++ tailWord_2688318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688318).length < 2 ^ (prefixWord ++ tailWord_2688318).sum := by decide
  have hdescent : baseEnd_2688318 < baseStart_2688318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688346 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_2688346 : Nat := 118140960795 + 2688346 * 2 ^ 59
def prefixEnd_2688346 : Nat := 4983230072969 + 3 ^ 40 * 2688346 * 2
def baseEnd_2688346 : Nat := 306758591909343126135895

theorem tailTrace_2688346 : CollatzResearch.WordTrace tailWord_2688346 prefixEnd_2688346 306758591909343126135895 := by
  unfold tailWord_2688346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24513008479647262447117223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65368022612392699858979261 24513008479647262447117223)
  ·
    refine ⟨36769512719470893670675835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24513008479647262447117223 36769512719470893670675835)
    ·
      refine ⟨55154269079206340506013753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36769512719470893670675835 55154269079206340506013753)
      ·
        refine ⟨41365701809404755379510315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55154269079206340506013753 41365701809404755379510315)
        ·
          refine ⟨62048552714107133069265473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41365701809404755379510315 62048552714107133069265473)
          ·
            refine ⟨46536414535580349801949105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62048552714107133069265473 46536414535580349801949105)
            ·
              refine ⟨34902310901685262351461829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46536414535580349801949105 34902310901685262351461829)
              ·
                refine ⟨6544183294065986690899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34902310901685262351461829 6544183294065986690899093)
                ·
                  refine ⟨306758591909343126135895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6544183294065986690899093 306758591909343126135895)
                  ·
                    rfl

theorem cell22_2688346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_2688346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688346 prefixEnd_2688346 := by exact prefixLift 2688346
  have htrace : WordTrace (prefixWord ++ tailWord_2688346) baseStart_2688346 baseEnd_2688346 := by
    simpa [prefixWord, tailWord_2688346, baseEnd_2688346] using wordTrace_append hprefix tailTrace_2688346
  have hstable : (prefixWord ++ tailWord_2688346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688346).length < 2 ^ (prefixWord ++ tailWord_2688346).sum := by decide
  have hdescent : baseEnd_2688346 < baseStart_2688346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688414 : List Nat := [4, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2688414 : Nat := 118140960795 + 2688414 * 2 ^ 59
def prefixEnd_2688414 : Nat := 4983230072969 + 3 ^ 40 * 2688414 * 2
def baseEnd_2688414 : Nat := 306766351172566622569159

theorem tailTrace_2688414 : CollatzResearch.WordTrace tailWord_2688414 prefixEnd_2688414 306766351172566622569159 := by
  unfold tailWord_2688414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256814260292837175243037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65369676054895131601296197 12256814260292837175243037)
  ·
    refine ⟨4596305347609813940716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12256814260292837175243037 4596305347609813940716139)
    ·
      refine ⟨6894458021414720911074209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596305347609813940716139 6894458021414720911074209)
      ·
        refine ⟨5170843516061040683305657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6894458021414720911074209 5170843516061040683305657)
        ·
          refine ⟨3878132637045780512479243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5170843516061040683305657 3878132637045780512479243)
          ·
            refine ⟨5817198955568670768718865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878132637045780512479243 5817198955568670768718865)
            ·
              refine ⟨4362899216676503076539149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817198955568670768718865 4362899216676503076539149)
              ·
                refine ⟨1636087206253688653702181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4362899216676503076539149 1636087206253688653702181)
                ·
                  refine ⟨306766351172566622569159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636087206253688653702181 306766351172566622569159)
                  ·
                    rfl

theorem cell22_2688414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2688414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688414 prefixEnd_2688414 := by exact prefixLift 2688414
  have htrace : WordTrace (prefixWord ++ tailWord_2688414) baseStart_2688414 baseEnd_2688414 := by
    simpa [prefixWord, tailWord_2688414, baseEnd_2688414] using wordTrace_append hprefix tailTrace_2688414
  have hstable : (prefixWord ++ tailWord_2688414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688414).length < 2 ^ (prefixWord ++ tailWord_2688414).sum := by decide
  have hdescent : baseEnd_2688414 < baseStart_2688414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688421 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2688421 : Nat := 118140960795 + 2688421 * 2 ^ 59
def prefixEnd_2688421 : Nat := 4983230072969 + 3 ^ 40 * 2688421 * 2
def baseEnd_2688421 : Nat := 920301449760754182782455

theorem tailTrace_2688421 : CollatzResearch.WordTrace tailWord_2688421 prefixEnd_2688421 920301449760754182782455 := by
  unfold tailWord_2688421
  simp only [CollatzResearch.WordTrace]
  refine ⟨98054769393317337597449117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65369846262211558398299411 98054769393317337597449117)
  ·
    refine ⟨36770538522494001599043419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98054769393317337597449117 36770538522494001599043419)
    ·
      refine ⟨55155807783741002398565129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36770538522494001599043419 55155807783741002398565129)
      ·
        refine ⟨41366855837805751798923847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55155807783741002398565129 41366855837805751798923847)
        ·
          refine ⟨62050283756708627698385771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41366855837805751798923847 62050283756708627698385771)
          ·
            refine ⟨93075425635062941547578657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62050283756708627698385771 93075425635062941547578657)
            ·
              refine ⟨69806569226297206160683993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93075425635062941547578657 69806569226297206160683993)
              ·
                refine ⟨52354926919722904620512995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69806569226297206160683993 52354926919722904620512995)
                ·
                  refine ⟨78532390379584356930769493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52354926919722904620512995 78532390379584356930769493)
                  ·
                    refine ⟨920301449760754182782455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78532390379584356930769493 920301449760754182782455)
                    ·
                      rfl

theorem cell22_2688421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2688421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688421 prefixEnd_2688421 := by exact prefixLift 2688421
  have htrace : WordTrace (prefixWord ++ tailWord_2688421) baseStart_2688421 baseEnd_2688421 := by
    simpa [prefixWord, tailWord_2688421, baseEnd_2688421] using wordTrace_append hprefix tailTrace_2688421
  have hstable : (prefixWord ++ tailWord_2688421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688421).length < 2 ^ (prefixWord ++ tailWord_2688421).sum := by decide
  have hdescent : baseEnd_2688421 < baseStart_2688421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688429 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2688429 : Nat := 118140960795 + 2688429 * 2 ^ 59
def prefixEnd_2688429 : Nat := 4983230072969 + 3 ^ 40 * 2688429 * 2
def baseEnd_2688429 : Nat := 920304188324244828582431

theorem tailTrace_2688429 : CollatzResearch.WordTrace tailWord_2688429 prefixEnd_2688429 920304188324244828582431 := by
  unfold tailWord_2688429
  simp only [CollatzResearch.WordTrace]
  refine ⟨98055061177288354963740341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65370040784858903309160227 98055061177288354963740341)
  ·
    refine ⟨9192661985370783277850657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98055061177288354963740341 9192661985370783277850657)
    ·
      refine ⟨6894496489028087458387993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9192661985370783277850657 6894496489028087458387993)
      ·
        refine ⟨5170872366771065593790995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6894496489028087458387993 5170872366771065593790995)
        ·
          refine ⟨7756308550156598390686493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170872366771065593790995 7756308550156598390686493)
          ·
            refine ⟨2908615706308724396507435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7756308550156598390686493 2908615706308724396507435)
            ·
              refine ⟨4362923559463086594761153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908615706308724396507435 4362923559463086594761153)
              ·
                refine ⟨3272192669597314946070865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4362923559463086594761153 3272192669597314946070865)
                ·
                  refine ⟨2454144502197986209553149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3272192669597314946070865 2454144502197986209553149)
                  ·
                    refine ⟨920304188324244828582431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454144502197986209553149 920304188324244828582431)
                    ·
                      rfl

theorem cell22_2688429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2688429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688429 prefixEnd_2688429 := by exact prefixLift 2688429
  have htrace : WordTrace (prefixWord ++ tailWord_2688429) baseStart_2688429 baseEnd_2688429 := by
    simpa [prefixWord, tailWord_2688429, baseEnd_2688429] using wordTrace_append hprefix tailTrace_2688429
  have hstable : (prefixWord ++ tailWord_2688429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688429).length < 2 ^ (prefixWord ++ tailWord_2688429).sum := by decide
  have hdescent : baseEnd_2688429 < baseStart_2688429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688470 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2688470 : Nat := 118140960795 + 2688470 * 2 ^ 59
def prefixEnd_2688470 : Nat := 4983230072969 + 3 ^ 40 * 2688470 * 2
def baseEnd_2688470 : Nat := 306772741154044796102435

theorem tailTrace_2688470 : CollatzResearch.WordTrace tailWord_2688470 prefixEnd_2688470 306772741154044796102435 := by
  unfold tailWord_2688470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128534785633738685373929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65371037713426545977321909 6128534785633738685373929)
  ·
    refine ⟨4596401089225304014030447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6128534785633738685373929 4596401089225304014030447)
    ·
      refine ⟨6894601633837956021045671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596401089225304014030447 6894601633837956021045671)
      ·
        refine ⟨10341902450756934031568507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894601633837956021045671 10341902450756934031568507)
        ·
          refine ⟨15512853676135401047352761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10341902450756934031568507 15512853676135401047352761)
          ·
            refine ⟨11634640257101550785514571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15512853676135401047352761 11634640257101550785514571)
            ·
              refine ⟨17451960385652326178271857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11634640257101550785514571 17451960385652326178271857)
              ·
                refine ⟨13088970289239244633703893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17451960385652326178271857 13088970289239244633703893)
                ·
                  refine ⟨306772741154044796102435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13088970289239244633703893 306772741154044796102435)
                  ·
                    rfl

theorem cell22_2688470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2688470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688470 prefixEnd_2688470 := by exact prefixLift 2688470
  have htrace : WordTrace (prefixWord ++ tailWord_2688470) baseStart_2688470 baseEnd_2688470 := by
    simpa [prefixWord, tailWord_2688470, baseEnd_2688470] using wordTrace_append hprefix tailTrace_2688470
  have hstable : (prefixWord ++ tailWord_2688470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688470).length < 2 ^ (prefixWord ++ tailWord_2688470).sum := by decide
  have hdescent : baseEnd_2688470 < baseStart_2688470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688474 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_2688474 : Nat := 118140960795 + 2688474 * 2 ^ 59
def prefixEnd_2688474 : Nat := 4983230072969 + 3 ^ 40 * 2688474 * 2
def baseEnd_2688474 : Nat := 920319592743879711207293

theorem tailTrace_2688474 : CollatzResearch.WordTrace tailWord_2688474 prefixEnd_2688474 920319592743879711207293 := by
  unfold tailWord_2688474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24514175615531331912282119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65371134974750218432752317 24514175615531331912282119)
  ·
    refine ⟨36771263423296997868423179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24514175615531331912282119 36771263423296997868423179)
    ·
      refine ⟨55156895134945496802634769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36771263423296997868423179 55156895134945496802634769)
      ·
        refine ⟨41367671351209122601976077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55156895134945496802634769 41367671351209122601976077)
        ·
          refine ⟨15512876756703420975741029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41367671351209122601976077 15512876756703420975741029)
          ·
            refine ⟨2908664391881891432951443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15512876756703420975741029 2908664391881891432951443)
            ·
              refine ⟨4362996587822837149427165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908664391881891432951443 4362996587822837149427165)
              ·
                refine ⟨1636123720433563931035187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4362996587822837149427165 1636123720433563931035187)
                ·
                  refine ⟨2454185580650345896552781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636123720433563931035187 2454185580650345896552781)
                  ·
                    refine ⟨920319592743879711207293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454185580650345896552781 920319592743879711207293)
                    ·
                      rfl

theorem cell22_2688474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_2688474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688474 prefixEnd_2688474 := by exact prefixLift 2688474
  have htrace : WordTrace (prefixWord ++ tailWord_2688474) baseStart_2688474 baseEnd_2688474 := by
    simpa [prefixWord, tailWord_2688474, baseEnd_2688474] using wordTrace_append hprefix tailTrace_2688474
  have hstable : (prefixWord ++ tailWord_2688474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688474).length < 2 ^ (prefixWord ++ tailWord_2688474).sum := by decide
  have hdescent : baseEnd_2688474 < baseStart_2688474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688542 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2688542 : Nat := 118140960795 + 2688542 * 2 ^ 59
def prefixEnd_2688542 : Nat := 4983230072969 + 3 ^ 40 * 2688542 * 2
def baseEnd_2688542 : Nat := 920342870533550200507085

theorem tailTrace_2688542 : CollatzResearch.WordTrace tailWord_2688542 prefixEnd_2688542 920342870533550200507085 := by
  unfold tailWord_2688542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257397828234871907825485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65372788417252650175069253 12257397828234871907825485)
  ·
    refine ⟨4596524185588076965434557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12257397828234871907825485 4596524185588076965434557)
    ·
      refine ⟨1723696569595528862037959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4596524185588076965434557 1723696569595528862037959)
      ·
        refine ⟨2585544854393293293056939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723696569595528862037959 2585544854393293293056939)
        ·
          refine ⟨3878317281589939939585409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585544854393293293056939 3878317281589939939585409)
          ·
            refine ⟨2908737961192454954689057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3878317281589939939585409 2908737961192454954689057)
            ·
              refine ⟨2181553470894341216016793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908737961192454954689057 2181553470894341216016793)
              ·
                refine ⟨1636165103170755912012595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2181553470894341216016793 1636165103170755912012595)
                ·
                  refine ⟨2454247654756133868018893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636165103170755912012595 2454247654756133868018893)
                  ·
                    refine ⟨920342870533550200507085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454247654756133868018893 920342870533550200507085)
                    ·
                      rfl

theorem cell22_2688542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2688542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688542 prefixEnd_2688542 := by exact prefixLift 2688542
  have htrace : WordTrace (prefixWord ++ tailWord_2688542) baseStart_2688542 baseEnd_2688542 := by
    simpa [prefixWord, tailWord_2688542, baseEnd_2688542] using wordTrace_append hprefix tailTrace_2688542
  have hstable : (prefixWord ++ tailWord_2688542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688542).length < 2 ^ (prefixWord ++ tailWord_2688542).sum := by decide
  have hdescent : baseEnd_2688542 < baseStart_2688542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688545 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2688545 : Nat := 118140960795 + 2688545 * 2 ^ 59
def prefixEnd_2688545 : Nat := 4983230072969 + 3 ^ 40 * 2688545 * 2
def baseEnd_2688545 : Nat := 920343897494859192682075

theorem tailTrace_2688545 : CollatzResearch.WordTrace tailWord_2688545 prefixEnd_2688545 920343897494859192682075 := by
  unfold tailWord_2688545
  simp only [CollatzResearch.WordTrace]
  refine ⟨98059292044868106774963089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65372861363245404516642059 98059292044868106774963089)
  ·
    refine ⟨73544469033651080081222317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98059292044868106774963089 73544469033651080081222317)
    ·
      refine ⟨27579175887619155030458369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73544469033651080081222317 27579175887619155030458369)
      ·
        refine ⟨20684381915714366272843777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27579175887619155030458369 20684381915714366272843777)
        ·
          refine ⟨15513286436785774704632833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20684381915714366272843777 15513286436785774704632833)
          ·
            refine ⟨11634964827589331028474625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513286436785774704632833 11634964827589331028474625)
            ·
              refine ⟨8726223620691998271355969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11634964827589331028474625 8726223620691998271355969)
              ·
                refine ⟨6544667715518998703516977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8726223620691998271355969 6544667715518998703516977)
                ·
                  refine ⟨4908500786639249027637733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544667715518998703516977 4908500786639249027637733)
                  ·
                    refine ⟨920343897494859192682075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4908500786639249027637733 920343897494859192682075)
                    ·
                      rfl

theorem cell22_2688545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2688545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688545 prefixEnd_2688545 := by exact prefixLift 2688545
  have htrace : WordTrace (prefixWord ++ tailWord_2688545) baseStart_2688545 baseEnd_2688545 := by
    simpa [prefixWord, tailWord_2688545, baseEnd_2688545] using wordTrace_append hprefix tailTrace_2688545
  have hstable : (prefixWord ++ tailWord_2688545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688545).length < 2 ^ (prefixWord ++ tailWord_2688545).sum := by decide
  have hdescent : baseEnd_2688545 < baseStart_2688545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688575 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 5, 3]
def baseStart_2688575 : Nat := 118140960795 + 2688575 * 2 ^ 59
def prefixEnd_2688575 : Nat := 4983230072969 + 3 ^ 40 * 2688575 * 2
def baseEnd_2688575 : Nat := 920354167107949114431983

theorem tailTrace_2688575 : CollatzResearch.WordTrace tailWord_2688575 prefixEnd_2688575 920354167107949114431983 := by
  unfold tailWord_2688575
  simp only [CollatzResearch.WordTrace]
  refine ⟨98060386234759421898555179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65373590823172947932370119 98060386234759421898555179)
  ·
    refine ⟨147090579352139132847832769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98060386234759421898555179 147090579352139132847832769)
    ·
      refine ⟨110317934514104349635874577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147090579352139132847832769 110317934514104349635874577)
      ·
        refine ⟨82738450885578262226905933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110317934514104349635874577 82738450885578262226905933)
        ·
          refine ⟨31026919082091848335089725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82738450885578262226905933 31026919082091848335089725)
          ·
            refine ⟨11635094655784443125658647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31026919082091848335089725 11635094655784443125658647)
            ·
              refine ⟨17452641983676664688487971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635094655784443125658647 17452641983676664688487971)
              ·
                refine ⟨26178962975514997032731957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17452641983676664688487971 26178962975514997032731957)
                ·
                  refine ⟨2454277778954530971818621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26178962975514997032731957 2454277778954530971818621)
                  ·
                    refine ⟨920354167107949114431983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454277778954530971818621 920354167107949114431983)
                    ·
                      rfl

theorem cell22_2688575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_2688575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688575 prefixEnd_2688575 := by exact prefixLift 2688575
  have htrace : WordTrace (prefixWord ++ tailWord_2688575) baseStart_2688575 baseEnd_2688575 := by
    simpa [prefixWord, tailWord_2688575, baseEnd_2688575] using wordTrace_append hprefix tailTrace_2688575
  have hstable : (prefixWord ++ tailWord_2688575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688575).length < 2 ^ (prefixWord ++ tailWord_2688575).sum := by decide
  have hdescent : baseEnd_2688575 < baseStart_2688575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688695 : List Nat := [1, 1, 3, 1, 5, 1, 2, 8]
def baseStart_2688695 : Nat := 118140960795 + 2688695 * 2 ^ 59
def prefixEnd_2688695 : Nat := 4983230072969 + 3 ^ 40 * 2688695 * 2
def baseEnd_2688695 : Nat := 102266138395589866825735

theorem tailTrace_2688695 : CollatzResearch.WordTrace tailWord_2688695 prefixEnd_2688695 102266138395589866825735 := by
  unfold tailWord_2688695
  simp only [CollatzResearch.WordTrace]
  refine ⟨98064762994324682392923539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65376508662883121595282359 98064762994324682392923539)
  ·
    refine ⟨147097144491487023589385309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98064762994324682392923539 147097144491487023589385309)
    ·
      refine ⟨55161429184307633846019491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147097144491487023589385309 55161429184307633846019491)
      ·
        refine ⟨82742143776461450769029237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55161429184307633846019491 82742143776461450769029237)
        ·
          refine ⟨7757075979043261009596491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82742143776461450769029237 7757075979043261009596491)
          ·
            refine ⟨11635613968564891514394737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757075979043261009596491 11635613968564891514394737)
            ·
              refine ⟨8726710476423668635796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635613968564891514394737 8726710476423668635796053)
              ·
                refine ⟨102266138395589866825735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8726710476423668635796053 102266138395589866825735)
                ·
                  rfl

theorem cell22_2688695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 8].length) (baseStart_2688695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688695 prefixEnd_2688695 := by exact prefixLift 2688695
  have htrace : WordTrace (prefixWord ++ tailWord_2688695) baseStart_2688695 baseEnd_2688695 := by
    simpa [prefixWord, tailWord_2688695, baseEnd_2688695] using wordTrace_append hprefix tailTrace_2688695
  have hstable : (prefixWord ++ tailWord_2688695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688695).length < 2 ^ (prefixWord ++ tailWord_2688695).sum := by decide
  have hdescent : baseEnd_2688695 < baseStart_2688695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688716 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_2688716 : Nat := 118140960795 + 2688716 * 2 ^ 59
def prefixEnd_2688716 : Nat := 4983230072969 + 3 ^ 40 * 2688716 * 2
def baseEnd_2688716 : Nat := 920402434289471746656551

theorem tailTrace_2688716 : CollatzResearch.WordTrace tailWord_2688716 prefixEnd_2688716 920402434289471746656551 := by
  unfold tailWord_2688716
  simp only [CollatzResearch.WordTrace]
  refine ⟨49032764463624301489719001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65377019284832401986292001 49032764463624301489719001)
  ·
    refine ⟨36774573347718226117289251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49032764463624301489719001 36774573347718226117289251)
    ·
      refine ⟨55161860021577339175933877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36774573347718226117289251 55161860021577339175933877)
      ·
        refine ⟨5171424377022875547743801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55161860021577339175933877 5171424377022875547743801)
        ·
          refine ⟨3878568282767156660807851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171424377022875547743801 3878568282767156660807851)
          ·
            refine ⟨5817852424150734991211777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878568282767156660807851 5817852424150734991211777)
            ·
              refine ⟨4363389318113051243408833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5817852424150734991211777 4363389318113051243408833)
              ·
                refine ⟨3272541988584788432556625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363389318113051243408833 3272541988584788432556625)
                ·
                  refine ⟨2454406491438591324417469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3272541988584788432556625 2454406491438591324417469)
                  ·
                    refine ⟨920402434289471746656551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454406491438591324417469 920402434289471746656551)
                    ·
                      rfl

theorem cell22_2688716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_2688716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688716 prefixEnd_2688716 := by exact prefixLift 2688716
  have htrace : WordTrace (prefixWord ++ tailWord_2688716) baseStart_2688716 baseEnd_2688716 := by
    simpa [prefixWord, tailWord_2688716, baseEnd_2688716] using wordTrace_append hprefix tailTrace_2688716
  have hstable : (prefixWord ++ tailWord_2688716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688716).length < 2 ^ (prefixWord ++ tailWord_2688716).sum := by decide
  have hdescent : baseEnd_2688716 < baseStart_2688716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688727 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 3, 3]
def baseStart_2688727 : Nat := 118140960795 + 2688727 * 2 ^ 59
def prefixEnd_2688727 : Nat := 4983230072969 + 3 ^ 40 * 2688727 * 2
def baseEnd_2688727 : Nat := 920406199814271384631517

theorem tailTrace_2688727 : CollatzResearch.WordTrace tailWord_2688727 prefixEnd_2688727 920406199814271384631517 := by
  unfold tailWord_2688727
  simp only [CollatzResearch.WordTrace]
  refine ⟨98065930130208751858088435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65377286753472501238725623 98065930130208751858088435)
  ·
    refine ⟨147098895195313127787132653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98065930130208751858088435 147098895195313127787132653)
    ·
      refine ⟨55162085698242422920174745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147098895195313127787132653 55162085698242422920174745)
      ·
        refine ⟨41371564273681817190131059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55162085698242422920174745 41371564273681817190131059)
        ·
          refine ⟨62057346410522725785196589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41371564273681817190131059 62057346410522725785196589)
          ·
            refine ⟨23271504903946022169448721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62057346410522725785196589 23271504903946022169448721)
            ·
              refine ⟨17453628677959516627086541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23271504903946022169448721 17453628677959516627086541)
              ·
                refine ⟨6545110754234818735157453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17453628677959516627086541 6545110754234818735157453)
                ·
                  refine ⟨2454416532838057025684045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6545110754234818735157453 2454416532838057025684045)
                  ·
                    refine ⟨920406199814271384631517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454416532838057025684045 920406199814271384631517)
                    ·
                      rfl

theorem cell22_2688727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_2688727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688727 prefixEnd_2688727 := by exact prefixLift 2688727
  have htrace : WordTrace (prefixWord ++ tailWord_2688727) baseStart_2688727 baseEnd_2688727 := by
    simpa [prefixWord, tailWord_2688727, baseEnd_2688727] using wordTrace_append hprefix tailTrace_2688727
  have hstable : (prefixWord ++ tailWord_2688727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688727).length < 2 ^ (prefixWord ++ tailWord_2688727).sum := by decide
  have hdescent : baseEnd_2688727 < baseStart_2688727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688744 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_2688744 : Nat := 118140960795 + 2688744 * 2 ^ 59
def prefixEnd_2688744 : Nat := 4983230072969 + 3 ^ 40 * 2688744 * 2
def baseEnd_2688744 : Nat := 920412019261689006956465

theorem tailTrace_2688744 : CollatzResearch.WordTrace tailWord_2688744 prefixEnd_2688744 920412019261689006956465 := by
  unfold tailWord_2688744
  simp only [CollatzResearch.WordTrace]
  refine ⟨49033275085573581880728643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65377700114098109174304857 49033275085573581880728643)
  ·
    refine ⟨73549912628360372821092965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49033275085573581880728643 73549912628360372821092965)
    ·
      refine ⟨13790608617817569903954931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73549912628360372821092965 13790608617817569903954931)
      ·
        refine ⟨20685912926726354855932397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13790608617817569903954931 20685912926726354855932397)
        ·
          refine ⟨7757217347522383070974649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20685912926726354855932397 7757217347522383070974649)
          ·
            refine ⟨5817913010641787303230987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757217347522383070974649 5817913010641787303230987)
            ·
              refine ⟨8726869515962680954846481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5817913010641787303230987 8726869515962680954846481)
              ·
                refine ⟨6545152136972010716134861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8726869515962680954846481 6545152136972010716134861)
                ·
                  refine ⟨2454432051364504018550573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6545152136972010716134861 2454432051364504018550573)
                  ·
                    refine ⟨920412019261689006956465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454432051364504018550573 920412019261689006956465)
                    ·
                      rfl

theorem cell22_2688744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_2688744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688744 prefixEnd_2688744 := by exact prefixLift 2688744
  have htrace : WordTrace (prefixWord ++ tailWord_2688744) baseStart_2688744 baseEnd_2688744 := by
    simpa [prefixWord, tailWord_2688744, baseEnd_2688744] using wordTrace_append hprefix tailTrace_2688744
  have hstable : (prefixWord ++ tailWord_2688744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688744).length < 2 ^ (prefixWord ++ tailWord_2688744).sum := by decide
  have hdescent : baseEnd_2688744 < baseStart_2688744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688772 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_2688772 : Nat := 118140960795 + 2688772 * 2 ^ 59
def prefixEnd_2688772 : Nat := 4983230072969 + 3 ^ 40 * 2688772 * 2
def baseEnd_2688772 : Nat := 920421604233906267256379

theorem tailTrace_2688772 : CollatzResearch.WordTrace tailWord_2688772 prefixEnd_2688772 920421604233906267256379 := by
  unfold tailWord_2688772
  simp only [CollatzResearch.WordTrace]
  refine ⟨49033785707522862271738285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65378380943363816362317713 49033785707522862271738285)
  ·
    refine ⟨18387669640321073351901857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49033785707522862271738285 18387669640321073351901857)
    ·
      refine ⟨13790752230240805013926393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18387669640321073351901857 13790752230240805013926393)
      ·
        refine ⟨10343064172680603760444795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13790752230240805013926393 10343064172680603760444795)
        ·
          refine ⟨15514596259020905640667193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10343064172680603760444795 15514596259020905640667193)
          ·
            refine ⟨11635947194265679230500395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15514596259020905640667193 11635947194265679230500395)
            ·
              refine ⟨17453920791398518845750593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635947194265679230500395 17453920791398518845750593)
              ·
                refine ⟨13090440593548889134312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17453920791398518845750593 13090440593548889134312945)
                ·
                  refine ⟨9817830445161666850734709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13090440593548889134312945 9817830445161666850734709)
                  ·
                    refine ⟨920421604233906267256379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9817830445161666850734709 920421604233906267256379)
                    ·
                      rfl

theorem cell22_2688772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_2688772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688772 prefixEnd_2688772 := by exact prefixLift 2688772
  have htrace : WordTrace (prefixWord ++ tailWord_2688772) baseStart_2688772 baseEnd_2688772 := by
    simpa [prefixWord, tailWord_2688772, baseEnd_2688772] using wordTrace_append hprefix tailTrace_2688772
  have hstable : (prefixWord ++ tailWord_2688772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688772).length < 2 ^ (prefixWord ++ tailWord_2688772).sum := by decide
  have hdescent : baseEnd_2688772 < baseStart_2688772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688802 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2688802 : Nat := 118140960795 + 2688802 * 2 ^ 59
def prefixEnd_2688802 : Nat := 4983230072969 + 3 ^ 40 * 2688802 * 2
def baseEnd_2688802 : Nat := 306810624615665396335429

theorem tailTrace_2688802 : CollatzResearch.WordTrace tailWord_2688802 prefixEnd_2688802 306810624615665396335429 := by
  unfold tailWord_2688802
  simp only [CollatzResearch.WordTrace]
  refine ⟨24517166401234259916767165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65379110403291359778045773 24517166401234259916767165)
  ·
    refine ⟨9193937400462847468787687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24517166401234259916767165 9193937400462847468787687)
    ·
      refine ⟨13790906100694271203181531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193937400462847468787687 13790906100694271203181531)
      ·
        refine ⟨20686359151041406804772297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13790906100694271203181531 20686359151041406804772297)
        ·
          refine ⟨15514769363281055103579223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20686359151041406804772297 15514769363281055103579223)
          ·
            refine ⟨23272154044921582655368835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15514769363281055103579223 23272154044921582655368835)
            ·
              refine ⟨34908231067382373983053253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23272154044921582655368835 34908231067382373983053253)
              ·
                refine ⟨6545293325134195121822485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34908231067382373983053253 6545293325134195121822485)
                ·
                  refine ⟨306810624615665396335429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6545293325134195121822485 306810624615665396335429)
                  ·
                    rfl

theorem cell22_2688802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2688802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688802 prefixEnd_2688802 := by exact prefixLift 2688802
  have htrace : WordTrace (prefixWord ++ tailWord_2688802) baseStart_2688802 baseEnd_2688802 := by
    simpa [prefixWord, tailWord_2688802, baseEnd_2688802] using wordTrace_append hprefix tailTrace_2688802
  have hstable : (prefixWord ++ tailWord_2688802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688802).length < 2 ^ (prefixWord ++ tailWord_2688802).sum := by decide
  have hdescent : baseEnd_2688802 < baseStart_2688802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688804 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_2688804 : Nat := 118140960795 + 2688804 * 2 ^ 59
def prefixEnd_2688804 : Nat := 4983230072969 + 3 ^ 40 * 2688804 * 2
def baseEnd_2688804 : Nat := 920432558487868850456281

theorem tailTrace_2688804 : CollatzResearch.WordTrace tailWord_2688804 prefixEnd_2688804 920432558487868850456281 := by
  unfold tailWord_2688804
  simp only [CollatzResearch.WordTrace]
  refine ⟨49034369275464897004320733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65379159033953196005760977 49034369275464897004320733)
  ·
    refine ⟨18387888478299336376620275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49034369275464897004320733 18387888478299336376620275)
    ·
      refine ⟨27581832717449004564930413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18387888478299336376620275 27581832717449004564930413)
      ·
        refine ⟨10343187269043376711848905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27581832717449004564930413 10343187269043376711848905)
        ·
          refine ⟨7757390451782532533886679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343187269043376711848905 7757390451782532533886679)
          ·
            refine ⟨11636085677673798800830019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757390451782532533886679 11636085677673798800830019)
            ·
              refine ⟨17454128516510698201245029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11636085677673798800830019 17454128516510698201245029)
              ·
                refine ⟨3272649096845755912733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17454128516510698201245029 3272649096845755912733443)
                ·
                  refine ⟨4908973645268633869100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272649096845755912733443 4908973645268633869100165)
                  ·
                    refine ⟨920432558487868850456281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4908973645268633869100165 920432558487868850456281)
                    ·
                      rfl

theorem cell22_2688804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_2688804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688804 prefixEnd_2688804 := by exact prefixLift 2688804
  have htrace : WordTrace (prefixWord ++ tailWord_2688804) baseStart_2688804 baseEnd_2688804 := by
    simpa [prefixWord, tailWord_2688804, baseEnd_2688804] using wordTrace_append hprefix tailTrace_2688804
  have hstable : (prefixWord ++ tailWord_2688804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688804).length < 2 ^ (prefixWord ++ tailWord_2688804).sum := by decide
  have hdescent : baseEnd_2688804 < baseStart_2688804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688866 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2688866 : Nat := 118140960795 + 2688866 * 2 ^ 59
def prefixEnd_2688866 : Nat := 4983230072969 + 3 ^ 40 * 2688866 * 2
def baseEnd_2688866 : Nat := 920453782354921355406091

theorem tailTrace_2688866 : CollatzResearch.WordTrace tailWord_2688866 prefixEnd_2688866 920453782354921355406091 := by
  unfold tailWord_2688866
  simp only [CollatzResearch.WordTrace]
  refine ⟨24517749969176294649349613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65380666584470119064932301 24517749969176294649349613)
  ·
    refine ⟨9194156238441110493506105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24517749969176294649349613 9194156238441110493506105)
    ·
      refine ⟨6895617178830832870129579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9194156238441110493506105 6895617178830832870129579)
      ·
        refine ⟨10343425768246249305194369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6895617178830832870129579 10343425768246249305194369)
        ·
          refine ⟨7757569326184686978895777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343425768246249305194369 7757569326184686978895777)
          ·
            refine ⟨5818176994638515234171833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7757569326184686978895777 5818176994638515234171833)
            ·
              refine ⟨4363632745978886425628875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818176994638515234171833 4363632745978886425628875)
              ·
                refine ⟨6545449118968329638443313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363632745978886425628875 6545449118968329638443313)
                ·
                  refine ⟨4909086839226247228832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545449118968329638443313 4909086839226247228832485)
                  ·
                    refine ⟨920453782354921355406091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909086839226247228832485 920453782354921355406091)
                    ·
                      rfl

theorem cell22_2688866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2688866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688866 prefixEnd_2688866 := by exact prefixLift 2688866
  have htrace : WordTrace (prefixWord ++ tailWord_2688866) baseStart_2688866 baseEnd_2688866 := by
    simpa [prefixWord, tailWord_2688866, baseEnd_2688866] using wordTrace_append hprefix tailTrace_2688866
  have hstable : (prefixWord ++ tailWord_2688866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688866).length < 2 ^ (prefixWord ++ tailWord_2688866).sum := by decide
  have hdescent : baseEnd_2688866 < baseStart_2688866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688896 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_2688896 : Nat := 118140960795 + 2688896 * 2 ^ 59
def prefixEnd_2688896 : Nat := 4983230072969 + 3 ^ 40 * 2688896 * 2
def baseEnd_2688896 : Nat := 920464051968011277155999

theorem tailTrace_2688896 : CollatzResearch.WordTrace tailWord_2688896 prefixEnd_2688896 920464051968011277155999 := by
  unfold tailWord_2688896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49036047033298246860495271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65381396044397662480660361 49036047033298246860495271)
  ·
    refine ⟨73554070549947370290742907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49036047033298246860495271 73554070549947370290742907)
    ·
      refine ⟨110331105824921055436114361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73554070549947370290742907 110331105824921055436114361)
      ·
        refine ⟨82748329368690791577085771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110331105824921055436114361 82748329368690791577085771)
        ·
          refine ⟨124122494053036187365628657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82748329368690791577085771 124122494053036187365628657)
          ·
            refine ⟨93091870539777140524221493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124122494053036187365628657 93091870539777140524221493)
            ·
              refine ⟨8727362863104106924145765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93091870539777140524221493 8727362863104106924145765)
              ·
                refine ⟨1636380536832020048277331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8727362863104106924145765 1636380536832020048277331)
                ·
                  refine ⟨2454570805248030072415997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636380536832020048277331 2454570805248030072415997)
                  ·
                    refine ⟨920464051968011277155999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454570805248030072415997 920464051968011277155999)
                    ·
                      rfl

theorem cell22_2688896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_2688896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688896 prefixEnd_2688896 := by exact prefixLift 2688896
  have htrace : WordTrace (prefixWord ++ tailWord_2688896) baseStart_2688896 baseEnd_2688896 := by
    simpa [prefixWord, tailWord_2688896, baseEnd_2688896] using wordTrace_append hprefix tailTrace_2688896
  have hstable : (prefixWord ++ tailWord_2688896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688896).length < 2 ^ (prefixWord ++ tailWord_2688896).sum := by decide
  have hdescent : baseEnd_2688896 < baseStart_2688896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688930 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2688930 : Nat := 118140960795 + 2688930 * 2 ^ 59
def prefixEnd_2688930 : Nat := 4983230072969 + 3 ^ 40 * 2688930 * 2
def baseEnd_2688930 : Nat := 920475690862846521805895

theorem tailTrace_2688930 : CollatzResearch.WordTrace tailWord_2688930 prefixEnd_2688930 920475690862846521805895 := by
  unfold tailWord_2688930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24518333537118329381932061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65382222765648878351818829 24518333537118329381932061)
  ·
    refine ⟨9194375076419373518224523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24518333537118329381932061 9194375076419373518224523)
    ·
      refine ⟨13791562614629060277336785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194375076419373518224523 13791562614629060277336785)
      ·
        refine ⟨10343671960971795208002589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13791562614629060277336785 10343671960971795208002589)
        ·
          refine ⟨3878876985364423203000971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10343671960971795208002589 3878876985364423203000971)
          ·
            refine ⟨5818315478046634804501457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878876985364423203000971 5818315478046634804501457)
            ·
              refine ⟨4363736608534976103376093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818315478046634804501457 4363736608534976103376093)
              ·
                refine ⟨1636401228200616038766035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4363736608534976103376093 1636401228200616038766035)
                ·
                  refine ⟨2454601842300924058149053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636401228200616038766035 2454601842300924058149053)
                  ·
                    refine ⟨920475690862846521805895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454601842300924058149053 920475690862846521805895)
                    ·
                      rfl

theorem cell22_2688930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2688930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688930 prefixEnd_2688930 := by exact prefixLift 2688930
  have htrace : WordTrace (prefixWord ++ tailWord_2688930) baseStart_2688930 baseEnd_2688930 := by
    simpa [prefixWord, tailWord_2688930, baseEnd_2688930] using wordTrace_append hprefix tailTrace_2688930
  have hstable : (prefixWord ++ tailWord_2688930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688930).length < 2 ^ (prefixWord ++ tailWord_2688930).sum := by decide
  have hdescent : baseEnd_2688930 < baseStart_2688930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2688984 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_2688984 : Nat := 118140960795 + 2688984 * 2 ^ 59
def prefixEnd_2688984 : Nat := 4983230072969 + 3 ^ 40 * 2688984 * 2
def baseEnd_2688984 : Nat := 920494176166408380955729

theorem tailTrace_2688984 : CollatzResearch.WordTrace tailWord_2688984 prefixEnd_2688984 920494176166408380955729 := by
  unfold tailWord_2688984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49037651845138842375097003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65383535793518456500129337 49037651845138842375097003)
  ·
    refine ⟨73556477767708263562645505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49037651845138842375097003 73556477767708263562645505)
    ·
      refine ⟨55167358325781197671984129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73556477767708263562645505 55167358325781197671984129)
      ·
        refine ⟨41375518744335898253988097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55167358325781197671984129 41375518744335898253988097)
        ·
          refine ⟨31031639058251923690491073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41375518744335898253988097 31031639058251923690491073)
          ·
            refine ⟨23273729293688942767868305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31031639058251923690491073 23273729293688942767868305)
            ·
              refine ⟨17455296970266707075901229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23273729293688942767868305 17455296970266707075901229)
              ·
                refine ⟨6545736363850015153462961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17455296970266707075901229 6545736363850015153462961)
                ·
                  refine ⟨4909302272887511365097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545736363850015153462961 4909302272887511365097221)
                  ·
                    refine ⟨920494176166408380955729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909302272887511365097221 920494176166408380955729)
                    ·
                      rfl

theorem cell22_2688984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_2688984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2688984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2688984 prefixEnd_2688984 := by exact prefixLift 2688984
  have htrace : WordTrace (prefixWord ++ tailWord_2688984) baseStart_2688984 baseEnd_2688984 := by
    simpa [prefixWord, tailWord_2688984, baseEnd_2688984] using wordTrace_append hprefix tailTrace_2688984
  have hstable : (prefixWord ++ tailWord_2688984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2688984).length < 2 ^ (prefixWord ++ tailWord_2688984).sum := by decide
  have hdescent : baseEnd_2688984 < baseStart_2688984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2688984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689005 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2689005 : Nat := 118140960795 + 2689005 * 2 ^ 59
def prefixEnd_2689005 : Nat := 4983230072969 + 3 ^ 40 * 2689005 * 2
def baseEnd_2689005 : Nat := 306833788298523775393555

theorem tailTrace_2689005 : CollatzResearch.WordTrace tailWord_2689005 prefixEnd_2689005 306833788298523775393555 := by
  unfold tailWord_2689005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98076069623201605336708469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65384046415467736891138979 98076069623201605336708469)
  ·
    refine ⟨9194631527175150500316419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98076069623201605336708469 9194631527175150500316419)
    ·
      refine ⟨13791947290762725750474629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194631527175150500316419 13791947290762725750474629)
      ·
        refine ⟨2585990117018011078213993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13791947290762725750474629 2585990117018011078213993)
        ·
          refine ⟨1939492587763508308660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2585990117018011078213993 1939492587763508308660495)
          ·
            refine ⟨2909238881645262462990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939492587763508308660495 2909238881645262462990743)
            ·
              refine ⟨4363858322467893694486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909238881645262462990743 4363858322467893694486115)
              ·
                refine ⟨6545787483701840541729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363858322467893694486115 6545787483701840541729173)
                ·
                  refine ⟨306833788298523775393555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6545787483701840541729173 306833788298523775393555)
                  ·
                    rfl

theorem cell22_2689005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2689005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689005 prefixEnd_2689005 := by exact prefixLift 2689005
  have htrace : WordTrace (prefixWord ++ tailWord_2689005) baseStart_2689005 baseEnd_2689005 := by
    simpa [prefixWord, tailWord_2689005, baseEnd_2689005] using wordTrace_append hprefix tailTrace_2689005
  have hstable : (prefixWord ++ tailWord_2689005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689005).length < 2 ^ (prefixWord ++ tailWord_2689005).sum := by decide
  have hdescent : baseEnd_2689005 < baseStart_2689005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689048 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_2689048 : Nat := 118140960795 + 2689048 * 2 ^ 59
def prefixEnd_2689048 : Nat := 4983230072969 + 3 ^ 40 * 2689048 * 2
def baseEnd_2689048 : Nat := 920516084674333547355533

theorem tailTrace_2689048 : CollatzResearch.WordTrace tailWord_2689048 prefixEnd_2689048 920516084674333547355533 := by
  unfold tailWord_2689048
  simp only [CollatzResearch.WordTrace]
  refine ⟨49038818981022911840261899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65385091974697215787015865 49038818981022911840261899)
  ·
    refine ⟨73558228471534367760392849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49038818981022911840261899 73558228471534367760392849)
    ·
      refine ⟨55168671353650775820294637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73558228471534367760392849 55168671353650775820294637)
      ·
        refine ⟨20688251757619040932610489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55168671353650775820294637 20688251757619040932610489)
        ·
          refine ⟨15516188818214280699457867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20688251757619040932610489 15516188818214280699457867)
          ·
            refine ⟨23274283227321421049186801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15516188818214280699457867 23274283227321421049186801)
            ·
              refine ⟨17455712420491065786890101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23274283227321421049186801 17455712420491065786890101)
              ·
                refine ⟨1636473039421037417520947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17455712420491065786890101 1636473039421037417520947)
                ·
                  refine ⟨2454709559131556126281421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636473039421037417520947 2454709559131556126281421)
                  ·
                    refine ⟨920516084674333547355533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454709559131556126281421 920516084674333547355533)
                    ·
                      rfl

theorem cell22_2689048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_2689048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689048 prefixEnd_2689048 := by exact prefixLift 2689048
  have htrace : WordTrace (prefixWord ++ tailWord_2689048) baseStart_2689048 baseEnd_2689048 := by
    simpa [prefixWord, tailWord_2689048, baseEnd_2689048] using wordTrace_append hprefix tailTrace_2689048
  have hstable : (prefixWord ++ tailWord_2689048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689048).length < 2 ^ (prefixWord ++ tailWord_2689048).sum := by decide
  have hdescent : baseEnd_2689048 < baseStart_2689048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689059 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_2689059 : Nat := 118140960795 + 2689059 * 2 ^ 59
def prefixEnd_2689059 : Nat := 4983230072969 + 3 ^ 40 * 2689059 * 2
def baseEnd_2689059 : Nat := 920519850199133185330499

theorem tailTrace_2689059 : CollatzResearch.WordTrace tailWord_2689059 prefixEnd_2689059 920519850199133185330499 := by
  unfold tailWord_2689059
  simp only [CollatzResearch.WordTrace]
  refine ⟨98078039165005972559174231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65385359443337315039449487 98078039165005972559174231)
  ·
    refine ⟨147117058747508958838761347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98078039165005972559174231 147117058747508958838761347)
    ·
      refine ⟨220675588121263438258142021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147117058747508958838761347 220675588121263438258142021)
      ·
        refine ⟨41376672772736894673401629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220675588121263438258142021 41376672772736894673401629)
        ·
          refine ⟨15516252289776335502525611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41376672772736894673401629 15516252289776335502525611)
          ·
            refine ⟨23274378434664503253788417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15516252289776335502525611 23274378434664503253788417)
            ·
              refine ⟨17455783825998377440341313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23274378434664503253788417 17455783825998377440341313)
              ·
                refine ⟨13091837869498783080255985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17455783825998377440341313 13091837869498783080255985)
                ·
                  refine ⟨9818878402124087310191989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13091837869498783080255985 9818878402124087310191989)
                  ·
                    refine ⟨920519850199133185330499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9818878402124087310191989 920519850199133185330499)
                    ·
                      rfl

theorem cell22_2689059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_2689059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689059 prefixEnd_2689059 := by exact prefixLift 2689059
  have htrace : WordTrace (prefixWord ++ tailWord_2689059) baseStart_2689059 baseEnd_2689059 := by
    simpa [prefixWord, tailWord_2689059, baseEnd_2689059] using wordTrace_append hprefix tailTrace_2689059
  have hstable : (prefixWord ++ tailWord_2689059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689059).length < 2 ^ (prefixWord ++ tailWord_2689059).sum := by decide
  have hdescent : baseEnd_2689059 < baseStart_2689059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689061 : List Nat := [1, 3, 1, 2, 2, 4, 2, 2, 5]
def baseStart_2689061 : Nat := 118140960795 + 2689061 * 2 ^ 59
def prefixEnd_2689061 : Nat := 4983230072969 + 3 ^ 40 * 2689061 * 2
def baseEnd_2689061 : Nat := 306840178280001948926831

theorem tailTrace_2689061 : CollatzResearch.WordTrace tailWord_2689061 prefixEnd_2689061 306840178280001948926831 := by
  unfold tailWord_2689061
  simp only [CollatzResearch.WordTrace]
  refine ⟨98078112110998726900747037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65385408073999151267164691 98078112110998726900747037)
  ·
    refine ⟨36779292041624522587780139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98078112110998726900747037 36779292041624522587780139)
    ·
      refine ⟨55168938062436783881670209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36779292041624522587780139 55168938062436783881670209)
      ·
        refine ⟨41376703546827587911252657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55168938062436783881670209 41376703546827587911252657)
        ·
          refine ⟨31032527660120690933439493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41376703546827587911252657 31032527660120690933439493)
          ·
            refine ⟨5818598936272629550019905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31032527660120690933439493 5818598936272629550019905)
            ·
              refine ⟨4363949202204472162514929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818598936272629550019905 4363949202204472162514929)
              ·
                refine ⟨3272961901653354121886197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363949202204472162514929 3272961901653354121886197)
                ·
                  refine ⟨306840178280001948926831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3272961901653354121886197 306840178280001948926831)
                  ·
                    rfl

theorem cell22_2689061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_2689061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689061 prefixEnd_2689061 := by exact prefixLift 2689061
  have htrace : WordTrace (prefixWord ++ tailWord_2689061) baseStart_2689061 baseEnd_2689061 := by
    simpa [prefixWord, tailWord_2689061, baseEnd_2689061] using wordTrace_append hprefix tailTrace_2689061
  have hstable : (prefixWord ++ tailWord_2689061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689061).length < 2 ^ (prefixWord ++ tailWord_2689061).sum := by decide
  have hdescent : baseEnd_2689061 < baseStart_2689061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689138 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_2689138 : Nat := 118140960795 + 2689138 * 2 ^ 59
def prefixEnd_2689138 : Nat := 4983230072969 + 3 ^ 40 * 2689138 * 2
def baseEnd_2689138 : Nat := 920546893513603312605257

theorem tailTrace_2689138 : CollatzResearch.WordTrace tailWord_2689138 prefixEnd_2689138 920546893513603312605257 := by
  unfold tailWord_2689138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24520230132929942262825017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65387280354479846034200045 24520230132929942262825017)
  ·
    refine ⟨18390172599697456697118763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24520230132929942262825017 18390172599697456697118763)
    ·
      refine ⟨27585258899546185045678145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390172599697456697118763 27585258899546185045678145)
      ·
        refine ⟨20688944174659638784258609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27585258899546185045678145 20688944174659638784258609)
        ·
          refine ⟨15516708130994729088193957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20688944174659638784258609 15516708130994729088193957)
          ·
            refine ⟨2909382774561511704036367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15516708130994729088193957 2909382774561511704036367)
            ·
              refine ⟨4364074161842267556054551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909382774561511704036367 4364074161842267556054551)
              ·
                refine ⟨6546111242763401334081827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364074161842267556054551 6546111242763401334081827)
                ·
                  refine ⟨9819166864145102001122741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546111242763401334081827 9819166864145102001122741)
                  ·
                    refine ⟨920546893513603312605257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9819166864145102001122741 920546893513603312605257)
                    ·
                      rfl

theorem cell22_2689138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_2689138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689138 prefixEnd_2689138 := by exact prefixLift 2689138
  have htrace : WordTrace (prefixWord ++ tailWord_2689138) baseStart_2689138 baseEnd_2689138 := by
    simpa [prefixWord, tailWord_2689138, baseEnd_2689138] using wordTrace_append hprefix tailTrace_2689138
  have hstable : (prefixWord ++ tailWord_2689138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689138).length < 2 ^ (prefixWord ++ tailWord_2689138).sum := by decide
  have hdescent : baseEnd_2689138 < baseStart_2689138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689164 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2689164 : Nat := 118140960795 + 2689164 * 2 ^ 59
def prefixEnd_2689164 : Nat := 4983230072969 + 3 ^ 40 * 2689164 * 2
def baseEnd_2689164 : Nat := 920555793844947911455177

theorem tailTrace_2689164 : CollatzResearch.WordTrace tailWord_2689164 prefixEnd_2689164 920555793844947911455177 := by
  unfold tailWord_2689164
  simp only [CollatzResearch.WordTrace]
  refine ⟨49040934414812787745873273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65387912553083716994497697 49040934414812787745873273)
  ·
    refine ⟨36780700811109590809404955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49040934414812787745873273 36780700811109590809404955)
    ·
      refine ⟨55171051216664386214107433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36780700811109590809404955 55171051216664386214107433)
      ·
        refine ⟨41378288412498289660580575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55171051216664386214107433 41378288412498289660580575)
        ·
          refine ⟨62067432618747434490870863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41378288412498289660580575 62067432618747434490870863)
          ·
            refine ⟨93101148928121151736306295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62067432618747434490870863 93101148928121151736306295)
            ·
              refine ⟨139651723392181727604459443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93101148928121151736306295 139651723392181727604459443)
              ·
                refine ⟨209477585088272591406689165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139651723392181727604459443 209477585088272591406689165)
                ·
                  refine ⟨78554094408102221777508437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209477585088272591406689165 78554094408102221777508437)
                  ·
                    refine ⟨920555793844947911455177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78554094408102221777508437 920555793844947911455177)
                    ·
                      rfl

theorem cell22_2689164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2689164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689164 prefixEnd_2689164 := by exact prefixLift 2689164
  have htrace : WordTrace (prefixWord ++ tailWord_2689164) baseStart_2689164 baseEnd_2689164 := by
    simpa [prefixWord, tailWord_2689164, baseEnd_2689164] using wordTrace_append hprefix tailTrace_2689164
  have hstable : (prefixWord ++ tailWord_2689164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689164).length < 2 ^ (prefixWord ++ tailWord_2689164).sum := by decide
  have hdescent : baseEnd_2689164 < baseStart_2689164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689179 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 7]
def baseStart_2689179 : Nat := 118140960795 + 2689179 * 2 ^ 59
def prefixEnd_2689179 : Nat := 4983230072969 + 3 ^ 40 * 2689179 * 2
def baseEnd_2689179 : Nat := 306853642883830957443377

theorem tailTrace_2689179 : CollatzResearch.WordTrace tailWord_2689179 prefixEnd_2689179 306853642883830957443377 := by
  unfold tailWord_2689179
  simp only [CollatzResearch.WordTrace]
  refine ⟨98082415924571233053542591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65388277283047488702361727 98082415924571233053542591)
  ·
    refine ⟨147123623886856849580313887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98082415924571233053542591 147123623886856849580313887)
    ·
      refine ⟨220685435830285274370470831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147123623886856849580313887 220685435830285274370470831)
      ·
        refine ⟨331028153745427911555706247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220685435830285274370470831 331028153745427911555706247)
        ·
          refine ⟨496542230618141867333559371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331028153745427911555706247 496542230618141867333559371)
          ·
            refine ⟨744813345927212801000339057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496542230618141867333559371 744813345927212801000339057)
            ·
              refine ⟨558610009445409600750254293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744813345927212801000339057 558610009445409600750254293)
              ·
                refine ⟨13092422096376787517584085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 558610009445409600750254293 13092422096376787517584085)
                ·
                  refine ⟨306853642883830957443377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13092422096376787517584085 306853642883830957443377)
                  ·
                    rfl

theorem cell22_2689179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_2689179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689179 prefixEnd_2689179 := by exact prefixLift 2689179
  have htrace : WordTrace (prefixWord ++ tailWord_2689179) baseStart_2689179 baseEnd_2689179 := by
    simpa [prefixWord, tailWord_2689179, baseEnd_2689179] using wordTrace_append hprefix tailTrace_2689179
  have hstable : (prefixWord ++ tailWord_2689179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689179).length < 2 ^ (prefixWord ++ tailWord_2689179).sum := by decide
  have hdescent : baseEnd_2689179 < baseStart_2689179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689204 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2689204 : Nat := 118140960795 + 2689204 * 2 ^ 59
def prefixEnd_2689204 : Nat := 4983230072969 + 3 ^ 40 * 2689204 * 2
def baseEnd_2689204 : Nat := 920569486662401140455055

theorem tailTrace_2689204 : CollatzResearch.WordTrace tailWord_2689204 prefixEnd_2689204 920569486662401140455055 := by
  unfold tailWord_2689204
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041663874740331161601333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65388885166320441548801777 49041663874740331161601333)
  ·
    refine ⟨4597655988256906046400125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49041663874740331161601333 4597655988256906046400125)
    ·
      refine ⟨1724120995596339767400047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4597655988256906046400125 1724120995596339767400047)
      ·
        refine ⟨2586181493394509651100071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724120995596339767400047 2586181493394509651100071)
        ·
          refine ⟨3879272240091764476650107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586181493394509651100071 3879272240091764476650107)
          ·
            refine ⟨5818908360137646714975161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879272240091764476650107 5818908360137646714975161)
            ·
              refine ⟨4364181270103235036231371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818908360137646714975161 4364181270103235036231371)
              ·
                refine ⟨6546271905154852554347057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364181270103235036231371 6546271905154852554347057)
                ·
                  refine ⟨4909703928866139415760293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546271905154852554347057 4909703928866139415760293)
                  ·
                    refine ⟨920569486662401140455055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909703928866139415760293 920569486662401140455055)
                    ·
                      rfl

theorem cell22_2689204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2689204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689204 prefixEnd_2689204 := by exact prefixLift 2689204
  have htrace : WordTrace (prefixWord ++ tailWord_2689204) baseStart_2689204 baseEnd_2689204 := by
    simpa [prefixWord, tailWord_2689204, baseEnd_2689204] using wordTrace_append hprefix tailTrace_2689204
  have hstable : (prefixWord ++ tailWord_2689204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689204).length < 2 ^ (prefixWord ++ tailWord_2689204).sum := by decide
  have hdescent : baseEnd_2689204 < baseStart_2689204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689234 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2689234 : Nat := 118140960795 + 2689234 * 2 ^ 59
def prefixEnd_2689234 : Nat := 4983230072969 + 3 ^ 40 * 2689234 * 2
def baseEnd_2689234 : Nat := 920579756275491062204963

theorem tailTrace_2689234 : CollatzResearch.WordTrace tailWord_2689234 prefixEnd_2689234 920579756275491062204963 := by
  unfold tailWord_2689234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521105484842994361698689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65389614626247984964529837 24521105484842994361698689)
  ·
    refine ⟨18390829113632245771274017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24521105484842994361698689 18390829113632245771274017)
    ·
      refine ⟨13793121835224184328455513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18390829113632245771274017 13793121835224184328455513)
      ·
        refine ⟨10344841376418138246341635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13793121835224184328455513 10344841376418138246341635)
        ·
          refine ⟨15517262064627207369512453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10344841376418138246341635 15517262064627207369512453)
          ·
            refine ⟨2909486637117601381783585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15517262064627207369512453 2909486637117601381783585)
            ·
              refine ⟨2182114977838201036337689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909486637117601381783585 2182114977838201036337689)
              ·
                refine ⟨1636586233378650777253267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182114977838201036337689 1636586233378650777253267)
                ·
                  refine ⟨2454879350067976165879901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636586233378650777253267 2454879350067976165879901)
                  ·
                    refine ⟨920579756275491062204963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454879350067976165879901 920579756275491062204963)
                    ·
                      rfl

theorem cell22_2689234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2689234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689234 prefixEnd_2689234 := by exact prefixLift 2689234
  have htrace : WordTrace (prefixWord ++ tailWord_2689234) baseStart_2689234 baseEnd_2689234 := by
    simpa [prefixWord, tailWord_2689234, baseEnd_2689234] using wordTrace_append hprefix tailTrace_2689234
  have hstable : (prefixWord ++ tailWord_2689234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689234).length < 2 ^ (prefixWord ++ tailWord_2689234).sum := by decide
  have hdescent : baseEnd_2689234 < baseStart_2689234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689290 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_2689290 : Nat := 118140960795 + 2689290 * 2 ^ 59
def prefixEnd_2689290 : Nat := 4983230072969 + 3 ^ 40 * 2689290 * 2
def baseEnd_2689290 : Nat := 920598926219925582804791

theorem tailTrace_2689290 : CollatzResearch.WordTrace tailWord_2689290 prefixEnd_2689290 920598926219925582804791 := by
  unfold tailWord_2689290
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521616106792274752708331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65390976284779399340555549 24521616106792274752708331)
  ·
    refine ⟨36782424160188412129062497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24521616106792274752708331 36782424160188412129062497)
    ·
      refine ⟨27586818120141309096796873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36782424160188412129062497 27586818120141309096796873)
      ·
        refine ⟨20690113590105981822597655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27586818120141309096796873 20690113590105981822597655)
        ·
          refine ⟨31035170385158972733896483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20690113590105981822597655 31035170385158972733896483)
          ·
            refine ⟨46552755577738459100844725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31035170385158972733896483 46552755577738459100844725)
            ·
              refine ⟨4364320835412980540704193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46552755577738459100844725 4364320835412980540704193)
              ·
                refine ⟨3273240626559735405528145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364320835412980540704193 3273240626559735405528145)
                ·
                  refine ⟨2454930469919801554146109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273240626559735405528145 2454930469919801554146109)
                  ·
                    refine ⟨920598926219925582804791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2454930469919801554146109 920598926219925582804791)
                    ·
                      rfl

theorem cell22_2689290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_2689290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689290 prefixEnd_2689290 := by exact prefixLift 2689290
  have htrace : WordTrace (prefixWord ++ tailWord_2689290) baseStart_2689290 baseEnd_2689290 := by
    simpa [prefixWord, tailWord_2689290, baseEnd_2689290] using wordTrace_append hprefix tailTrace_2689290
  have hstable : (prefixWord ++ tailWord_2689290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689290).length < 2 ^ (prefixWord ++ tailWord_2689290).sum := by decide
  have hdescent : baseEnd_2689290 < baseStart_2689290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689326 : List Nat := [4, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_2689326 : Nat := 118140960795 + 2689326 * 2 ^ 59
def prefixEnd_2689326 : Nat := 4983230072969 + 3 ^ 40 * 2689326 * 2
def baseEnd_2689326 : Nat := 306870416585211162968227

theorem tailTrace_2689326 : CollatzResearch.WordTrace tailWord_2689326 prefixEnd_2689326 306870416585211162968227 := by
  unfold tailWord_2689326
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260972181879834644892979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65391851636692451439429221 12260972181879834644892979)
  ·
    refine ⟨18391458272819751967339469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260972181879834644892979 18391458272819751967339469)
    ·
      refine ⟨6896796852307406987752301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18391458272819751967339469 6896796852307406987752301)
      ·
        refine ⟨2586298819615277620407113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6896796852307406987752301 2586298819615277620407113)
        ·
          refine ⟨1939724114711458215305335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2586298819615277620407113 1939724114711458215305335)
          ·
            refine ⟨2909586172067187322958003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939724114711458215305335 2909586172067187322958003)
            ·
              refine ⟨4364379258100780984437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909586172067187322958003 4364379258100780984437005)
              ·
                refine ⟨1636642221787792869163877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364379258100780984437005 1636642221787792869163877)
                ·
                  refine ⟨306870416585211162968227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636642221787792869163877 306870416585211162968227)
                  ·
                    rfl

theorem cell22_2689326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_2689326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689326 prefixEnd_2689326 := by exact prefixLift 2689326
  have htrace : WordTrace (prefixWord ++ tailWord_2689326) baseStart_2689326 baseEnd_2689326 := by
    simpa [prefixWord, tailWord_2689326, baseEnd_2689326] using wordTrace_append hprefix tailTrace_2689326
  have hstable : (prefixWord ++ tailWord_2689326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689326).length < 2 ^ (prefixWord ++ tailWord_2689326).sum := by decide
  have hdescent : baseEnd_2689326 < baseStart_2689326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689331 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 9]
def baseStart_2689331 : Nat := 118140960795 + 2689331 * 2 ^ 59
def prefixEnd_2689331 : Nat := 4983230072969 + 3 ^ 40 * 2689331 * 2
def baseEnd_2689331 : Nat := 306870987119271714176555

theorem tailTrace_2689331 : CollatzResearch.WordTrace tailWord_2689331 prefixEnd_2689331 306870987119271714176555 := by
  unfold tailWord_2689331
  simp only [CollatzResearch.WordTrace]
  refine ⟨98087959820020563013075847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65391973213347042008717231 98087959820020563013075847)
  ·
    refine ⟨147131939730030844519613771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98087959820020563013075847 147131939730030844519613771)
    ·
      refine ⟨220697909595046266779420657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147131939730030844519613771 220697909595046266779420657)
      ·
        refine ⟨165523432196284700084565493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220697909595046266779420657 165523432196284700084565493)
        ·
          refine ⟨15517821768401690632928015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165523432196284700084565493 15517821768401690632928015)
          ·
            refine ⟨23276732652602535949392023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15517821768401690632928015 23276732652602535949392023)
            ·
              refine ⟨34915098978903803924088035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23276732652602535949392023 34915098978903803924088035)
              ·
                refine ⟨52372648468355705886132053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34915098978903803924088035 52372648468355705886132053)
                ·
                  refine ⟨306870987119271714176555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52372648468355705886132053 306870987119271714176555)
                  ·
                    rfl

theorem cell22_2689331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_2689331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689331 prefixEnd_2689331 := by exact prefixLift 2689331
  have htrace : WordTrace (prefixWord ++ tailWord_2689331) baseStart_2689331 baseEnd_2689331 := by
    simpa [prefixWord, tailWord_2689331, baseEnd_2689331] using wordTrace_append hprefix tailTrace_2689331
  have hstable : (prefixWord ++ tailWord_2689331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689331).length < 2 ^ (prefixWord ++ tailWord_2689331).sum := by decide
  have hdescent : baseEnd_2689331 < baseStart_2689331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689365 : List Nat := [1, 3, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2689365 : Nat := 118140960795 + 2689365 * 2 ^ 59
def prefixEnd_2689365 : Nat := 4983230072969 + 3 ^ 40 * 2689365 * 2
def baseEnd_2689365 : Nat := 306874866750883462393187

theorem tailTrace_2689365 : CollatzResearch.WordTrace tailWord_2689365 prefixEnd_2689365 306874866750883462393187 := by
  unfold tailWord_2689365
  simp only [CollatzResearch.WordTrace]
  refine ⟨98089199901897386819813549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65392799934598257879875699 98089199901897386819813549)
  ·
    refine ⟨36783449963211520057430081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98089199901897386819813549 36783449963211520057430081)
    ·
      refine ⟨27587587472408640043072561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36783449963211520057430081 27587587472408640043072561)
      ·
        refine ⟨20690690604306480032304421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27587587472408640043072561 20690690604306480032304421)
        ·
          refine ⟨3879504488307465006057079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20690690604306480032304421 3879504488307465006057079)
          ·
            refine ⟨5819256732461197509085619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879504488307465006057079 5819256732461197509085619)
            ·
              refine ⟨8728885098691796263628429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819256732461197509085619 8728885098691796263628429)
              ·
                refine ⟨3273331912009423598860661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8728885098691796263628429 3273331912009423598860661)
                ·
                  refine ⟨306874866750883462393187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273331912009423598860661 306874866750883462393187)
                  ·
                    rfl

theorem cell22_2689365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2689365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689365 prefixEnd_2689365 := by exact prefixLift 2689365
  have htrace : WordTrace (prefixWord ++ tailWord_2689365) baseStart_2689365 baseEnd_2689365 := by
    simpa [prefixWord, tailWord_2689365, baseEnd_2689365] using wordTrace_append hprefix tailTrace_2689365
  have hstable : (prefixWord ++ tailWord_2689365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689365).length < 2 ^ (prefixWord ++ tailWord_2689365).sum := by decide
  have hdescent : baseEnd_2689365 < baseStart_2689365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689440 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_2689440 : Nat := 118140960795 + 2689440 * 2 ^ 59
def prefixEnd_2689440 : Nat := 4983230072969 + 3 ^ 40 * 2689440 * 2
def baseEnd_2689440 : Nat := 920650274285375191554331

theorem tailTrace_2689440 : CollatzResearch.WordTrace tailWord_2689440 prefixEnd_2689440 920650274285375191554331 := by
  unfold tailWord_2689440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49045967688312837314396887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65394623584417116419195849 49045967688312837314396887)
  ·
    refine ⟨73568951532469255971595331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49045967688312837314396887 73568951532469255971595331)
    ·
      refine ⟨110353427298703883957392997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73568951532469255971595331 110353427298703883957392997)
      ·
        refine ⟨20691267618506978242011187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110353427298703883957392997 20691267618506978242011187)
        ·
          refine ⟨31036901427760467363016781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691267618506978242011187 31036901427760467363016781)
          ·
            refine ⟨11638838035410175261131293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31036901427760467363016781 11638838035410175261131293)
            ·
              refine ⟨4364564263278815722924235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11638838035410175261131293 4364564263278815722924235)
              ·
                refine ⟨6546846394918223584386353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364564263278815722924235 6546846394918223584386353)
                ·
                  refine ⟨4910134796188667688289765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546846394918223584386353 4910134796188667688289765)
                  ·
                    refine ⟨920650274285375191554331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910134796188667688289765 920650274285375191554331)
                    ·
                      rfl

theorem cell22_2689440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_2689440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689440 prefixEnd_2689440 := by exact prefixLift 2689440
  have htrace : WordTrace (prefixWord ++ tailWord_2689440) baseStart_2689440 baseEnd_2689440 := by
    simpa [prefixWord, tailWord_2689440, baseEnd_2689440] using wordTrace_append hprefix tailTrace_2689440
  have hstable : (prefixWord ++ tailWord_2689440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689440).length < 2 ^ (prefixWord ++ tailWord_2689440).sum := by decide
  have hdescent : baseEnd_2689440 < baseStart_2689440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689476 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2689476 : Nat := 118140960795 + 2689476 * 2 ^ 59
def prefixEnd_2689476 : Nat := 4983230072969 + 3 ^ 40 * 2689476 * 2
def baseEnd_2689476 : Nat := 920662597821083097654221

theorem tailTrace_2689476 : CollatzResearch.WordTrace tailWord_2689476 prefixEnd_2689476 920662597821083097654221 := by
  unfold tailWord_2689476
  simp only [CollatzResearch.WordTrace]
  refine ⟨49046624202247626388552141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65395498936330168518069521 49046624202247626388552141)
  ·
    refine ⟨18392484075842859895707053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49046624202247626388552141 18392484075842859895707053)
    ·
      refine ⟨6897181528441072460890145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18392484075842859895707053 6897181528441072460890145)
      ·
        refine ⟨5172886146330804345667609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6897181528441072460890145 5172886146330804345667609)
        ·
          refine ⟨3879664609748103259250707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5172886146330804345667609 3879664609748103259250707)
          ·
            refine ⟨5819496914622154888876061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879664609748103259250707 5819496914622154888876061)
            ·
              refine ⟨2182311342983308083328523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819496914622154888876061 2182311342983308083328523)
              ·
                refine ⟨3273467014474962124992785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182311342983308083328523 3273467014474962124992785)
                ·
                  refine ⟨2455100260856221593744589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273467014474962124992785 2455100260856221593744589)
                  ·
                    refine ⟨920662597821083097654221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455100260856221593744589 920662597821083097654221)
                    ·
                      rfl

theorem cell22_2689476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2689476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689476 prefixEnd_2689476 := by exact prefixLift 2689476
  have htrace : WordTrace (prefixWord ++ tailWord_2689476) baseStart_2689476 baseEnd_2689476 := by
    simpa [prefixWord, tailWord_2689476, baseEnd_2689476] using wordTrace_append hprefix tailTrace_2689476
  have hstable : (prefixWord ++ tailWord_2689476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689476).length < 2 ^ (prefixWord ++ tailWord_2689476).sum := by decide
  have hdescent : baseEnd_2689476 < baseStart_2689476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689547 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 1, 4]
def baseStart_2689547 : Nat := 118140960795 + 2689547 * 2 ^ 59
def prefixEnd_2689547 : Nat := 4983230072969 + 3 ^ 40 * 2689547 * 2
def baseEnd_2689547 : Nat := 920686902572062579129003

theorem tailTrace_2689547 : CollatzResearch.WordTrace tailWord_2689547 prefixEnd_2689547 920686902572062579129003 := by
  unfold tailWord_2689547
  simp only [CollatzResearch.WordTrace]
  refine ⟨98095837987238031902938895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65397225324825354601959263 98095837987238031902938895)
  ·
    refine ⟨147143756980857047854408343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98095837987238031902938895 147143756980857047854408343)
    ·
      refine ⟨220715635471285571781612515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147143756980857047854408343 220715635471285571781612515)
      ·
        refine ⟨331073453206928357672418773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220715635471285571781612515 331073453206928357672418773)
        ·
          refine ⟨7759534059537383382947315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 331073453206928357672418773 7759534059537383382947315)
          ·
            refine ⟨11639301089306075074420973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7759534059537383382947315 11639301089306075074420973)
            ·
              refine ⟨4364737908489778152907865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11639301089306075074420973 4364737908489778152907865)
              ·
                refine ⟨3273553431367333614680899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364737908489778152907865 3273553431367333614680899)
                ·
                  refine ⟨4910330147051000422021349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273553431367333614680899 4910330147051000422021349)
                  ·
                    refine ⟨920686902572062579129003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910330147051000422021349 920686902572062579129003)
                    ·
                      rfl

theorem cell22_2689547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 4].length) (baseStart_2689547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689547 prefixEnd_2689547 := by exact prefixLift 2689547
  have htrace : WordTrace (prefixWord ++ tailWord_2689547) baseStart_2689547 baseEnd_2689547 := by
    simpa [prefixWord, tailWord_2689547, baseEnd_2689547] using wordTrace_append hprefix tailTrace_2689547
  have hstable : (prefixWord ++ tailWord_2689547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689547).length < 2 ^ (prefixWord ++ tailWord_2689547).sum := by decide
  have hdescent : baseEnd_2689547 < baseStart_2689547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689560 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_2689560 : Nat := 118140960795 + 2689560 * 2 ^ 59
def prefixEnd_2689560 : Nat := 4983230072969 + 3 ^ 40 * 2689560 * 2
def baseEnd_2689560 : Nat := 920691352737734878553963

theorem tailTrace_2689560 : CollatzResearch.WordTrace tailWord_2689560 prefixEnd_2689560 920691352737734878553963 := by
  unfold tailWord_2689560
  simp only [CollatzResearch.WordTrace]
  refine ⟨49048156068095467561581067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65397541424127290082108089 49048156068095467561581067)
  ·
    refine ⟨73572234102143201342371601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49048156068095467561581067 73572234102143201342371601)
    ·
      refine ⟨55179175576607401006778701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73572234102143201342371601 55179175576607401006778701)
      ·
        refine ⟨20692190841227775377542013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55179175576607401006778701 20692190841227775377542013)
        ·
          refine ⟨7759571565460415766578255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20692190841227775377542013 7759571565460415766578255)
          ·
            refine ⟨11639357348190623649867383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7759571565460415766578255 11639357348190623649867383)
            ·
              refine ⟨17459036022285935474801075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11639357348190623649867383 17459036022285935474801075)
              ·
                refine ⟨26188554033428903212201613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17459036022285935474801075 26188554033428903212201613)
                ·
                  refine ⟨9820707762535838704575605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26188554033428903212201613 9820707762535838704575605)
                  ·
                    refine ⟨920691352737734878553963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9820707762535838704575605 920691352737734878553963)
                    ·
                      rfl

theorem cell22_2689560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_2689560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689560 prefixEnd_2689560 := by exact prefixLift 2689560
  have htrace : WordTrace (prefixWord ++ tailWord_2689560) baseStart_2689560 baseEnd_2689560 := by
    simpa [prefixWord, tailWord_2689560, baseEnd_2689560] using wordTrace_append hprefix tailTrace_2689560
  have hstable : (prefixWord ++ tailWord_2689560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689560).length < 2 ^ (prefixWord ++ tailWord_2689560).sum := by decide
  have hdescent : baseEnd_2689560 < baseStart_2689560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689564 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2689564 : Nat := 118140960795 + 2689564 * 2 ^ 59
def prefixEnd_2689564 : Nat := 4983230072969 + 3 ^ 40 * 2689564 * 2
def baseEnd_2689564 : Nat := 920692722019480201453951

theorem tailTrace_2689564 : CollatzResearch.WordTrace tailWord_2689564 prefixEnd_2689564 920692722019480201453951 := by
  unfold tailWord_2689564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49048229014088221903153873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65397638685450962537538497 49048229014088221903153873)
  ·
    refine ⟨36786171760566166427365405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49048229014088221903153873 36786171760566166427365405)
    ·
      refine ⟨13794814410212312410262027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36786171760566166427365405 13794814410212312410262027)
      ·
        refine ⟨20692221615318468615393041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794814410212312410262027 20692221615318468615393041)
        ·
          refine ⟨15519166211488851461544781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20692221615318468615393041 15519166211488851461544781)
          ·
            refine ⟨5819687329308319298079293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15519166211488851461544781 5819687329308319298079293)
            ·
              refine ⟨2182382748490619736779735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819687329308319298079293 2182382748490619736779735)
              ·
                refine ⟨3273574122735929605169603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182382748490619736779735 3273574122735929605169603)
                ·
                  refine ⟨4910361184103894407754405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273574122735929605169603 4910361184103894407754405)
                  ·
                    refine ⟨920692722019480201453951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910361184103894407754405 920692722019480201453951)
                    ·
                      rfl

theorem cell22_2689564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2689564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689564 prefixEnd_2689564 := by exact prefixLift 2689564
  have htrace : WordTrace (prefixWord ++ tailWord_2689564) baseStart_2689564 baseEnd_2689564 := by
    simpa [prefixWord, tailWord_2689564, baseEnd_2689564] using wordTrace_append hprefix tailTrace_2689564
  have hstable : (prefixWord ++ tailWord_2689564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689564).length < 2 ^ (prefixWord ++ tailWord_2689564).sum := by decide
  have hdescent : baseEnd_2689564 < baseStart_2689564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689607 : List Nat := [1, 1, 4, 1, 4, 2, 3, 6]
def baseStart_2689607 : Nat := 118140960795 + 2689607 * 2 ^ 59
def prefixEnd_2689607 : Nat := 4983230072969 + 3 ^ 40 * 2689607 * 2
def baseEnd_2689607 : Nat := 102300826866471380292091

theorem tailTrace_2689607 : CollatzResearch.WordTrace tailWord_2689607 prefixEnd_2689607 102300826866471380292091 := by
  unfold tailWord_2689607
  simp only [CollatzResearch.WordTrace]
  refine ⟨98098026367020662150123075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65398684244680441433415383 98098026367020662150123075)
  ·
    refine ⟨147147039550530993225184613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98098026367020662150123075 147147039550530993225184613)
    ·
      refine ⟨27590069915724561229722115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147147039550530993225184613 27590069915724561229722115)
      ·
        refine ⟨41385104873586841844583173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27590069915724561229722115 41385104873586841844583173)
        ·
          refine ⟨7759707163797532845859345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41385104873586841844583173 7759707163797532845859345)
          ·
            refine ⟨5819780372848149634394509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7759707163797532845859345 5819780372848149634394509)
            ·
              refine ⟨2182417639818056112897941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819780372848149634394509 2182417639818056112897941)
              ·
                refine ⟨102300826866471380292091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2182417639818056112897941 102300826866471380292091)
                ·
                  rfl

theorem cell22_2689607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 6].length) (baseStart_2689607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689607 prefixEnd_2689607 := by exact prefixLift 2689607
  have htrace : WordTrace (prefixWord ++ tailWord_2689607) baseStart_2689607 baseEnd_2689607 := by
    simpa [prefixWord, tailWord_2689607, baseEnd_2689607] using wordTrace_append hprefix tailTrace_2689607
  have hstable : (prefixWord ++ tailWord_2689607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689607).length < 2 ^ (prefixWord ++ tailWord_2689607).sum := by decide
  have hdescent : baseEnd_2689607 < baseStart_2689607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689628 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2689628 : Nat := 118140960795 + 2689628 * 2 ^ 59
def prefixEnd_2689628 : Nat := 4983230072969 + 3 ^ 40 * 2689628 * 2
def baseEnd_2689628 : Nat := 920714630527405367853755

theorem tailTrace_2689628 : CollatzResearch.WordTrace tailWord_2689628 prefixEnd_2689628 920714630527405367853755 := by
  unfold tailWord_2689628
  simp only [CollatzResearch.WordTrace]
  refine ⟨49049396149972291368318769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65399194866629721824425025 49049396149972291368318769)
  ·
    refine ⟨36787047112479218526239077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49049396149972291368318769 36787047112479218526239077)
    ·
      refine ⟨6897571333589853473669827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36787047112479218526239077 6897571333589853473669827)
      ·
        refine ⟨10346357000384780210504741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897571333589853473669827 10346357000384780210504741)
        ·
          refine ⟨1939941937572146289469639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10346357000384780210504741 1939941937572146289469639)
          ·
            refine ⟨2909912906358219434204459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939941937572146289469639 2909912906358219434204459)
            ·
              refine ⟨4364869359537329151306689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909912906358219434204459 4364869359537329151306689)
              ·
                refine ⟨3273652019652996863480017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364869359537329151306689 3273652019652996863480017)
                ·
                  refine ⟨2455239014739747647610013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273652019652996863480017 2455239014739747647610013)
                  ·
                    refine ⟨920714630527405367853755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455239014739747647610013 920714630527405367853755)
                    ·
                      rfl

theorem cell22_2689628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2689628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689628 prefixEnd_2689628 := by exact prefixLift 2689628
  have htrace : WordTrace (prefixWord ++ tailWord_2689628) baseStart_2689628 baseEnd_2689628 := by
    simpa [prefixWord, tailWord_2689628, baseEnd_2689628] using wordTrace_append hprefix tailTrace_2689628
  have hstable : (prefixWord ++ tailWord_2689628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689628).length < 2 ^ (prefixWord ++ tailWord_2689628).sum := by decide
  have hdescent : baseEnd_2689628 < baseStart_2689628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689635 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 7]
def baseStart_2689635 : Nat := 118140960795 + 2689635 * 2 ^ 59
def prefixEnd_2689635 : Nat := 4983230072969 + 3 ^ 40 * 2689635 * 2
def baseEnd_2689635 : Nat := 306905675590153227642911

theorem tailTrace_2689635 : CollatzResearch.WordTrace tailWord_2689635 prefixEnd_2689635 306905675590153227642911 := by
  unfold tailWord_2689635
  simp only [CollatzResearch.WordTrace]
  refine ⟨98099047610919222932142359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65399365073946148621428239 98099047610919222932142359)
  ·
    refine ⟨147148571416378834398213539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98099047610919222932142359 147148571416378834398213539)
    ·
      refine ⟨220722857124568251597320309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147148571416378834398213539 220722857124568251597320309)
      ·
        refine ⟨20692767855428273587248779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220722857124568251597320309 20692767855428273587248779)
        ·
          refine ⟨31039151783142410380873169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20692767855428273587248779 31039151783142410380873169)
          ·
            refine ⟨23279363837356807785654877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31039151783142410380873169 23279363837356807785654877)
            ·
              refine ⟨8729761439008802919620579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23279363837356807785654877 8729761439008802919620579)
              ·
                refine ⟨13094642158513204379430869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729761439008802919620579 13094642158513204379430869)
                ·
                  refine ⟨306905675590153227642911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13094642158513204379430869 306905675590153227642911)
                  ·
                    rfl

theorem cell22_2689635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_2689635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689635 prefixEnd_2689635 := by exact prefixLift 2689635
  have htrace : WordTrace (prefixWord ++ tailWord_2689635) baseStart_2689635 baseEnd_2689635 := by
    simpa [prefixWord, tailWord_2689635, baseEnd_2689635] using wordTrace_append hprefix tailTrace_2689635
  have hstable : (prefixWord ++ tailWord_2689635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689635).length < 2 ^ (prefixWord ++ tailWord_2689635).sum := by decide
  have hdescent : baseEnd_2689635 < baseStart_2689635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689690 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_2689690 : Nat := 118140960795 + 2689690 * 2 ^ 59
def prefixEnd_2689690 : Nat := 4983230072969 + 3 ^ 40 * 2689690 * 2
def baseEnd_2689690 : Nat := 920735854394457872803565

theorem tailTrace_2689690 : CollatzResearch.WordTrace tailWord_2689690 prefixEnd_2689690 920735854394457872803565 := by
  unfold tailWord_2689690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24525263406429991831348631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65400702417146644883596349 24525263406429991831348631)
  ·
    refine ⟨36787895109644987747022947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24525263406429991831348631 36787895109644987747022947)
    ·
      refine ⟨55181842664467481620534421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36787895109644987747022947 55181842664467481620534421)
      ·
        refine ⟨2586648874896913200962551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55181842664467481620534421 2586648874896913200962551)
        ·
          refine ⟨3879973312345369801443827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586648874896913200962551 3879973312345369801443827)
          ·
            refine ⟨5819959968518054702165741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879973312345369801443827 5819959968518054702165741)
            ·
              refine ⟨2182484988194270513312153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5819959968518054702165741 2182484988194270513312153)
              ·
                refine ⟨1636863741145702884984115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182484988194270513312153 1636863741145702884984115)
                ·
                  refine ⟨2455295611718554327476173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636863741145702884984115 2455295611718554327476173)
                  ·
                    refine ⟨920735854394457872803565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455295611718554327476173 920735854394457872803565)
                    ·
                      rfl

theorem cell22_2689690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_2689690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689690 prefixEnd_2689690 := by exact prefixLift 2689690
  have htrace : WordTrace (prefixWord ++ tailWord_2689690) baseStart_2689690 baseEnd_2689690 := by
    simpa [prefixWord, tailWord_2689690, baseEnd_2689690] using wordTrace_append hprefix tailTrace_2689690
  have hstable : (prefixWord ++ tailWord_2689690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689690).length < 2 ^ (prefixWord ++ tailWord_2689690).sum := by decide
  have hdescent : baseEnd_2689690 < baseStart_2689690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689703 : List Nat := [1, 1, 6, 3, 1, 2, 2, 1, 5]
def baseStart_2689703 : Nat := 118140960795 + 2689703 * 2 ^ 59
def prefixEnd_2689703 : Nat := 4983230072969 + 3 ^ 40 * 2689703 * 2
def baseEnd_2689703 : Nat := 306913434853376724076175

theorem tailTrace_2689703 : CollatzResearch.WordTrace tailWord_2689703 prefixEnd_2689703 306913434853376724076175 := by
  unfold tailWord_2689703
  simp only [CollatzResearch.WordTrace]
  refine ⟨98101527774672870545617763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65401018516448580363745175 98101527774672870545617763)
  ·
    refine ⟨147152291662009305818426645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98101527774672870545617763 147152291662009305818426645)
    ·
      refine ⟨6897763671656686210238749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147152291662009305818426645 6897763671656686210238749)
      ·
        refine ⟨2586661376871257328839531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6897763671656686210238749 2586661376871257328839531)
        ·
          refine ⟨3879992065306885993259297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586661376871257328839531 3879992065306885993259297)
          ·
            refine ⟨2909994048980164494944473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879992065306885993259297 2909994048980164494944473)
            ·
              refine ⟨2182495536735123371208355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909994048980164494944473 2182495536735123371208355)
              ·
                refine ⟨3273743305102685056812533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182495536735123371208355 3273743305102685056812533)
                ·
                  refine ⟨306913434853376724076175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273743305102685056812533 306913434853376724076175)
                  ·
                    rfl

theorem cell22_2689703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 5].length) (baseStart_2689703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689703 prefixEnd_2689703 := by exact prefixLift 2689703
  have htrace : WordTrace (prefixWord ++ tailWord_2689703) baseStart_2689703 baseEnd_2689703 := by
    simpa [prefixWord, tailWord_2689703, baseEnd_2689703] using wordTrace_append hprefix tailTrace_2689703
  have hstable : (prefixWord ++ tailWord_2689703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689703).length < 2 ^ (prefixWord ++ tailWord_2689703).sum := by decide
  have hdescent : baseEnd_2689703 < baseStart_2689703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689727 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2689727 : Nat := 118140960795 + 2689727 * 2 ^ 59
def prefixEnd_2689727 : Nat := 4983230072969 + 3 ^ 40 * 2689727 * 2
def baseEnd_2689727 : Nat := 920748520250602109628451

theorem tailTrace_2689727 : CollatzResearch.WordTrace tailWord_2689727 prefixEnd_2689727 920748520250602109628451 := by
  unfold tailWord_2689727
  simp only [CollatzResearch.WordTrace]
  refine ⟨98102403126585922644491435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65401602084390615096327623 98102403126585922644491435)
  ·
    refine ⟨147153604689878883966737153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98102403126585922644491435 147153604689878883966737153)
    ·
      refine ⟨110365203517409162975052865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147153604689878883966737153 110365203517409162975052865)
      ·
        refine ⟨82773902638056872231289649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110365203517409162975052865 82773902638056872231289649)
        ·
          refine ⟨62080426978542654173467237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82773902638056872231289649 62080426978542654173467237)
          ·
            refine ⟨11640080058476747657525107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62080426978542654173467237 11640080058476747657525107)
            ·
              refine ⟨17460120087715121486287661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640080058476747657525107 17460120087715121486287661)
              ·
                refine ⟨6547545032893170557357873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17460120087715121486287661 6547545032893170557357873)
                ·
                  refine ⟨4910658774669877918018405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547545032893170557357873 4910658774669877918018405)
                  ·
                    refine ⟨920748520250602109628451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910658774669877918018405 920748520250602109628451)
                    ·
                      rfl

theorem cell22_2689727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2689727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689727 prefixEnd_2689727 := by exact prefixLift 2689727
  have htrace : WordTrace (prefixWord ++ tailWord_2689727) baseStart_2689727 baseEnd_2689727 := by
    simpa [prefixWord, tailWord_2689727, baseEnd_2689727] using wordTrace_append hprefix tailTrace_2689727
  have hstable : (prefixWord ++ tailWord_2689727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689727).length < 2 ^ (prefixWord ++ tailWord_2689727).sum := by decide
  have hdescent : baseEnd_2689727 < baseStart_2689727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689774 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2689774 : Nat := 118140960795 + 2689774 * 2 ^ 59
def prefixEnd_2689774 : Nat := 4983230072969 + 3 ^ 40 * 2689774 * 2
def baseEnd_2689774 : Nat := 920764609311109653703307

theorem tailTrace_2689774 : CollatzResearch.WordTrace tailWord_2689774 prefixEnd_2689774 920764609311109653703307 := by
  unfold tailWord_2689774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263014669676956208931547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65402744904943766447634917 12263014669676956208931547)
  ·
    refine ⟨18394522004515434313397321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263014669676956208931547 18394522004515434313397321)
    ·
      refine ⟨13795891503386575735047991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18394522004515434313397321 13795891503386575735047991)
      ·
        refine ⟨20693837255079863602571987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13795891503386575735047991 20693837255079863602571987)
        ·
          refine ⟨31040755882619795403857981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20693837255079863602571987 31040755882619795403857981)
          ·
            refine ⟨11640283455982423276446743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31040755882619795403857981 11640283455982423276446743)
            ·
              refine ⟨17460425183973634914670115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640283455982423276446743 17460425183973634914670115)
              ·
                refine ⟨26190637775960452372005173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460425183973634914670115 26190637775960452372005173)
                ·
                  refine ⟨2455372291496292409875485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26190637775960452372005173 2455372291496292409875485)
                  ·
                    refine ⟨920764609311109653703307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455372291496292409875485 920764609311109653703307)
                    ·
                      rfl

theorem cell22_2689774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2689774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689774 prefixEnd_2689774 := by exact prefixLift 2689774
  have htrace : WordTrace (prefixWord ++ tailWord_2689774) baseStart_2689774 baseEnd_2689774 := by
    simpa [prefixWord, tailWord_2689774, baseEnd_2689774] using wordTrace_append hprefix tailTrace_2689774
  have hstable : (prefixWord ++ tailWord_2689774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689774).length < 2 ^ (prefixWord ++ tailWord_2689774).sum := by decide
  have hdescent : baseEnd_2689774 < baseStart_2689774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689802 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_2689802 : Nat := 118140960795 + 2689802 * 2 ^ 59
def prefixEnd_2689802 : Nat := 4983230072969 + 3 ^ 40 * 2689802 * 2
def baseEnd_2689802 : Nat := 920774194283326914003221

theorem tailTrace_2689802 : CollatzResearch.WordTrace tailWord_2689802 prefixEnd_2689802 920774194283326914003221 := by
  unfold tailWord_2689802
  simp only [CollatzResearch.WordTrace]
  refine ⟨24526284650328552613367915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65403425734209473635647773 24526284650328552613367915)
  ·
    refine ⟨36789426975492828920051873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24526284650328552613367915 36789426975492828920051873)
    ·
      refine ⟨27592070231619621690038905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36789426975492828920051873 27592070231619621690038905)
      ·
        refine ⟨20694052673714716267529179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27592070231619621690038905 20694052673714716267529179)
        ·
          refine ⟨31041079010572074401293769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20694052673714716267529179 31041079010572074401293769)
          ·
            refine ⟨23280809257929055800970327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31041079010572074401293769 23280809257929055800970327)
            ·
              refine ⟨34921213886893583701455491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23280809257929055800970327 34921213886893583701455491)
              ·
                refine ⟨52381820830340375552183237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34921213886893583701455491 52381820830340375552183237)
                ·
                  refine ⟨9821591405688820416034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52381820830340375552183237 9821591405688820416034357)
                  ·
                    refine ⟨920774194283326914003221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9821591405688820416034357 920774194283326914003221)
                    ·
                      rfl

theorem cell22_2689802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_2689802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689802 prefixEnd_2689802 := by exact prefixLift 2689802
  have htrace : WordTrace (prefixWord ++ tailWord_2689802) baseStart_2689802 baseEnd_2689802 := by
    simpa [prefixWord, tailWord_2689802, baseEnd_2689802] using wordTrace_append hprefix tailTrace_2689802
  have hstable : (prefixWord ++ tailWord_2689802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689802).length < 2 ^ (prefixWord ++ tailWord_2689802).sum := by decide
  have hdescent : baseEnd_2689802 < baseStart_2689802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689817 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_2689817 : Nat := 118140960795 + 2689817 * 2 ^ 59
def prefixEnd_2689817 : Nat := 4983230072969 + 3 ^ 40 * 2689817 * 2
def baseEnd_2689817 : Nat := 920779329089871874878175

theorem tailTrace_2689817 : CollatzResearch.WordTrace tailWord_2689817 prefixEnd_2689817 920779329089871874878175 := by
  unfold tailWord_2689817
  simp only [CollatzResearch.WordTrace]
  refine ⟨98105685696259868015267705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65403790464173245343511803 98105685696259868015267705)
  ·
    refine ⟨73579264272194901011450779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98105685696259868015267705 73579264272194901011450779)
    ·
      refine ⟨110368896408292351517176169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73579264272194901011450779 110368896408292351517176169)
      ·
        refine ⟨82776672306219263637882127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110368896408292351517176169 82776672306219263637882127)
        ·
          refine ⟨124165008459328895456823191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82776672306219263637882127 124165008459328895456823191)
          ·
            refine ⟨186247512688993343185234787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124165008459328895456823191 186247512688993343185234787)
            ·
              refine ⟨279371269033490014777852181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186247512688993343185234787 279371269033490014777852181)
              ·
                refine ⟨13095528235944844442711821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279371269033490014777852181 13095528235944844442711821)
                ·
                  refine ⟨4910823088479316666016933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13095528235944844442711821 4910823088479316666016933)
                  ·
                    refine ⟨920779329089871874878175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910823088479316666016933 920779329089871874878175)
                    ·
                      rfl

theorem cell22_2689817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_2689817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689817 prefixEnd_2689817 := by exact prefixLift 2689817
  have htrace : WordTrace (prefixWord ++ tailWord_2689817) baseStart_2689817 baseEnd_2689817 := by
    simpa [prefixWord, tailWord_2689817, baseEnd_2689817] using wordTrace_append hprefix tailTrace_2689817
  have hstable : (prefixWord ++ tailWord_2689817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689817).length < 2 ^ (prefixWord ++ tailWord_2689817).sum := by decide
  have hdescent : baseEnd_2689817 < baseStart_2689817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689847 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2689847 : Nat := 118140960795 + 2689847 * 2 ^ 59
def prefixEnd_2689847 : Nat := 4983230072969 + 3 ^ 40 * 2689847 * 2
def baseEnd_2689847 : Nat := 920789598702961796628083

theorem tailTrace_2689847 : CollatzResearch.WordTrace tailWord_2689847 prefixEnd_2689847 920789598702961796628083 := by
  unfold tailWord_2689847
  simp only [CollatzResearch.WordTrace]
  refine ⟨98106779886151183138859795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65404519924100788759239863 98106779886151183138859795)
  ·
    refine ⟨147160169829226774708289693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98106779886151183138859795 147160169829226774708289693)
    ·
      refine ⟨55185063685960040515608635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147160169829226774708289693 55185063685960040515608635)
      ·
        refine ⟨82777595528940060773412953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55185063685960040515608635 82777595528940060773412953)
        ·
          refine ⟨62083196646705045580059715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82777595528940060773412953 62083196646705045580059715)
          ·
            refine ⟨93124794970057568370089573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62083196646705045580059715 93124794970057568370089573)
            ·
              refine ⟨17460899056885794069391795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93124794970057568370089573 17460899056885794069391795)
              ·
                refine ⟨26191348585328691104087693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460899056885794069391795 26191348585328691104087693)
                ·
                  refine ⟨9821755719498259164032885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26191348585328691104087693 9821755719498259164032885)
                  ·
                    refine ⟨920789598702961796628083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9821755719498259164032885 920789598702961796628083)
                    ·
                      rfl

theorem cell22_2689847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2689847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689847 prefixEnd_2689847 := by exact prefixLift 2689847
  have htrace : WordTrace (prefixWord ++ tailWord_2689847) baseStart_2689847 baseEnd_2689847 := by
    simpa [prefixWord, tailWord_2689847, baseEnd_2689847] using wordTrace_append hprefix tailTrace_2689847
  have hstable : (prefixWord ++ tailWord_2689847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689847).length < 2 ^ (prefixWord ++ tailWord_2689847).sum := by decide
  have hdescent : baseEnd_2689847 < baseStart_2689847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689864 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_2689864 : Nat := 118140960795 + 2689864 * 2 ^ 59
def prefixEnd_2689864 : Nat := 4983230072969 + 3 ^ 40 * 2689864 * 2
def baseEnd_2689864 : Nat := 920795418150379418953031

theorem tailTrace_2689864 : CollatzResearch.WordTrace tailWord_2689864 prefixEnd_2689864 920795418150379418953031 := by
  unfold tailWord_2689864
  simp only [CollatzResearch.WordTrace]
  refine ⟨49053699963544797521114323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65404933284726396694819097 49053699963544797521114323)
  ·
    refine ⟨73580549945317196281671485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49053699963544797521114323 73580549945317196281671485)
    ·
      refine ⟨27592706229493948605626807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73580549945317196281671485 27592706229493948605626807)
      ·
        refine ⟨41389059344240922908440211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27592706229493948605626807 41389059344240922908440211)
        ·
          refine ⟨62083589016361384362660317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41389059344240922908440211 62083589016361384362660317)
          ·
            refine ⟨23281345881135519135997619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62083589016361384362660317 23281345881135519135997619)
            ·
              refine ⟨34922018821703278703996429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23281345881135519135997619 34922018821703278703996429)
              ·
                refine ⟨13095757058138729513998661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34922018821703278703996429 13095757058138729513998661)
                ·
                  refine ⟨2455454448401011783874749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13095757058138729513998661 2455454448401011783874749)
                  ·
                    refine ⟨920795418150379418953031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455454448401011783874749 920795418150379418953031)
                    ·
                      rfl

theorem cell22_2689864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_2689864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689864 prefixEnd_2689864 := by exact prefixLift 2689864
  have htrace : WordTrace (prefixWord ++ tailWord_2689864) baseStart_2689864 baseEnd_2689864 := by
    simpa [prefixWord, tailWord_2689864, baseEnd_2689864] using wordTrace_append hprefix tailTrace_2689864
  have hstable : (prefixWord ++ tailWord_2689864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689864).length < 2 ^ (prefixWord ++ tailWord_2689864).sum := by decide
  have hdescent : baseEnd_2689864 < baseStart_2689864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689881 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_2689881 : Nat := 118140960795 + 2689881 * 2 ^ 59
def prefixEnd_2689881 : Nat := 4983230072969 + 3 ^ 40 * 2689881 * 2
def baseEnd_2689881 : Nat := 920801237597797041277979

theorem tailTrace_2689881 : CollatzResearch.WordTrace tailWord_2689881 prefixEnd_2689881 920801237597797041277979 := by
  unfold tailWord_2689881
  simp only [CollatzResearch.WordTrace]
  refine ⟨98108019968028006945597497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65405346645352004630398331 98108019968028006945597497)
  ·
    refine ⟨73581014976021005209198123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98108019968028006945597497 73581014976021005209198123)
    ·
      refine ⟨110371522464031507813797185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73581014976021005209198123 110371522464031507813797185)
      ·
        refine ⟨82778641848023630860347889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110371522464031507813797185 82778641848023630860347889)
        ·
          refine ⟨62083981386017723145260917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82778641848023630860347889 62083981386017723145260917)
          ·
            refine ⟨5820373254939161544868211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62083981386017723145260917 5820373254939161544868211)
            ·
              refine ⟨8730559882408742317302317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5820373254939161544868211 8730559882408742317302317)
              ·
                refine ⟨3273959955903278368988369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8730559882408742317302317 3273959955903278368988369)
                ·
                  refine ⟨2455469966927458776741277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273959955903278368988369 2455469966927458776741277)
                  ·
                    refine ⟨920801237597797041277979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455469966927458776741277 920801237597797041277979)
                    ·
                      rfl

theorem cell22_2689881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_2689881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689881 prefixEnd_2689881 := by exact prefixLift 2689881
  have htrace : WordTrace (prefixWord ++ tailWord_2689881) baseStart_2689881 baseEnd_2689881 := by
    simpa [prefixWord, tailWord_2689881, baseEnd_2689881] using wordTrace_append hprefix tailTrace_2689881
  have hstable : (prefixWord ++ tailWord_2689881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689881).length < 2 ^ (prefixWord ++ tailWord_2689881).sum := by decide
  have hdescent : baseEnd_2689881 < baseStart_2689881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689896 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2689896 : Nat := 118140960795 + 2689896 * 2 ^ 59
def prefixEnd_2689896 : Nat := 4983230072969 + 3 ^ 40 * 2689896 * 2
def baseEnd_2689896 : Nat := 920806372404342002152933

theorem tailTrace_2689896 : CollatzResearch.WordTrace tailWord_2689896 prefixEnd_2689896 920806372404342002152933 := by
  unfold tailWord_2689896
  simp only [CollatzResearch.WordTrace]
  refine ⟨49054283531486832253696771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65405711375315776338262361 49054283531486832253696771)
  ·
    refine ⟨73581425297230248380545157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49054283531486832253696771 73581425297230248380545157)
    ·
      refine ⟨13796517243230671571352217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73581425297230248380545157 13796517243230671571352217)
      ·
        refine ⟨10347387932423003678514163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13796517243230671571352217 10347387932423003678514163)
        ·
          refine ⟨15521081898634505517771245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10347387932423003678514163 15521081898634505517771245)
          ·
            refine ⟨5820405711987939569164217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15521081898634505517771245 5820405711987939569164217)
            ·
              refine ⟨4365304283990954676873163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5820405711987939569164217 4365304283990954676873163)
              ·
                refine ⟨6547956425986432015309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365304283990954676873163 6547956425986432015309745)
                ·
                  refine ⟨4910967319489824011482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547956425986432015309745 4910967319489824011482309)
                  ·
                    refine ⟨920806372404342002152933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910967319489824011482309 920806372404342002152933)
                    ·
                      rfl

theorem cell22_2689896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2689896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689896 prefixEnd_2689896 := by exact prefixLift 2689896
  have htrace : WordTrace (prefixWord ++ tailWord_2689896) baseStart_2689896 baseEnd_2689896 := by
    simpa [prefixWord, tailWord_2689896, baseEnd_2689896] using wordTrace_append hprefix tailTrace_2689896
  have hstable : (prefixWord ++ tailWord_2689896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689896).length < 2 ^ (prefixWord ++ tailWord_2689896).sum := by decide
  have hdescent : baseEnd_2689896 < baseStart_2689896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2689984 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_2689984 : Nat := 118140960795 + 2689984 * 2 ^ 59
def prefixEnd_2689984 : Nat := 4983230072969 + 3 ^ 40 * 2689984 * 2
def baseEnd_2689984 : Nat := 306945498867579701984221

theorem tailTrace_2689984 : CollatzResearch.WordTrace tailWord_2689984 prefixEnd_2689984 306945498867579701984221 := by
  unfold tailWord_2689984
  simp only [CollatzResearch.WordTrace]
  refine ⟨49055888343327427768298503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65407851124436570357731337 49055888343327427768298503)
  ·
    refine ⟨73583832514991141652447755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49055888343327427768298503 73583832514991141652447755)
    ·
      refine ⟨110375748772486712478671633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73583832514991141652447755 110375748772486712478671633)
      ·
        refine ⟨82781811579365034359003725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110375748772486712478671633 82781811579365034359003725)
        ·
          refine ⟨31043179342261887884626397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82781811579365034359003725 31043179342261887884626397)
          ·
            refine ⟨11641192253348207956734899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31043179342261887884626397 11641192253348207956734899)
            ·
              refine ⟨17461788380022311935102349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641192253348207956734899 17461788380022311935102349)
              ·
                refine ⟨6548170642508366975663381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17461788380022311935102349 6548170642508366975663381)
                ·
                  refine ⟨306945498867579701984221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6548170642508366975663381 306945498867579701984221)
                  ·
                    rfl

theorem cell22_2689984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_2689984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2689984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2689984 prefixEnd_2689984 := by exact prefixLift 2689984
  have htrace : WordTrace (prefixWord ++ tailWord_2689984) baseStart_2689984 baseEnd_2689984 := by
    simpa [prefixWord, tailWord_2689984, baseEnd_2689984] using wordTrace_append hprefix tailTrace_2689984
  have hstable : (prefixWord ++ tailWord_2689984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2689984).length < 2 ^ (prefixWord ++ tailWord_2689984).sum := by decide
  have hdescent : baseEnd_2689984 < baseStart_2689984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2689984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690031 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_2690031 : Nat := 118140960795 + 2690031 * 2 ^ 59
def prefixEnd_2690031 : Nat := 4983230072969 + 3 ^ 40 * 2690031 * 2
def baseEnd_2690031 : Nat := 920852585663246650027519

theorem tailTrace_2690031 : CollatzResearch.WordTrace tailWord_2690031 prefixEnd_2690031 920852585663246650027519 := by
  unfold tailWord_2690031
  simp only [CollatzResearch.WordTrace]
  refine ⟨98113490917484582563557947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65408993944989721709038631 98113490917484582563557947)
  ·
    refine ⟨147170236376226873845336921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98113490917484582563557947 147170236376226873845336921)
    ·
      refine ⟨110377677282170155384002691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147170236376226873845336921 110377677282170155384002691)
      ·
        refine ⟨165566515923255233076004037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110377677282170155384002691 165566515923255233076004037)
        ·
          refine ⟨31043721735610356201750757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165566515923255233076004037 31043721735610356201750757)
          ·
            refine ⟨5820697825426941787828267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31043721735610356201750757 5820697825426941787828267)
            ·
              refine ⟨8731046738140412681742401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5820697825426941787828267 8731046738140412681742401)
              ·
                refine ⟨6548285053605309511306801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8731046738140412681742401 6548285053605309511306801)
                ·
                  refine ⟨4911213790203982133480101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548285053605309511306801 4911213790203982133480101)
                  ·
                    refine ⟨920852585663246650027519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911213790203982133480101 920852585663246650027519)
                    ·
                      rfl

theorem cell22_2690031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_2690031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690031 prefixEnd_2690031 := by exact prefixLift 2690031
  have htrace : WordTrace (prefixWord ++ tailWord_2690031) baseStart_2690031 baseEnd_2690031 := by
    simpa [prefixWord, tailWord_2690031, baseEnd_2690031] using wordTrace_append hprefix tailTrace_2690031
  have hstable : (prefixWord ++ tailWord_2690031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690031).length < 2 ^ (prefixWord ++ tailWord_2690031).sum := by decide
  have hdescent : baseEnd_2690031 < baseStart_2690031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690091 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 5]
def baseStart_2690091 : Nat := 118140960795 + 2690091 * 2 ^ 59
def prefixEnd_2690091 : Nat := 4983230072969 + 3 ^ 40 * 2690091 * 2
def baseEnd_2690091 : Nat := 306957708296475497842445

theorem tailTrace_2690091 : CollatzResearch.WordTrace tailWord_2690091 prefixEnd_2690091 306957708296475497842445 := by
  unfold tailWord_2690091
  simp only [CollatzResearch.WordTrace]
  refine ⟨98115679297267212810742127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65410452864844808540494751 98115679297267212810742127)
  ·
    refine ⟨147173518945900819216113191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98115679297267212810742127 147173518945900819216113191)
    ·
      refine ⟨220760278418851228824169787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147173518945900819216113191 220760278418851228824169787)
      ·
        refine ⟨331140417628276843236254681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220760278418851228824169787 331140417628276843236254681)
        ·
          refine ⟨248355313221207632427191011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331140417628276843236254681 248355313221207632427191011)
          ·
            refine ⟨372532969831811448640786517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248355313221207632427191011 372532969831811448640786517)
            ·
              refine ⟨4365620740216540413759217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 372532969831811448640786517 4365620740216540413759217)
              ·
                refine ⟨3274215555162405310319413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365620740216540413759217 3274215555162405310319413)
                ·
                  refine ⟨306957708296475497842445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274215555162405310319413 306957708296475497842445)
                  ·
                    rfl

theorem cell22_2690091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].length) (baseStart_2690091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690091 prefixEnd_2690091 := by exact prefixLift 2690091
  have htrace : WordTrace (prefixWord ++ tailWord_2690091) baseStart_2690091 baseEnd_2690091 := by
    simpa [prefixWord, tailWord_2690091, baseEnd_2690091] using wordTrace_append hprefix tailTrace_2690091
  have hstable : (prefixWord ++ tailWord_2690091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690091).length < 2 ^ (prefixWord ++ tailWord_2690091).sum := by decide
  have hdescent : baseEnd_2690091 < baseStart_2690091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690142 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2690142 : Nat := 118140960795 + 2690142 * 2 ^ 59
def prefixEnd_2690142 : Nat := 4983230072969 + 3 ^ 40 * 2690142 * 2
def baseEnd_2690142 : Nat := 306963527743893120167393

theorem tailTrace_2690142 : CollatzResearch.WordTrace tailWord_2690142 prefixEnd_2690142 306963527743893120167393 := by
  unfold tailWord_2690142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12264692427510306065106085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65411692946721632347232453 12264692427510306065106085)
  ·
    refine ⟨2299629830158182387207391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12264692427510306065106085 2299629830158182387207391)
    ·
      refine ⟨3449444745237273580811087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299629830158182387207391 3449444745237273580811087)
      ·
        refine ⟨5174167117855910371216631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449444745237273580811087 5174167117855910371216631)
        ·
          refine ⟨7761250676783865556824947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174167117855910371216631 7761250676783865556824947)
          ·
            refine ⟨11641876015175798335237421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761250676783865556824947 11641876015175798335237421)
            ·
              refine ⟨4365703505690924375714033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11641876015175798335237421 4365703505690924375714033)
              ·
                refine ⟨3274277629268193281785525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365703505690924375714033 3274277629268193281785525)
                ·
                  refine ⟨306963527743893120167393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274277629268193281785525 306963527743893120167393)
                  ·
                    rfl

theorem cell22_2690142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2690142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690142 prefixEnd_2690142 := by exact prefixLift 2690142
  have htrace : WordTrace (prefixWord ++ tailWord_2690142) baseStart_2690142 baseEnd_2690142 := by
    simpa [prefixWord, tailWord_2690142, baseEnd_2690142] using wordTrace_append hprefix tailTrace_2690142
  have hstable : (prefixWord ++ tailWord_2690142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690142).length < 2 ^ (prefixWord ++ tailWord_2690142).sum := by decide
  have hdescent : baseEnd_2690142 < baseStart_2690142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690153 : List Nat := [1, 2, 1, 1, 1, 6, 2, 4, 4]
def baseStart_2690153 : Nat := 118140960795 + 2690153 * 2 ^ 59
def prefixEnd_2690153 : Nat := 4983230072969 + 3 ^ 40 * 2690153 * 2
def baseEnd_2690153 : Nat := 306964782918826332825715

theorem tailTrace_2690153 : CollatzResearch.WordTrace tailWord_2690153 prefixEnd_2690153 306964782918826332825715 := by
  unfold tailWord_2690153
  simp only [CollatzResearch.WordTrace]
  refine ⟨98117940623042597399499113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65411960415361731599666075 98117940623042597399499113)
  ·
    refine ⟨73588455467281948049624335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98117940623042597399499113 73588455467281948049624335)
    ·
      refine ⟨110382683200922922074436503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73588455467281948049624335 110382683200922922074436503)
      ·
        refine ⟨165574024801384383111654755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110382683200922922074436503 165574024801384383111654755)
        ·
          refine ⟨248361037202076574667482133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165574024801384383111654755 248361037202076574667482133)
          ·
            refine ⟨11641923618847339437538225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248361037202076574667482133 11641923618847339437538225)
            ·
              refine ⟨8731442714135504578153669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11641923618847339437538225 8731442714135504578153669)
              ·
                refine ⟨1637145508900407108403813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8731442714135504578153669 1637145508900407108403813)
                ·
                  refine ⟨306964782918826332825715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637145508900407108403813 306964782918826332825715)
                  ·
                    rfl

theorem cell22_2690153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_2690153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690153 prefixEnd_2690153 := by exact prefixLift 2690153
  have htrace : WordTrace (prefixWord ++ tailWord_2690153) baseStart_2690153 baseEnd_2690153 := by
    simpa [prefixWord, tailWord_2690153, baseEnd_2690153] using wordTrace_append hprefix tailTrace_2690153
  have hstable : (prefixWord ++ tailWord_2690153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690153).length < 2 ^ (prefixWord ++ tailWord_2690153).sum := by decide
  have hdescent : baseEnd_2690153 < baseStart_2690153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690168 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_2690168 : Nat := 118140960795 + 2690168 * 2 ^ 59
def prefixEnd_2690168 : Nat := 4983230072969 + 3 ^ 40 * 2690168 * 2
def baseEnd_2690168 : Nat := 920899483563023959352099

theorem tailTrace_2690168 : CollatzResearch.WordTrace tailWord_2690168 prefixEnd_2690168 920899483563023959352099 := by
  unfold tailWord_2690168
  simp only [CollatzResearch.WordTrace]
  refine ⟨49059243858994127480647579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65412325145325503307530105 49059243858994127480647579)
  ·
    refine ⟨73588865788491191220971369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49059243858994127480647579 73588865788491191220971369)
    ·
      refine ⟨55191649341368393415728527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73588865788491191220971369 55191649341368393415728527)
      ·
        refine ⟨82787474012052590123592791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55191649341368393415728527 82787474012052590123592791)
        ·
          refine ⟨124181211018078885185389187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82787474012052590123592791 124181211018078885185389187)
          ·
            refine ⟨186271816527118327778083781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124181211018078885185389187 186271816527118327778083781)
            ·
              refine ⟨34925965598834686458390709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186271816527118327778083781 34925965598834686458390709)
              ·
                refine ⟨3274309274890751855474129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34925965598834686458390709 3274309274890751855474129)
                ·
                  refine ⟨2455731956168063891605597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3274309274890751855474129 2455731956168063891605597)
                  ·
                    refine ⟨920899483563023959352099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455731956168063891605597 920899483563023959352099)
                    ·
                      rfl

theorem cell22_2690168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_2690168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690168 prefixEnd_2690168 := by exact prefixLift 2690168
  have htrace : WordTrace (prefixWord ++ tailWord_2690168) baseStart_2690168 baseEnd_2690168 := by
    simpa [prefixWord, tailWord_2690168, baseEnd_2690168] using wordTrace_append hprefix tailTrace_2690168
  have hstable : (prefixWord ++ tailWord_2690168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690168).length < 2 ^ (prefixWord ++ tailWord_2690168).sum := by decide
  have hdescent : baseEnd_2690168 < baseStart_2690168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690258 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2690258 : Nat := 118140960795 + 2690258 * 2 ^ 59
def prefixEnd_2690258 : Nat := 4983230072969 + 3 ^ 40 * 2690258 * 2
def baseEnd_2690258 : Nat := 920930292402293724601823

theorem tailTrace_2690258 : CollatzResearch.WordTrace tailWord_2690258 prefixEnd_2690258 920930292402293724601823 := by
  unfold tailWord_2690258
  simp only [CollatzResearch.WordTrace]
  refine ⟨24530442571915550083017857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65414513525108133554714285 24530442571915550083017857)
  ·
    refine ⟨18397831928936662562263393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24530442571915550083017857 18397831928936662562263393)
    ·
      refine ⟨13798373946702496921697545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18397831928936662562263393 13798373946702496921697545)
      ·
        refine ⟨10348780460026872691273159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13798373946702496921697545 10348780460026872691273159)
        ·
          refine ⟨15523170690040309036909739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10348780460026872691273159 15523170690040309036909739)
          ·
            refine ⟨23284756035060463555364609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15523170690040309036909739 23284756035060463555364609)
            ·
              refine ⟨17463567026295347666523457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23284756035060463555364609 17463567026295347666523457)
              ·
                refine ⟨13097675269721510749892593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17463567026295347666523457 13097675269721510749892593)
                ·
                  refine ⟨9823256452291133062419445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13097675269721510749892593 9823256452291133062419445)
                  ·
                    refine ⟨920930292402293724601823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9823256452291133062419445 920930292402293724601823)
                    ·
                      rfl

theorem cell22_2690258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2690258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690258 prefixEnd_2690258 := by exact prefixLift 2690258
  have htrace : WordTrace (prefixWord ++ tailWord_2690258) baseStart_2690258 baseEnd_2690258 := by
    simpa [prefixWord, tailWord_2690258, baseEnd_2690258] using wordTrace_append hprefix tailTrace_2690258
  have hstable : (prefixWord ++ tailWord_2690258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690258).length < 2 ^ (prefixWord ++ tailWord_2690258).sum := by decide
  have hdescent : baseEnd_2690258 < baseStart_2690258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690273 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2690273 : Nat := 118140960795 + 2690273 * 2 ^ 59
def prefixEnd_2690273 : Nat := 4983230072969 + 3 ^ 40 * 2690273 * 2
def baseEnd_2690273 : Nat := 920935427208838685476777

theorem tailTrace_2690273 : CollatzResearch.WordTrace tailWord_2690273 prefixEnd_2690273 920935427208838685476777 := by
  unfold tailWord_2690273
  simp only [CollatzResearch.WordTrace]
  refine ⟨98122317382607857893867473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65414878255071905262578315 98122317382607857893867473)
  ·
    refine ⟨73591738036955893420400605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98122317382607857893867473 73591738036955893420400605)
    ·
      refine ⟨27596901763858460032650227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73591738036955893420400605 27596901763858460032650227)
      ·
        refine ⟨41395352645787690048975341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27596901763858460032650227 41395352645787690048975341)
        ·
          refine ⟨15523257242170383768365753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41395352645787690048975341 15523257242170383768365753)
          ·
            refine ⟨11642442931627787826274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15523257242170383768365753 11642442931627787826274315)
            ·
              refine ⟨17463664397441681739411473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11642442931627787826274315 17463664397441681739411473)
              ·
                refine ⟨13097748298081261304558605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17463664397441681739411473 13097748298081261304558605)
                ·
                  refine ⟨4911655611780472989209477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13097748298081261304558605 4911655611780472989209477)
                  ·
                    refine ⟨920935427208838685476777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911655611780472989209477 920935427208838685476777)
                    ·
                      rfl

theorem cell22_2690273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2690273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690273 prefixEnd_2690273 := by exact prefixLift 2690273
  have htrace : WordTrace (prefixWord ++ tailWord_2690273) baseStart_2690273 baseEnd_2690273 := by
    simpa [prefixWord, tailWord_2690273, baseEnd_2690273] using wordTrace_append hprefix tailTrace_2690273
  have hstable : (prefixWord ++ tailWord_2690273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690273).length < 2 ^ (prefixWord ++ tailWord_2690273).sum := by decide
  have hdescent : baseEnd_2690273 < baseStart_2690273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690303 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2690303 : Nat := 118140960795 + 2690303 * 2 ^ 59
def prefixEnd_2690303 : Nat := 4983230072969 + 3 ^ 40 * 2690303 * 2
def baseEnd_2690303 : Nat := 920945696821928607226685

theorem tailTrace_2690303 : CollatzResearch.WordTrace tailWord_2690303 prefixEnd_2690303 920945696821928607226685 := by
  unfold tailWord_2690303
  simp only [CollatzResearch.WordTrace]
  refine ⟨98123411572499173017459563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65415607714999448678306375 98123411572499173017459563)
  ·
    refine ⟨147185117358748759526189345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98123411572499173017459563 147185117358748759526189345)
    ·
      refine ⟨110388838019061569644642009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147185117358748759526189345 110388838019061569644642009)
      ·
        refine ⟨82791628514296177233481507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110388838019061569644642009 82791628514296177233481507)
        ·
          refine ⟨124187442771444265850222261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82791628514296177233481507 124187442771444265850222261)
          ·
            refine ⟨11642572759822899923458337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124187442771444265850222261 11642572759822899923458337)
            ·
              refine ⟨8731929569867174942593753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11642572759822899923458337 8731929569867174942593753)
              ·
                refine ⟨6548947177400381206945315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8731929569867174942593753 6548947177400381206945315)
                ·
                  refine ⟨9823420766100571810417973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6548947177400381206945315 9823420766100571810417973)
                  ·
                    refine ⟨920945696821928607226685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9823420766100571810417973 920945696821928607226685)
                    ·
                      rfl

theorem cell22_2690303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2690303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690303 prefixEnd_2690303 := by exact prefixLift 2690303
  have htrace : WordTrace (prefixWord ++ tailWord_2690303) baseStart_2690303 baseEnd_2690303 := by
    simpa [prefixWord, tailWord_2690303, baseEnd_2690303] using wordTrace_append hprefix tailTrace_2690303
  have hstable : (prefixWord ++ tailWord_2690303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690303).length < 2 ^ (prefixWord ++ tailWord_2690303).sum := by decide
  have hdescent : baseEnd_2690303 < baseStart_2690303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690305 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 4]
def baseStart_2690305 : Nat := 118140960795 + 2690305 * 2 ^ 59
def prefixEnd_2690305 : Nat := 4983230072969 + 3 ^ 40 * 2690305 * 2
def baseEnd_2690305 : Nat := 306982127154267089558893

theorem tailTrace_2690305 : CollatzResearch.WordTrace tailWord_2690305 prefixEnd_2690305 306982127154267089558893 := by
  unfold tailWord_2690305
  simp only [CollatzResearch.WordTrace]
  refine ⟨98123484518491927359032369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65415656345661284906021579 98123484518491927359032369)
  ·
    refine ⟨73592613388868945519274277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98123484518491927359032369 73592613388868945519274277)
    ·
      refine ⟨13798615010412927284863927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73592613388868945519274277 13798615010412927284863927)
      ·
        refine ⟨20697922515619390927295891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798615010412927284863927 20697922515619390927295891)
        ·
          refine ⟨31046883773429086390943837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697922515619390927295891 31046883773429086390943837)
          ·
            refine ⟨11642581415035907396603939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31046883773429086390943837 11642581415035907396603939)
            ·
              refine ⟨17463872122553861094905909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11642581415035907396603939 17463872122553861094905909)
              ·
                refine ⟨1637238011489424477647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17463872122553861094905909 1637238011489424477647429)
                ·
                  refine ⟨306982127154267089558893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637238011489424477647429 306982127154267089558893)
                  ·
                    rfl

theorem cell22_2690305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_2690305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690305 prefixEnd_2690305 := by exact prefixLift 2690305
  have htrace : WordTrace (prefixWord ++ tailWord_2690305) baseStart_2690305 baseEnd_2690305 := by
    simpa [prefixWord, tailWord_2690305, baseEnd_2690305] using wordTrace_append hprefix tailTrace_2690305
  have hstable : (prefixWord ++ tailWord_2690305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690305).length < 2 ^ (prefixWord ++ tailWord_2690305).sum := by decide
  have hdescent : baseEnd_2690305 < baseStart_2690305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690307 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 1, 4]
def baseStart_2690307 : Nat := 118140960795 + 2690307 * 2 ^ 59
def prefixEnd_2690307 : Nat := 4983230072969 + 3 ^ 40 * 2690307 * 2
def baseEnd_2690307 : Nat := 920947066103673930126673

theorem tailTrace_2690307 : CollatzResearch.WordTrace tailWord_2690307 prefixEnd_2690307 920947066103673930126673 := by
  unfold tailWord_2690307
  simp only [CollatzResearch.WordTrace]
  refine ⟨98123557464484681700605175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65415704976323121133736783 98123557464484681700605175)
  ·
    refine ⟨147185336196727022550907763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98123557464484681700605175 147185336196727022550907763)
    ·
      refine ⟨220778004295090533826361645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147185336196727022550907763 220778004295090533826361645)
      ·
        refine ⟨82791751610658950184885617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220778004295090533826361645 82791751610658950184885617)
        ·
          refine ⟨62093813707994212638664213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82791751610658950184885617 62093813707994212638664213)
          ·
            refine ⟨2910647517562228717437385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62093813707994212638664213 2910647517562228717437385)
            ·
              refine ⟨2182985638171671538078039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910647517562228717437385 2182985638171671538078039)
              ·
                refine ⟨3274478457257507307117059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182985638171671538078039 3274478457257507307117059)
                ·
                  refine ⟨4911717685886260960675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274478457257507307117059 4911717685886260960675589)
                  ·
                    refine ⟨920947066103673930126673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911717685886260960675589 920947066103673930126673)
                    ·
                      rfl

theorem cell22_2690307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 4].length) (baseStart_2690307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690307 prefixEnd_2690307 := by exact prefixLift 2690307
  have htrace : WordTrace (prefixWord ++ tailWord_2690307) baseStart_2690307 baseEnd_2690307 := by
    simpa [prefixWord, tailWord_2690307, baseEnd_2690307] using wordTrace_append hprefix tailTrace_2690307
  have hstable : (prefixWord ++ tailWord_2690307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690307).length < 2 ^ (prefixWord ++ tailWord_2690307).sum := by decide
  have hdescent : baseEnd_2690307 < baseStart_2690307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690393 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_2690393 : Nat := 118140960795 + 2690393 * 2 ^ 59
def prefixEnd_2690393 : Nat := 4983230072969 + 3 ^ 40 * 2690393 * 2
def baseEnd_2690393 : Nat := 920976505661198372476409

theorem tailTrace_2690393 : CollatzResearch.WordTrace tailWord_2690393 prefixEnd_2690393 920976505661198372476409 := by
  unfold tailWord_2690393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98126694142173118388235833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65417796094782078925490555 98126694142173118388235833)
  ·
    refine ⟨73595020606629838791176875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98126694142173118388235833 73595020606629838791176875)
    ·
      refine ⟨110392530909944758186765313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73595020606629838791176875 110392530909944758186765313)
      ·
        refine ⟨82794398182458568640073985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110392530909944758186765313 82794398182458568640073985)
        ·
          refine ⟨62095798636843926480055489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82794398182458568640073985 62095798636843926480055489)
          ·
            refine ⟨46571848977632944860041617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62095798636843926480055489 46571848977632944860041617)
            ·
              refine ⟨34928886733224708645031213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46571848977632944860041617 34928886733224708645031213)
              ·
                refine ⟨13098332524959265741886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34928886733224708645031213 13098332524959265741886705)
                ·
                  refine ⟨9823749393719449306415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098332524959265741886705 9823749393719449306415029)
                  ·
                    refine ⟨920976505661198372476409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9823749393719449306415029 920976505661198372476409)
                    ·
                      rfl

theorem cell22_2690393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_2690393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690393 prefixEnd_2690393 := by exact prefixLift 2690393
  have htrace : WordTrace (prefixWord ++ tailWord_2690393) baseStart_2690393 baseEnd_2690393 := by
    simpa [prefixWord, tailWord_2690393, baseEnd_2690393] using wordTrace_append hprefix tailTrace_2690393
  have hstable : (prefixWord ++ tailWord_2690393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690393).length < 2 ^ (prefixWord ++ tailWord_2690393).sum := by decide
  have hdescent : baseEnd_2690393 < baseStart_2690393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690425 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_2690425 : Nat := 118140960795 + 2690425 * 2 ^ 59
def prefixEnd_2690425 : Nat := 4983230072969 + 3 ^ 40 * 2690425 * 2
def baseEnd_2690425 : Nat := 920987459915160955676311

theorem tailTrace_2690425 : CollatzResearch.WordTrace tailWord_2690425 prefixEnd_2690425 920987459915160955676311 := by
  unfold tailWord_2690425
  simp only [CollatzResearch.WordTrace]
  refine ⟨98127861278057187853400729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65418574185371458568933819 98127861278057187853400729)
  ·
    refine ⟨73595895958542890890050547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98127861278057187853400729 73595895958542890890050547)
    ·
      refine ⟨110393843937814336335075821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73595895958542890890050547 110393843937814336335075821)
      ·
        refine ⟨41397691476680376125653433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110393843937814336335075821 41397691476680376125653433)
        ·
          refine ⟨31048268607510282094240075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41397691476680376125653433 31048268607510282094240075)
          ·
            refine ⟨46572402911265423141360113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31048268607510282094240075 46572402911265423141360113)
            ·
              refine ⟨34929302183449067356020085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46572402911265423141360113 34929302183449067356020085)
              ·
                refine ⟨3274622079698350064626883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34929302183449067356020085 3274622079698350064626883)
                ·
                  refine ⟨4911933119547525096940325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274622079698350064626883 4911933119547525096940325)
                  ·
                    refine ⟨920987459915160955676311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911933119547525096940325 920987459915160955676311)
                    ·
                      rfl

theorem cell22_2690425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_2690425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690425 prefixEnd_2690425 := by exact prefixLift 2690425
  have htrace : WordTrace (prefixWord ++ tailWord_2690425) baseStart_2690425 baseEnd_2690425 := by
    simpa [prefixWord, tailWord_2690425, baseEnd_2690425] using wordTrace_append hprefix tailTrace_2690425
  have hstable : (prefixWord ++ tailWord_2690425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690425).length < 2 ^ (prefixWord ++ tailWord_2690425).sum := by decide
  have hdescent : baseEnd_2690425 < baseStart_2690425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690433 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2690433 : Nat := 118140960795 + 2690433 * 2 ^ 59
def prefixEnd_2690433 : Nat := 4983230072969 + 3 ^ 40 * 2690433 * 2
def baseEnd_2690433 : Nat := 920990198478651601476287

theorem tailTrace_2690433 : CollatzResearch.WordTrace tailWord_2690433 prefixEnd_2690433 920990198478651601476287 := by
  unfold tailWord_2690433
  simp only [CollatzResearch.WordTrace]
  refine ⟨98128153062028205219691953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65418768708018803479794635 98128153062028205219691953)
  ·
    refine ⟨73596114796521153914768965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98128153062028205219691953 73596114796521153914768965)
    ·
      refine ⟨13799271524347716359019181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73596114796521153914768965 13799271524347716359019181)
      ·
        refine ⟨5174726821630393634632193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13799271524347716359019181 5174726821630393634632193)
        ·
          refine ⟨3881045116222795225974145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174726821630393634632193 3881045116222795225974145)
          ·
            refine ⟨2910783837167096419480609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3881045116222795225974145 2910783837167096419480609)
            ·
              refine ⟨2183087877875322314610457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2910783837167096419480609 2183087877875322314610457)
              ·
                refine ⟨1637315908406491735957843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183087877875322314610457 1637315908406491735957843)
                ·
                  refine ⟨2455973862609737603936765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1637315908406491735957843 2455973862609737603936765)
                  ·
                    refine ⟨920990198478651601476287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455973862609737603936765 920990198478651601476287)
                    ·
                      rfl

theorem cell22_2690433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2690433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690433 prefixEnd_2690433 := by exact prefixLift 2690433
  have htrace : WordTrace (prefixWord ++ tailWord_2690433) baseStart_2690433 baseEnd_2690433 := by
    simpa [prefixWord, tailWord_2690433, baseEnd_2690433] using wordTrace_append hprefix tailTrace_2690433
  have hstable : (prefixWord ++ tailWord_2690433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690433).length < 2 ^ (prefixWord ++ tailWord_2690433).sum := by decide
  have hdescent : baseEnd_2690433 < baseStart_2690433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690455 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 6, 3]
def baseStart_2690455 : Nat := 118140960795 + 2690455 * 2 ^ 59
def prefixEnd_2690455 : Nat := 4983230072969 + 3 ^ 40 * 2690455 * 2
def baseEnd_2690455 : Nat := 920997729528250877426219

theorem tailTrace_2690455 : CollatzResearch.WordTrace tailWord_2690455 prefixEnd_2690455 920997729528250877426219 := by
  unfold tailWord_2690455
  simp only [CollatzResearch.WordTrace]
  refine ⟨98128955467948502976992819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65419303645299001984661879 98128955467948502976992819)
  ·
    refine ⟨147193433201922754465489229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98128955467948502976992819 147193433201922754465489229)
    ·
      refine ⟨55197537450721032924558461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147193433201922754465489229 55197537450721032924558461)
      ·
        refine ⟨20699076544020387346709423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55197537450721032924558461 20699076544020387346709423)
        ·
          refine ⟨31048614816030581020064135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20699076544020387346709423 31048614816030581020064135)
          ·
            refine ⟨46572922224045871530096203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31048614816030581020064135 46572922224045871530096203)
            ·
              refine ⟨69859383336068807295144305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46572922224045871530096203 69859383336068807295144305)
              ·
                refine ⟨52394537502051605471358229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69859383336068807295144305 52394537502051605471358229)
                ·
                  refine ⟨2455993945408669006469917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52394537502051605471358229 2455993945408669006469917)
                  ·
                    refine ⟨920997729528250877426219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2455993945408669006469917 920997729528250877426219)
                    ·
                      rfl

theorem cell22_2690455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_2690455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690455 prefixEnd_2690455 := by exact prefixLift 2690455
  have htrace : WordTrace (prefixWord ++ tailWord_2690455) baseStart_2690455 baseEnd_2690455 := by
    simpa [prefixWord, tailWord_2690455, baseEnd_2690455] using wordTrace_append hprefix tailTrace_2690455
  have hstable : (prefixWord ++ tailWord_2690455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690455).length < 2 ^ (prefixWord ++ tailWord_2690455).sum := by decide
  have hdescent : baseEnd_2690455 < baseStart_2690455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 9]
def baseStart_2690483 : Nat := 118140960795 + 2690483 * 2 ^ 59
def prefixEnd_2690483 : Nat := 4983230072969 + 3 ^ 40 * 2690483 * 2
def baseEnd_2690483 : Nat := 921007314500468137726133

theorem tailTrace_2690483 : CollatzResearch.WordTrace tailWord_2690483 prefixEnd_2690483 921007314500468137726133 := by
  unfold tailWord_2690483
  simp only [CollatzResearch.WordTrace]
  refine ⟨98129976711847063759012103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65419984474564709172674735 98129976711847063759012103)
  ·
    refine ⟨147194965067770595638518155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98129976711847063759012103 147194965067770595638518155)
    ·
      refine ⟨220792447601655893457777233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147194965067770595638518155 220792447601655893457777233)
      ·
        refine ⟨165594335701241920093332925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220792447601655893457777233 165594335701241920093332925)
        ·
          refine ⟨62097875887965720034999847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165594335701241920093332925 62097875887965720034999847)
          ·
            refine ⟨93146813831948580052499771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62097875887965720034999847 93146813831948580052499771)
            ·
              refine ⟨139720220747922870078749657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93146813831948580052499771 139720220747922870078749657)
              ·
                refine ⟨104790165560942152559062243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139720220747922870078749657 104790165560942152559062243)
                ·
                  refine ⟨157185248341413228838593365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104790165560942152559062243 157185248341413228838593365)
                  ·
                    refine ⟨921007314500468137726133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157185248341413228838593365 921007314500468137726133)
                    ·
                      rfl

theorem cell22_2690483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_2690483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690483 prefixEnd_2690483 := by exact prefixLift 2690483
  have htrace : WordTrace (prefixWord ++ tailWord_2690483) baseStart_2690483 baseEnd_2690483 := by
    simpa [prefixWord, tailWord_2690483, baseEnd_2690483] using wordTrace_append hprefix tailTrace_2690483
  have hstable : (prefixWord ++ tailWord_2690483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690483).length < 2 ^ (prefixWord ++ tailWord_2690483).sum := by decide
  have hdescent : baseEnd_2690483 < baseStart_2690483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690485 : List Nat := [1, 3, 3, 2, 2, 2, 9]
def baseStart_2690485 : Nat := 118140960795 + 2690485 * 2 ^ 59
def prefixEnd_2690485 : Nat := 4983230072969 + 3 ^ 40 * 2690485 * 2
def baseEnd_2690485 : Nat := 34111407375605214784301

theorem tailTrace_2690485 : CollatzResearch.WordTrace tailWord_2690485 prefixEnd_2690485 34111407375605214784301 := by
  unfold tailWord_2690485
  simp only [CollatzResearch.WordTrace]
  refine ⟨98130049657839818100584909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65420033105226545400389939 98130049657839818100584909)
  ·
    refine ⟨36798768621689931787719341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98130049657839818100584909 36798768621689931787719341)
    ·
      refine ⟨13799538233133724420394753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36798768621689931787719341 13799538233133724420394753)
      ·
        refine ⟨10349653674850293315296065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13799538233133724420394753 10349653674850293315296065)
        ·
          refine ⟨7762240256137719986472049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10349653674850293315296065 7762240256137719986472049)
          ·
            refine ⟨5821680192103289989854037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7762240256137719986472049 5821680192103289989854037)
            ·
              refine ⟨34111407375605214784301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5821680192103289989854037 34111407375605214784301)
              ·
                rfl

theorem cell22_2690485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 9].length) (baseStart_2690485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690485 prefixEnd_2690485 := by exact prefixLift 2690485
  have htrace : WordTrace (prefixWord ++ tailWord_2690485) baseStart_2690485 baseEnd_2690485 := by
    simpa [prefixWord, tailWord_2690485, baseEnd_2690485] using wordTrace_append hprefix tailTrace_2690485
  have hstable : (prefixWord ++ tailWord_2690485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690485).length < 2 ^ (prefixWord ++ tailWord_2690485).sum := by decide
  have hdescent : baseEnd_2690485 < baseStart_2690485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690517 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2690517 : Nat := 118140960795 + 2690517 * 2 ^ 59
def prefixEnd_2690517 : Nat := 4983230072969 + 3 ^ 40 * 2690517 * 2
def baseEnd_2690517 : Nat := 921018953395303382376029

theorem tailTrace_2690517 : CollatzResearch.WordTrace tailWord_2690517 prefixEnd_2690517 921018953395303382376029 := by
  unfold tailWord_2690517
  simp only [CollatzResearch.WordTrace]
  refine ⟨98131216793723887565749805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65420811195815925043833203 98131216793723887565749805)
  ·
    refine ⟨36799206297646457837156177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98131216793723887565749805 36799206297646457837156177)
    ·
      refine ⟨27599404723234843377867133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36799206297646457837156177 27599404723234843377867133)
      ·
        refine ⟨10349776771213066266700175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27599404723234843377867133 10349776771213066266700175)
        ·
          refine ⟨15524665156819599400050263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10349776771213066266700175 15524665156819599400050263)
          ·
            refine ⟨23286997735229399100075395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15524665156819599400050263 23286997735229399100075395)
            ·
              refine ⟨34930496602844098650113093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23286997735229399100075395 34930496602844098650113093)
              ·
                refine ⟨6549468113033268496896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34930496602844098650113093 6549468113033268496896205)
                ·
                  refine ⟨2456050542387475686336077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6549468113033268496896205 2456050542387475686336077)
                  ·
                    refine ⟨921018953395303382376029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456050542387475686336077 921018953395303382376029)
                    ·
                      rfl

theorem cell22_2690517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2690517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690517 prefixEnd_2690517 := by exact prefixLift 2690517
  have htrace : WordTrace (prefixWord ++ tailWord_2690517) baseStart_2690517 baseEnd_2690517 := by
    simpa [prefixWord, tailWord_2690517, baseEnd_2690517] using wordTrace_append hprefix tailTrace_2690517
  have hstable : (prefixWord ++ tailWord_2690517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690517).length < 2 ^ (prefixWord ++ tailWord_2690517).sum := by decide
  have hdescent : baseEnd_2690517 < baseStart_2690517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690564 : List Nat := [2, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2690564 : Nat := 118140960795 + 2690564 * 2 ^ 59
def prefixEnd_2690564 : Nat := 4983230072969 + 3 ^ 40 * 2690564 * 2
def baseEnd_2690564 : Nat := 307011680818603642150295

theorem tailTrace_2690564 : CollatzResearch.WordTrace tailWord_2690564 prefixEnd_2690564 307011680818603642150295 := by
  unfold tailWord_2690564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49066465512276807296355373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65421954016369076395140497 49066465512276807296355373)
  ·
    refine ⟨18399924567103802736133265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49066465512276807296355373 18399924567103802736133265)
    ·
      refine ⟨13799943425327852052099949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18399924567103802736133265 13799943425327852052099949)
      ·
        refine ⟨5174978784497944519537481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13799943425327852052099949 5174978784497944519537481)
        ·
          refine ⟨3881234088373458389653111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5174978784497944519537481 3881234088373458389653111)
          ·
            refine ⟨5821851132560187584479667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881234088373458389653111 5821851132560187584479667)
            ·
              refine ⟨8732776698840281376719501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821851132560187584479667 8732776698840281376719501)
              ·
                refine ⟨3274791262065105516269813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8732776698840281376719501 3274791262065105516269813)
                ·
                  refine ⟨307011680818603642150295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274791262065105516269813 307011680818603642150295)
                  ·
                    rfl

theorem cell22_2690564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2690564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690564 prefixEnd_2690564 := by exact prefixLift 2690564
  have htrace : WordTrace (prefixWord ++ tailWord_2690564) baseStart_2690564 baseEnd_2690564 := by
    simpa [prefixWord, tailWord_2690564, baseEnd_2690564] using wordTrace_append hprefix tailTrace_2690564
  have hstable : (prefixWord ++ tailWord_2690564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690564).length < 2 ^ (prefixWord ++ tailWord_2690564).sum := by decide
  have hdescent : baseEnd_2690564 < baseStart_2690564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690746 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_2690746 : Nat := 118140960795 + 2690746 * 2 ^ 59
def prefixEnd_2690746 : Nat := 4983230072969 + 3 ^ 40 * 2690746 * 2
def baseEnd_2690746 : Nat := 921097344775223118400327

theorem tailTrace_2690746 : CollatzResearch.WordTrace tailWord_2690746 prefixEnd_2690746 921097344775223118400327 := by
  unfold tailWord_2690746
  simp only [CollatzResearch.WordTrace]
  refine ⟨24534892277473564918959023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65426379406596173117224061 24534892277473564918959023)
  ·
    refine ⟨36802338416210347378438535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24534892277473564918959023 36802338416210347378438535)
    ·
      refine ⟨55203507624315521067657803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36802338416210347378438535 55203507624315521067657803)
      ·
        refine ⟨82805261436473281601486705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55203507624315521067657803 82805261436473281601486705)
        ·
          refine ⟨62103946077354961201115029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82805261436473281601486705 62103946077354961201115029)
          ·
            refine ⟨2911122472376013806302267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62103946077354961201115029 2911122472376013806302267)
            ·
              refine ⟨4366683708564020709453401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911122472376013806302267 4366683708564020709453401)
              ·
                refine ⟨3275012781423015532090051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366683708564020709453401 3275012781423015532090051)
                ·
                  refine ⟨4912519172134523298135077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275012781423015532090051 4912519172134523298135077)
                  ·
                    refine ⟨921097344775223118400327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912519172134523298135077 921097344775223118400327)
                    ·
                      rfl

theorem cell22_2690746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_2690746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690746 prefixEnd_2690746 := by exact prefixLift 2690746
  have htrace : WordTrace (prefixWord ++ tailWord_2690746) baseStart_2690746 baseEnd_2690746 := by
    simpa [prefixWord, tailWord_2690746, baseEnd_2690746] using wordTrace_append hprefix tailTrace_2690746
  have hstable : (prefixWord ++ tailWord_2690746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690746).length < 2 ^ (prefixWord ++ tailWord_2690746).sum := by decide
  have hdescent : baseEnd_2690746 < baseStart_2690746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690757 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2690757 : Nat := 118140960795 + 2690757 * 2 ^ 59
def prefixEnd_2690757 : Nat := 4983230072969 + 3 ^ 40 * 2690757 * 2
def baseEnd_2690757 : Nat := 921101110300022756375293

theorem tailTrace_2690757 : CollatzResearch.WordTrace tailWord_2690757 prefixEnd_2690757 921101110300022756375293 := by
  unfold tailWord_2690757
  simp only [CollatzResearch.WordTrace]
  refine ⟨98139970312854408554486525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65426646875236272369657683 98139970312854408554486525)
  ·
    refine ⟨36802488867320403207932447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98139970312854408554486525 36802488867320403207932447)
    ·
      refine ⟨55203733300980604811898671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36802488867320403207932447 55203733300980604811898671)
      ·
        refine ⟨82805599951470907217848007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55203733300980604811898671 82805599951470907217848007)
        ·
          refine ⟨124208399927206360826772011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82805599951470907217848007 124208399927206360826772011)
          ·
            refine ⟨186312599890809541240158017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124208399927206360826772011 186312599890809541240158017)
            ·
              refine ⟨139734449918107155930118513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186312599890809541240158017 139734449918107155930118513)
              ·
                refine ⟨104800837438580366947588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139734449918107155930118513 104800837438580366947588885)
                ·
                  refine ⟨4912539254933454700668229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104800837438580366947588885 4912539254933454700668229)
                  ·
                    refine ⟨921101110300022756375293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912539254933454700668229 921101110300022756375293)
                    ·
                      rfl

theorem cell22_2690757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2690757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690757 prefixEnd_2690757 := by exact prefixLift 2690757
  have htrace : WordTrace (prefixWord ++ tailWord_2690757) baseStart_2690757 baseEnd_2690757 := by
    simpa [prefixWord, tailWord_2690757, baseEnd_2690757] using wordTrace_append hprefix tailTrace_2690757
  have hstable : (prefixWord ++ tailWord_2690757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690757).length < 2 ^ (prefixWord ++ tailWord_2690757).sum := by decide
  have hdescent : baseEnd_2690757 < baseStart_2690757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690776 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 2, 3]
def baseStart_2690776 : Nat := 118140960795 + 2690776 * 2 ^ 59
def prefixEnd_2690776 : Nat := 4983230072969 + 3 ^ 40 * 2690776 * 2
def baseEnd_2690776 : Nat := 921107614388313040150235

theorem tailTrace_2690776 : CollatzResearch.WordTrace tailWord_2690776 prefixEnd_2690776 921107614388313040150235 := by
  unfold tailWord_2690776
  simp only [CollatzResearch.WordTrace]
  refine ⟨49070331649892787399714091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65427108866523716532952121 49070331649892787399714091)
  ·
    refine ⟨73605497474839181099571137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49070331649892787399714091 73605497474839181099571137)
    ·
      refine ⟨55204123106129385824678353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73605497474839181099571137 55204123106129385824678353)
      ·
        refine ⟨41403092329597039368508765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55204123106129385824678353 41403092329597039368508765)
        ·
          refine ⟨15526159623598889763190787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41403092329597039368508765 15526159623598889763190787)
          ·
            refine ⟨23289239435398334644786181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15526159623598889763190787 23289239435398334644786181)
            ·
              refine ⟨4366732394137187745897409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23289239435398334644786181 4366732394137187745897409)
              ·
                refine ⟨3275049295602890809423057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366732394137187745897409 3275049295602890809423057)
                ·
                  refine ⟨2456286971702168107067293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3275049295602890809423057 2456286971702168107067293)
                  ·
                    refine ⟨921107614388313040150235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456286971702168107067293 921107614388313040150235)
                    ·
                      rfl

theorem cell22_2690776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_2690776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690776 prefixEnd_2690776 := by exact prefixLift 2690776
  have htrace : WordTrace (prefixWord ++ tailWord_2690776) baseStart_2690776 baseEnd_2690776 := by
    simpa [prefixWord, tailWord_2690776, baseEnd_2690776] using wordTrace_append hprefix tailTrace_2690776
  have hstable : (prefixWord ++ tailWord_2690776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690776).length < 2 ^ (prefixWord ++ tailWord_2690776).sum := by decide
  have hdescent : baseEnd_2690776 < baseStart_2690776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690778 : List Nat := [3, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_2690778 : Nat := 118140960795 + 2690778 * 2 ^ 59
def prefixEnd_2690778 : Nat := 4983230072969 + 3 ^ 40 * 2690778 * 2
def baseEnd_2690778 : Nat := 307036099676395233866743

theorem tailTrace_2690778 : CollatzResearch.WordTrace tailWord_2690778 prefixEnd_2690778 307036099676395233866743 := by
  unfold tailWord_2690778
  simp only [CollatzResearch.WordTrace]
  refine ⟨24535184061444582285250247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65427157497185552760667325 24535184061444582285250247)
  ·
    refine ⟨36802776092166873427875371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24535184061444582285250247 36802776092166873427875371)
    ·
      refine ⟨55204164138250310141813057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36802776092166873427875371 55204164138250310141813057)
      ·
        refine ⟨41403123103687732606359793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55204164138250310141813057 41403123103687732606359793)
        ·
          refine ⟨31052342327765799454769845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41403123103687732606359793 31052342327765799454769845)
          ·
            refine ⟨2911157093228043698884673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31052342327765799454769845 2911157093228043698884673)
            ·
              refine ⟨2183367819921032774163505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911157093228043698884673 2183367819921032774163505)
              ·
                refine ⟨1637525864940774580622629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183367819921032774163505 1637525864940774580622629)
                ·
                  refine ⟨307036099676395233866743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637525864940774580622629 307036099676395233866743)
                  ·
                    rfl

theorem cell22_2690778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_2690778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690778 prefixEnd_2690778 := by exact prefixLift 2690778
  have htrace : WordTrace (prefixWord ++ tailWord_2690778) baseStart_2690778 baseEnd_2690778 := by
    simpa [prefixWord, tailWord_2690778, baseEnd_2690778] using wordTrace_append hprefix tailTrace_2690778
  have hstable : (prefixWord ++ tailWord_2690778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690778).length < 2 ^ (prefixWord ++ tailWord_2690778).sum := by decide
  have hdescent : baseEnd_2690778 < baseStart_2690778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690806 : List Nat := [5, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2690806 : Nat := 118140960795 + 2690806 * 2 ^ 59
def prefixEnd_2690806 : Nat := 4983230072969 + 3 ^ 40 * 2690806 * 2
def baseEnd_2690806 : Nat := 102346431555711440211127

theorem tailTrace_2690806 : CollatzResearch.WordTrace tailWord_2690806 prefixEnd_2690806 102346431555711440211127 := by
  unfold tailWord_2690806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133859843104805620188767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65427838326451259948680181 6133859843104805620188767)
  ·
    refine ⟨9200789764657208430283151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6133859843104805620188767 9200789764657208430283151)
    ·
      refine ⟨13801184646985812645424727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200789764657208430283151 13801184646985812645424727)
      ·
        refine ⟨20701776970478718968137091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13801184646985812645424727 20701776970478718968137091)
        ·
          refine ⟨31052665455718078452205637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20701776970478718968137091 31052665455718078452205637)
          ·
            refine ⟨5822374772947139709788557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31052665455718078452205637 5822374772947139709788557)
            ·
              refine ⟨2183390539855177391170709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5822374772947139709788557 2183390539855177391170709)
              ·
                refine ⟨102346431555711440211127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2183390539855177391170709 102346431555711440211127)
                ·
                  rfl

theorem cell22_2690806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2690806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690806 prefixEnd_2690806 := by exact prefixLift 2690806
  have htrace : WordTrace (prefixWord ++ tailWord_2690806) baseStart_2690806 baseEnd_2690806 := by
    simpa [prefixWord, tailWord_2690806, baseEnd_2690806] using wordTrace_append hprefix tailTrace_2690806
  have hstable : (prefixWord ++ tailWord_2690806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690806).length < 2 ^ (prefixWord ++ tailWord_2690806).sum := by decide
  have hdescent : baseEnd_2690806 < baseStart_2690806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690849 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2690849 : Nat := 118140960795 + 2690849 * 2 ^ 59
def prefixEnd_2690849 : Nat := 4983230072969 + 3 ^ 40 * 2690849 * 2
def baseEnd_2690849 : Nat := 921132603780165183075011

theorem tailTrace_2690849 : CollatzResearch.WordTrace tailWord_2690849 prefixEnd_2690849 921132603780165183075011 := by
  unfold tailWord_2690849
  simp only [CollatzResearch.WordTrace]
  refine ⟨98143325828521108266835601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65428883885680738844557067 98143325828521108266835601)
  ·
    refine ⟨73607494371390831200126701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98143325828521108266835601 73607494371390831200126701)
    ·
      refine ⟨27602810389271561700047513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73607494371390831200126701 27602810389271561700047513)
      ·
        refine ⟨20702107791953671275035635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27602810389271561700047513 20702107791953671275035635)
        ·
          refine ⟨31053161687930506912553453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20702107791953671275035635 31053161687930506912553453)
          ·
            refine ⟨11644935632973940092207545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31053161687930506912553453 11644935632973940092207545)
            ·
              refine ⟨8733701724730455069155659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11644935632973940092207545 8733701724730455069155659)
              ·
                refine ⟨13100552587095682603733489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733701724730455069155659 13100552587095682603733489)
                ·
                  refine ⟨9825414440321761952800117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13100552587095682603733489 9825414440321761952800117)
                  ·
                    refine ⟨921132603780165183075011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9825414440321761952800117 921132603780165183075011)
                    ·
                      rfl

theorem cell22_2690849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2690849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690849 prefixEnd_2690849 := by exact prefixLift 2690849
  have htrace : WordTrace (prefixWord ++ tailWord_2690849) baseStart_2690849 baseEnd_2690849 := by
    simpa [prefixWord, tailWord_2690849, baseEnd_2690849] using wordTrace_append hprefix tailTrace_2690849
  have hstable : (prefixWord ++ tailWord_2690849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690849).length < 2 ^ (prefixWord ++ tailWord_2690849).sum := by decide
  have hdescent : baseEnd_2690849 < baseStart_2690849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690915 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 1, 4]
def baseStart_2690915 : Nat := 118140960795 + 2690915 * 2 ^ 59
def prefixEnd_2690915 : Nat := 4983230072969 + 3 ^ 40 * 2690915 * 2
def baseEnd_2690915 : Nat := 921155196928963010924809

theorem tailTrace_2690915 : CollatzResearch.WordTrace tailWord_2690915 prefixEnd_2690915 921155196928963010924809 := by
  unfold tailWord_2690915
  simp only [CollatzResearch.WordTrace]
  refine ⟨98145733046282001538738199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65430488697521334359158799 98145733046282001538738199)
  ·
    refine ⟨147218599569423002308107299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98145733046282001538738199 147218599569423002308107299)
    ·
      refine ⟨220827899354134503462160949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147218599569423002308107299 220827899354134503462160949)
      ·
        refine ⟨20702615564450109699577589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220827899354134503462160949 20702615564450109699577589)
        ·
          refine ⟨1940870209167197784335399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20702615564450109699577589 1940870209167197784335399)
          ·
            refine ⟨2911305313750796676503099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940870209167197784335399 2911305313750796676503099)
            ·
              refine ⟨4366957970626195014754649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911305313750796676503099 4366957970626195014754649)
              ·
                refine ⟨3275218477969646261065987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4366957970626195014754649 3275218477969646261065987)
                ·
                  refine ⟨4912827716954469391598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275218477969646261065987 4912827716954469391598981)
                  ·
                    refine ⟨921155196928963010924809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4912827716954469391598981 921155196928963010924809)
                    ·
                      rfl

theorem cell22_2690915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 4].length) (baseStart_2690915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690915 prefixEnd_2690915 := by exact prefixLift 2690915
  have htrace : WordTrace (prefixWord ++ tailWord_2690915) baseStart_2690915 baseEnd_2690915 := by
    simpa [prefixWord, tailWord_2690915, baseEnd_2690915] using wordTrace_append hprefix tailTrace_2690915
  have hstable : (prefixWord ++ tailWord_2690915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690915).length < 2 ^ (prefixWord ++ tailWord_2690915).sum := by decide
  have hdescent : baseEnd_2690915 < baseStart_2690915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690924 : List Nat := [2, 2, 1, 1, 4, 2, 2, 8]
def baseStart_2690924 : Nat := 118140960795 + 2690924 * 2 ^ 59
def prefixEnd_2690924 : Nat := 4983230072969 + 3 ^ 40 * 2690924 * 2
def baseEnd_2690924 : Nat := 102350919756987776383309

theorem tailTrace_2690924 : CollatzResearch.WordTrace tailWord_2690924 prefixEnd_2690924 102350919756987776383309 := by
  unfold tailWord_2690924
  simp only [CollatzResearch.WordTrace]
  refine ⟨49073030651624698037907913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65430707535499597383877217 49073030651624698037907913)
  ·
    refine ⟨36804772988718523528430935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49073030651624698037907913 36804772988718523528430935)
    ·
      refine ⟨55207159483077785292646403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36804772988718523528430935 55207159483077785292646403)
      ·
        refine ⟨82810739224616677938969605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55207159483077785292646403 82810739224616677938969605)
        ·
          refine ⟨15527013604615627113556801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82810739224616677938969605 15527013604615627113556801)
          ·
            refine ⟨11645260203461720335167601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15527013604615627113556801 11645260203461720335167601)
            ·
              refine ⟨8733945152596290251375701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11645260203461720335167601 8733945152596290251375701)
              ·
                refine ⟨102350919756987776383309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8733945152596290251375701 102350919756987776383309)
                ·
                  rfl

theorem cell22_2690924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_2690924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690924 prefixEnd_2690924 := by exact prefixLift 2690924
  have htrace : WordTrace (prefixWord ++ tailWord_2690924) baseStart_2690924 baseEnd_2690924 := by
    simpa [prefixWord, tailWord_2690924, baseEnd_2690924] using wordTrace_append hprefix tailTrace_2690924
  have hstable : (prefixWord ++ tailWord_2690924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690924).length < 2 ^ (prefixWord ++ tailWord_2690924).sum := by decide
  have hdescent : baseEnd_2690924 < baseStart_2690924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690956 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_2690956 : Nat := 118140960795 + 2690956 * 2 ^ 59
def prefixEnd_2690956 : Nat := 4983230072969 + 3 ^ 40 * 2690956 * 2
def baseEnd_2690956 : Nat := 921169232066852570649683

theorem tailTrace_2690956 : CollatzResearch.WordTrace tailWord_2690956 prefixEnd_2690956 921169232066852570649683 := by
  unfold tailWord_2690956
  simp only [CollatzResearch.WordTrace]
  refine ⟨49073614219566732770490361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65431485626088977027320481 49073614219566732770490361)
  ·
    refine ⟨36805210664675049577867771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49073614219566732770490361 36805210664675049577867771)
    ·
      refine ⟨55207815997012574366801657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36805210664675049577867771 55207815997012574366801657)
      ·
        refine ⟨41405861997759430775101243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55207815997012574366801657 41405861997759430775101243)
        ·
          refine ⟨62108792996639146162651865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41405861997759430775101243 62108792996639146162651865)
          ·
            refine ⟨46581594747479359621988899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62108792996639146162651865 46581594747479359621988899)
            ·
              refine ⟨69872392121219039432983349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46581594747479359621988899 69872392121219039432983349)
              ·
                refine ⟨6550536761364284946842189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69872392121219039432983349 6550536761364284946842189)
                ·
                  refine ⟨2456451285511606855065821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550536761364284946842189 2456451285511606855065821)
                  ·
                    refine ⟨921169232066852570649683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456451285511606855065821 921169232066852570649683)
                    ·
                      rfl

theorem cell22_2690956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_2690956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690956 prefixEnd_2690956 := by exact prefixLift 2690956
  have htrace : WordTrace (prefixWord ++ tailWord_2690956) baseStart_2690956 baseEnd_2690956 := by
    simpa [prefixWord, tailWord_2690956, baseEnd_2690956] using wordTrace_append hprefix tailTrace_2690956
  have hstable : (prefixWord ++ tailWord_2690956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690956).length < 2 ^ (prefixWord ++ tailWord_2690956).sum := by decide
  have hdescent : baseEnd_2690956 < baseStart_2690956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2690973 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2690973 : Nat := 118140960795 + 2690973 * 2 ^ 59
def prefixEnd_2690973 : Nat := 4983230072969 + 3 ^ 40 * 2690973 * 2
def baseEnd_2690973 : Nat := 921175051514270192974631

theorem tailTrace_2690973 : CollatzResearch.WordTrace tailWord_2690973 prefixEnd_2690973 921175051514270192974631 := by
  unfold tailWord_2690973
  simp only [CollatzResearch.WordTrace]
  refine ⟨98147848480071877444349573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65431898986714584962899715 98147848480071877444349573)
  ·
    refine ⟨18402721590013477020815545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98147848480071877444349573 18402721590013477020815545)
    ·
      refine ⟨13802041192510107765611659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18402721590013477020815545 13802041192510107765611659)
      ·
        refine ⟨20703061788765161648417489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13802041192510107765611659 20703061788765161648417489)
        ·
          refine ⟨15527296341573871236313117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20703061788765161648417489 15527296341573871236313117)
          ·
            refine ⟨5822736128090201713617419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15527296341573871236313117 5822736128090201713617419)
            ·
              refine ⟨8734104192135302570426129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822736128090201713617419 8734104192135302570426129)
              ·
                refine ⟨6550578144101476927819597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734104192135302570426129 6550578144101476927819597)
                ·
                  refine ⟨2456466804038053847932349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550578144101476927819597 2456466804038053847932349)
                  ·
                    refine ⟨921175051514270192974631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456466804038053847932349 921175051514270192974631)
                    ·
                      rfl

theorem cell22_2690973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2690973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2690973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2690973 prefixEnd_2690973 := by exact prefixLift 2690973
  have htrace : WordTrace (prefixWord ++ tailWord_2690973) baseStart_2690973 baseEnd_2690973 := by
    simpa [prefixWord, tailWord_2690973, baseEnd_2690973] using wordTrace_append hprefix tailTrace_2690973
  have hstable : (prefixWord ++ tailWord_2690973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2690973).length < 2 ^ (prefixWord ++ tailWord_2690973).sum := by decide
  have hdescent : baseEnd_2690973 < baseStart_2690973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2690973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691065 : List Nat := [1, 2, 1, 3, 1, 5, 3, 2, 4]
def baseStart_2691065 : Nat := 118140960795 + 2691065 * 2 ^ 59
def prefixEnd_2691065 : Nat := 4983230072969 + 3 ^ 40 * 2691065 * 2
def baseEnd_2691065 : Nat := 307068848331470873224783

theorem tailTrace_2691065 : CollatzResearch.WordTrace tailWord_2691065 prefixEnd_2691065 307068848331470873224783 := by
  unfold tailWord_2691065
  simp only [CollatzResearch.WordTrace]
  refine ⟨98151203995738577156698649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65434135997159051437799099 98151203995738577156698649)
  ·
    refine ⟨73613402996803932867523987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98151203995738577156698649 73613402996803932867523987)
    ·
      refine ⟨110420104495205899301285981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73613402996803932867523987 110420104495205899301285981)
      ·
        refine ⟨41407539185702212237982243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110420104495205899301285981 41407539185702212237982243)
        ·
          refine ⟨62111308778553318356973365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41407539185702212237982243 62111308778553318356973365)
          ·
            refine ⟨5822935197989373595966253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62111308778553318356973365 5822935197989373595966253)
            ·
              refine ⟨2183600699246015098487345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5822935197989373595966253 2183600699246015098487345)
              ·
                refine ⟨1637700524434511323865509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183600699246015098487345 1637700524434511323865509)
                ·
                  refine ⟨307068848331470873224783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637700524434511323865509 307068848331470873224783)
                  ·
                    rfl

theorem cell22_2691065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_2691065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691065 prefixEnd_2691065 := by exact prefixLift 2691065
  have htrace : WordTrace (prefixWord ++ tailWord_2691065) baseStart_2691065 baseEnd_2691065 := by
    simpa [prefixWord, tailWord_2691065, baseEnd_2691065] using wordTrace_append hprefix tailTrace_2691065
  have hstable : (prefixWord ++ tailWord_2691065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691065).length < 2 ^ (prefixWord ++ tailWord_2691065).sum := by decide
  have hdescent : baseEnd_2691065 < baseStart_2691065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691095 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2691095 : Nat := 118140960795 + 2691095 * 2 ^ 59
def prefixEnd_2691095 : Nat := 4983230072969 + 3 ^ 40 * 2691095 * 2
def baseEnd_2691095 : Nat := 921216814607502541424257

theorem tailTrace_2691095 : CollatzResearch.WordTrace tailWord_2691095 prefixEnd_2691095 921216814607502541424257 := by
  unfold tailWord_2691095
  simp only [CollatzResearch.WordTrace]
  refine ⟨98152298185629892280290739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65434865457086594853527159 98152298185629892280290739)
  ·
    refine ⟨147228447278444838420436109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98152298185629892280290739 147228447278444838420436109)
    ·
      refine ⟨55210667729416814407663541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147228447278444838420436109 55210667729416814407663541)
      ·
        refine ⟨5176000099632826350718457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55210667729416814407663541 5176000099632826350718457)
        ·
          refine ⟨3882000074724619763038843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5176000099632826350718457 3882000074724619763038843)
          ·
            refine ⟨5823000112086929644558265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882000074724619763038843 5823000112086929644558265)
            ·
              refine ⟨4367250084065197233418699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823000112086929644558265 4367250084065197233418699)
              ·
                refine ⟨6550875126097795850128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367250084065197233418699 6550875126097795850128049)
                ·
                  refine ⟨4913156344573346887596037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550875126097795850128049 4913156344573346887596037)
                  ·
                    refine ⟨921216814607502541424257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913156344573346887596037 921216814607502541424257)
                    ·
                      rfl

theorem cell22_2691095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2691095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691095 prefixEnd_2691095 := by exact prefixLift 2691095
  have htrace : WordTrace (prefixWord ++ tailWord_2691095) baseStart_2691095 baseEnd_2691095 := by
    simpa [prefixWord, tailWord_2691095, baseEnd_2691095] using wordTrace_append hprefix tailTrace_2691095
  have hstable : (prefixWord ++ tailWord_2691095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691095).length < 2 ^ (prefixWord ++ tailWord_2691095).sum := by decide
  have hdescent : baseEnd_2691095 < baseStart_2691095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691136 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_2691136 : Nat := 118140960795 + 2691136 * 2 ^ 59
def prefixEnd_2691136 : Nat := 4983230072969 + 3 ^ 40 * 2691136 * 2
def baseEnd_2691136 : Nat := 921230849745392101149131

theorem tailTrace_2691136 : CollatzResearch.WordTrace tailWord_2691136 prefixEnd_2691136 921230849745392101149131 := by
  unfold tailWord_2691136
  simp only [CollatzResearch.WordTrace]
  refine ⟨49076896789240678141266631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65435862385654237521688841 49076896789240678141266631)
  ·
    refine ⟨73615345183861017211899947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49076896789240678141266631 73615345183861017211899947)
    ·
      refine ⟨110423017775791525817849921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73615345183861017211899947 110423017775791525817849921)
      ·
        refine ⟨82817263331843644363387441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110423017775791525817849921 82817263331843644363387441)
        ·
          refine ⟨62112947498882733272540581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82817263331843644363387441 62112947498882733272540581)
          ·
            refine ⟨11646177656040512488601359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62112947498882733272540581 11646177656040512488601359)
            ·
              refine ⟨17469266484060768732902039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11646177656040512488601359 17469266484060768732902039)
              ·
                refine ⟨26203899726091153099353059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17469266484060768732902039 26203899726091153099353059)
                ·
                  refine ⟨39305849589136729649029589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26203899726091153099353059 39305849589136729649029589)
                  ·
                    refine ⟨921230849745392101149131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39305849589136729649029589 921230849745392101149131)
                    ·
                      rfl

theorem cell22_2691136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_2691136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691136 prefixEnd_2691136 := by exact prefixLift 2691136
  have htrace : WordTrace (prefixWord ++ tailWord_2691136) baseStart_2691136 baseEnd_2691136 := by
    simpa [prefixWord, tailWord_2691136, baseEnd_2691136] using wordTrace_append hprefix tailTrace_2691136
  have hstable : (prefixWord ++ tailWord_2691136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691136).length < 2 ^ (prefixWord ++ tailWord_2691136).sum := by decide
  have hdescent : baseEnd_2691136 < baseStart_2691136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691142 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2691142 : Nat := 118140960795 + 2691142 * 2 ^ 59
def prefixEnd_2691142 : Nat := 4983230072969 + 3 ^ 40 * 2691142 * 2
def baseEnd_2691142 : Nat := 921232903668010085499113

theorem tailTrace_2691142 : CollatzResearch.WordTrace tailWord_2691142 prefixEnd_2691142 921232903668010085499113 := by
  unfold tailWord_2691142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067312888014363103351615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65436008277639746204834453 3067312888014363103351615)
  ·
    refine ⟨4600969332021544655027423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3067312888014363103351615 4600969332021544655027423)
    ·
      refine ⟨6901453998032316982541135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4600969332021544655027423 6901453998032316982541135)
      ·
        refine ⟨10352180997048475473811703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901453998032316982541135 10352180997048475473811703)
        ·
          refine ⟨15528271495572713210717555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10352180997048475473811703 15528271495572713210717555)
          ·
            refine ⟨23292407243359069816076333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15528271495572713210717555 23292407243359069816076333)
            ·
              refine ⟨8734652716259651181028625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23292407243359069816076333 8734652716259651181028625)
              ·
                refine ⟨6550989537194738385771469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734652716259651181028625 6550989537194738385771469)
                ·
                  refine ⟨2456621076448026894664301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6550989537194738385771469 2456621076448026894664301)
                  ·
                    refine ⟨921232903668010085499113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456621076448026894664301 921232903668010085499113)
                    ·
                      rfl

theorem cell22_2691142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2691142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691142 prefixEnd_2691142 := by exact prefixLift 2691142
  have htrace : WordTrace (prefixWord ++ tailWord_2691142) baseStart_2691142 baseEnd_2691142 := by
    simpa [prefixWord, tailWord_2691142, baseEnd_2691142] using wordTrace_append hprefix tailTrace_2691142
  have hstable : (prefixWord ++ tailWord_2691142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691142).length < 2 ^ (prefixWord ++ tailWord_2691142).sum := by decide
  have hdescent : baseEnd_2691142 < baseStart_2691142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691183 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 6]
def baseStart_2691183 : Nat := 118140960795 + 2691183 * 2 ^ 59
def prefixEnd_2691183 : Nat := 4983230072969 + 3 ^ 40 * 2691183 * 2
def baseEnd_2691183 : Nat := 307082312935299881741329

theorem tailTrace_2691183 : CollatzResearch.WordTrace tailWord_2691183 prefixEnd_2691183 307082312935299881741329 := by
  unfold tailWord_2691183
  simp only [CollatzResearch.WordTrace]
  refine ⟨98155507809311083309494203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65437005206207388872996135 98155507809311083309494203)
  ·
    refine ⟨147233261713966624964241305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98155507809311083309494203 147233261713966624964241305)
    ·
      refine ⟨110424946285474968723180979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147233261713966624964241305 110424946285474968723180979)
      ·
        refine ⟨165637419428212453084771469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110424946285474968723180979 165637419428212453084771469)
        ·
          refine ⟨62114032285579669906789301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165637419428212453084771469 62114032285579669906789301)
          ·
            refine ⟨5823190526773094053761497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62114032285579669906789301 5823190526773094053761497)
            ·
              refine ⟨4367392895079820540321123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823190526773094053761497 4367392895079820540321123)
              ·
                refine ⟨6551089342619730810481685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367392895079820540321123 6551089342619730810481685)
                ·
                  refine ⟨307082312935299881741329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6551089342619730810481685 307082312935299881741329)
                  ·
                    rfl

theorem cell22_2691183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_2691183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691183 prefixEnd_2691183 := by exact prefixLift 2691183
  have htrace : WordTrace (prefixWord ++ tailWord_2691183) baseStart_2691183 baseEnd_2691183 := by
    simpa [prefixWord, tailWord_2691183, baseEnd_2691183] using wordTrace_append hprefix tailTrace_2691183
  have hstable : (prefixWord ++ tailWord_2691183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691183).length < 2 ^ (prefixWord ++ tailWord_2691183).sum := by decide
  have hdescent : baseEnd_2691183 < baseStart_2691183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691234 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_2691234 : Nat := 118140960795 + 2691234 * 2 ^ 59
def prefixEnd_2691234 : Nat := 4983230072969 + 3 ^ 40 * 2691234 * 2
def baseEnd_2691234 : Nat := 307088132382717504066277

theorem tailTrace_2691234 : CollatzResearch.WordTrace tailWord_2691234 prefixEnd_2691234 307088132382717504066277 := by
  unfold tailWord_2691234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539341983031579754900189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65438245288084212679733837 24539341983031579754900189)
  ·
    refine ⟨9202253243636842408087571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24539341983031579754900189 9202253243636842408087571)
    ·
      refine ⟨13803379865455263612131357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9202253243636842408087571 13803379865455263612131357)
      ·
        refine ⟨5176267449545723854549259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13803379865455263612131357 5176267449545723854549259)
        ·
          refine ⟨7764401174318585781823889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5176267449545723854549259 7764401174318585781823889)
          ·
            refine ⟨5823300880738939336367917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764401174318585781823889 5823300880738939336367917)
            ·
              refine ⟨2183737830277102251137969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5823300880738939336367917 2183737830277102251137969)
              ·
                refine ⟨1637803372707826688353477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2183737830277102251137969 1637803372707826688353477)
                ·
                  refine ⟨307088132382717504066277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637803372707826688353477 307088132382717504066277)
                  ·
                    rfl

theorem cell22_2691234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_2691234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691234 prefixEnd_2691234 := by exact prefixLift 2691234
  have htrace : WordTrace (prefixWord ++ tailWord_2691234) baseStart_2691234 baseEnd_2691234 := by
    simpa [prefixWord, tailWord_2691234, baseEnd_2691234] using wordTrace_append hprefix tailTrace_2691234
  have hstable : (prefixWord ++ tailWord_2691234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691234).length < 2 ^ (prefixWord ++ tailWord_2691234).sum := by decide
  have hdescent : baseEnd_2691234 < baseStart_2691234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691245 : List Nat := [1, 5, 2, 1, 2, 2, 2, 7]
def baseStart_2691245 : Nat := 118140960795 + 2691245 * 2 ^ 59
def prefixEnd_2691245 : Nat := 4983230072969 + 3 ^ 40 * 2691245 * 2
def baseEnd_2691245 : Nat := 102363129185883572241533

theorem tailTrace_2691245 : CollatzResearch.WordTrace tailWord_2691245 prefixEnd_2691245 102363129185883572241533 := by
  unfold tailWord_2691245
  simp only [CollatzResearch.WordTrace]
  refine ⟨98157769135086467898251189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65438512756724311932167459 98157769135086467898251189)
  ·
    refine ⟨9202290856414356365461049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98157769135086467898251189 9202290856414356365461049)
    ·
      refine ⟨6901718142310767274095787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9202290856414356365461049 6901718142310767274095787)
      ·
        refine ⟨10352577213466150911143681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6901718142310767274095787 10352577213466150911143681)
        ·
          refine ⟨7764432910099613183357761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10352577213466150911143681 7764432910099613183357761)
          ·
            refine ⟨5823324682574709887518321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764432910099613183357761 5823324682574709887518321)
            ·
              refine ⟨4367493511931032415638741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823324682574709887518321 4367493511931032415638741)
              ·
                refine ⟨102363129185883572241533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4367493511931032415638741 102363129185883572241533)
                ·
                  rfl

theorem cell22_2691245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 7].length) (baseStart_2691245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691245 prefixEnd_2691245 := by exact prefixLift 2691245
  have htrace : WordTrace (prefixWord ++ tailWord_2691245) baseStart_2691245 baseEnd_2691245 := by
    simpa [prefixWord, tailWord_2691245, baseEnd_2691245] using wordTrace_append hprefix tailTrace_2691245
  have hstable : (prefixWord ++ tailWord_2691245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691245).length < 2 ^ (prefixWord ++ tailWord_2691245).sum := by decide
  have hdescent : baseEnd_2691245 < baseStart_2691245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691333 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2691333 : Nat := 118140960795 + 2691333 * 2 ^ 59
def prefixEnd_2691333 : Nat := 4983230072969 + 3 ^ 40 * 2691333 * 2
def baseEnd_2691333 : Nat := 921298286871349253973527

theorem tailTrace_2691333 : CollatzResearch.WordTrace tailWord_2691333 prefixEnd_2691333 921298286871349253973527 := by
  unfold tailWord_2691333
  simp only [CollatzResearch.WordTrace]
  refine ⟨98160978758767658927454653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65440652505845105951636435 98160978758767658927454653)
  ·
    refine ⟨36810367034537872097795495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98160978758767658927454653 36810367034537872097795495)
    ·
      refine ⟨55215550551806808146693243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36810367034537872097795495 55215550551806808146693243)
      ·
        refine ⟨82823325827710212220039865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55215550551806808146693243 82823325827710212220039865)
        ·
          refine ⟨62117494370782659165029899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82823325827710212220039865 62117494370782659165029899)
          ·
            refine ⟨93176241556173988747544849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62117494370782659165029899 93176241556173988747544849)
            ·
              refine ⟨69882181167130491560658637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93176241556173988747544849 69882181167130491560658637)
              ·
                refine ⟨26205817937673934335246989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69882181167130491560658637 26205817937673934335246989)
                ·
                  refine ⟨9827181726627725375717621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26205817937673934335246989 9827181726627725375717621)
                  ·
                    refine ⟨921298286871349253973527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9827181726627725375717621 921298286871349253973527)
                    ·
                      rfl

theorem cell22_2691333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2691333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691333 prefixEnd_2691333 := by exact prefixLift 2691333
  have htrace : WordTrace (prefixWord ++ tailWord_2691333) baseStart_2691333 baseEnd_2691333 := by
    simpa [prefixWord, tailWord_2691333, baseEnd_2691333] using wordTrace_append hprefix tailTrace_2691333
  have hstable : (prefixWord ++ tailWord_2691333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691333).length < 2 ^ (prefixWord ++ tailWord_2691333).sum := by decide
  have hdescent : baseEnd_2691333 < baseStart_2691333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691337 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_2691337 : Nat := 118140960795 + 2691337 * 2 ^ 59
def prefixEnd_2691337 : Nat := 4983230072969 + 3 ^ 40 * 2691337 * 2
def baseEnd_2691337 : Nat := 921299656153094576873515

theorem tailTrace_2691337 : CollatzResearch.WordTrace tailWord_2691337 prefixEnd_2691337 921299656153094576873515 := by
  unfold tailWord_2691337
  simp only [CollatzResearch.WordTrace]
  refine ⟨98161124650753167610600265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65440749767168778407066843 98161124650753167610600265)
  ·
    refine ⟨73620843488064875707950199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98161124650753167610600265 73620843488064875707950199)
    ·
      refine ⟨110431265232097313561925299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73620843488064875707950199 110431265232097313561925299)
      ·
        refine ⟨165646897848145970342887949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110431265232097313561925299 165646897848145970342887949)
        ·
          refine ⟨62117586693054738878582981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165646897848145970342887949 62117586693054738878582981)
          ·
            refine ⟨11647047504947763539734309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62117586693054738878582981 11647047504947763539734309)
            ·
              refine ⟨2183821407177705663700183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11647047504947763539734309 2183821407177705663700183)
              ·
                refine ⟨3275732110766558495550275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183821407177705663700183 3275732110766558495550275)
                ·
                  refine ⟨4913598166149837743325413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275732110766558495550275 4913598166149837743325413)
                  ·
                    refine ⟨921299656153094576873515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913598166149837743325413 921299656153094576873515)
                    ·
                      rfl

theorem cell22_2691337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_2691337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691337 prefixEnd_2691337 := by exact prefixLift 2691337
  have htrace : WordTrace (prefixWord ++ tailWord_2691337) baseStart_2691337 baseEnd_2691337 := by
    simpa [prefixWord, tailWord_2691337, baseEnd_2691337] using wordTrace_append hprefix tailTrace_2691337
  have hstable : (prefixWord ++ tailWord_2691337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691337).length < 2 ^ (prefixWord ++ tailWord_2691337).sum := by decide
  have hdescent : baseEnd_2691337 < baseStart_2691337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691363 : List Nat := [1, 1, 1, 4, 2, 2, 2, 9]
def baseStart_2691363 : Nat := 118140960795 + 2691363 * 2 ^ 59
def prefixEnd_2691363 : Nat := 4983230072969 + 3 ^ 40 * 2691363 * 2
def baseEnd_2691363 : Nat := 102367617387159908413715

theorem tailTrace_2691363 : CollatzResearch.WordTrace tailWord_2691363 prefixEnd_2691363 102367617387159908413715 := by
  unfold tailWord_2691363
  simp only [CollatzResearch.WordTrace]
  refine ⟨98162072948658974051046743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65441381965772649367364495 98162072948658974051046743)
  ·
    refine ⟨147243109422988461076570115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98162072948658974051046743 147243109422988461076570115)
    ·
      refine ⟨220864664134482691614855173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147243109422988461076570115 220864664134482691614855173)
      ·
        refine ⟨41412124525215504677785345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220864664134482691614855173 41412124525215504677785345)
        ·
          refine ⟨31059093393911628508339009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41412124525215504677785345 31059093393911628508339009)
          ·
            refine ⟨23294320045433721381254257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31059093393911628508339009 23294320045433721381254257)
            ·
              refine ⟨17470740034075291035940693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23294320045433721381254257 17470740034075291035940693)
              ·
                refine ⟨102367617387159908413715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17470740034075291035940693 102367617387159908413715)
                ·
                  rfl

theorem cell22_2691363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_2691363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691363 prefixEnd_2691363 := by exact prefixLift 2691363
  have htrace : WordTrace (prefixWord ++ tailWord_2691363) baseStart_2691363 baseEnd_2691363 := by
    simpa [prefixWord, tailWord_2691363, baseEnd_2691363] using wordTrace_append hprefix tailTrace_2691363
  have hstable : (prefixWord ++ tailWord_2691363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691363).length < 2 ^ (prefixWord ++ tailWord_2691363).sum := by decide
  have hdescent : baseEnd_2691363 < baseStart_2691363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691395 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 5, 3]
def baseStart_2691395 : Nat := 118140960795 + 2691395 * 2 ^ 59
def prefixEnd_2691395 : Nat := 4983230072969 + 3 ^ 40 * 2691395 * 2
def baseEnd_2691395 : Nat := 921319510738401758923337

theorem tailTrace_2691395 : CollatzResearch.WordTrace tailWord_2691395 prefixEnd_2691395 921319510738401758923337 := by
  unfold tailWord_2691395
  simp only [CollatzResearch.WordTrace]
  refine ⟨98163240084543043516211639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65442160056362029010807759 98163240084543043516211639)
  ·
    refine ⟨147244860126814565274317459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98163240084543043516211639 147244860126814565274317459)
    ·
      refine ⟨220867290190221847911476189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147244860126814565274317459 220867290190221847911476189)
      ·
        refine ⟨82825233821333192966803571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220867290190221847911476189 82825233821333192966803571)
        ·
          refine ⟨124237850731999789450205357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82825233821333192966803571 124237850731999789450205357)
          ·
            refine ⟨46589194024499921043827009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124237850731999789450205357 46589194024499921043827009)
            ·
              refine ⟨34941895518374940782870257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46589194024499921043827009 34941895518374940782870257)
              ·
                refine ⟨26206421638781205587152693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34941895518374940782870257 26206421638781205587152693)
                ·
                  refine ⟨2456852028635738023795565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26206421638781205587152693 2456852028635738023795565)
                  ·
                    refine ⟨921319510738401758923337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2456852028635738023795565 921319510738401758923337)
                    ·
                      rfl

theorem cell22_2691395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3].length) (baseStart_2691395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691395 prefixEnd_2691395 := by exact prefixLift 2691395
  have htrace : WordTrace (prefixWord ++ tailWord_2691395) baseStart_2691395 baseEnd_2691395 := by
    simpa [prefixWord, tailWord_2691395, baseEnd_2691395] using wordTrace_append hprefix tailTrace_2691395
  have hstable : (prefixWord ++ tailWord_2691395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691395).length < 2 ^ (prefixWord ++ tailWord_2691395).sum := by decide
  have hdescent : baseEnd_2691395 < baseStart_2691395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691422 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2691422 : Nat := 118140960795 + 2691422 * 2 ^ 59
def prefixEnd_2691422 : Nat := 4983230072969 + 3 ^ 40 * 2691422 * 2
def baseEnd_2691422 : Nat := 921328753390182688498255

theorem tailTrace_2691422 : CollatzResearch.WordTrace tailWord_2691422 prefixEnd_2691422 921328753390182688498255 := by
  unfold tailWord_2691422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12270528106930653390930565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65442816570296818084963013 12270528106930653390930565)
  ·
    refine ⟨2300724020049497510799481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12270528106930653390930565 2300724020049497510799481)
    ·
      refine ⟨1725543015037123133099611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300724020049497510799481 1725543015037123133099611)
      ·
        refine ⟨2588314522555684699649417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725543015037123133099611 2588314522555684699649417)
        ·
          refine ⟨1941235891916763524737063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588314522555684699649417 1941235891916763524737063)
          ·
            refine ⟨2911853837875145287105595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941235891916763524737063 2911853837875145287105595)
            ·
              refine ⟨4367780756812717930658393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911853837875145287105595 4367780756812717930658393)
              ·
                refine ⟨3275835567609538447993795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367780756812717930658393 3275835567609538447993795)
                ·
                  refine ⟨4913753351414307671990693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3275835567609538447993795 4913753351414307671990693)
                  ·
                    refine ⟨921328753390182688498255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4913753351414307671990693 921328753390182688498255)
                    ·
                      rfl

theorem cell22_2691422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2691422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691422 prefixEnd_2691422 := by exact prefixLift 2691422
  have htrace : WordTrace (prefixWord ++ tailWord_2691422) baseStart_2691422 baseEnd_2691422 := by
    simpa [prefixWord, tailWord_2691422, baseEnd_2691422] using wordTrace_append hprefix tailTrace_2691422
  have hstable : (prefixWord ++ tailWord_2691422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691422).length < 2 ^ (prefixWord ++ tailWord_2691422).sum := by decide
  have hdescent : baseEnd_2691422 < baseStart_2691422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691637 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2691637 : Nat := 118140960795 + 2691637 * 2 ^ 59
def prefixEnd_2691637 : Nat := 4983230072969 + 3 ^ 40 * 2691637 * 2
def baseEnd_2691637 : Nat := 921402352283993794372595

theorem tailTrace_2691637 : CollatzResearch.WordTrace tailWord_2691637 prefixEnd_2691637 921402352283993794372595 := by
  unfold tailWord_2691637
  simp only [CollatzResearch.WordTrace]
  refine ⟨98172066549666318846521165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65448044366444212564347443 98172066549666318846521165)
  ·
    refine ⟨36814524956124869567445437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98172066549666318846521165 36814524956124869567445437)
    ·
      refine ⟨13805446858546826087792039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36814524956124869567445437 13805446858546826087792039)
      ·
        refine ⟨20708170287820239131688059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13805446858546826087792039 20708170287820239131688059)
        ·
          refine ⟨31062255431730358697532089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20708170287820239131688059 31062255431730358697532089)
          ·
            refine ⟨23296691573797769023149067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31062255431730358697532089 23296691573797769023149067)
            ·
              refine ⟨34945037360696653534723601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23296691573797769023149067 34945037360696653534723601)
              ·
                refine ⟨26208778020522490151042701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34945037360696653534723601 26208778020522490151042701)
                ·
                  refine ⟨9828291757695933806641013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26208778020522490151042701 9828291757695933806641013)
                  ·
                    refine ⟨921402352283993794372595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9828291757695933806641013 921402352283993794372595)
                    ·
                      rfl

theorem cell22_2691637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2691637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691637 prefixEnd_2691637 := by exact prefixLift 2691637
  have htrace : WordTrace (prefixWord ++ tailWord_2691637) baseStart_2691637 baseEnd_2691637 := by
    simpa [prefixWord, tailWord_2691637, baseEnd_2691637] using wordTrace_append hprefix tailTrace_2691637
  have hstable : (prefixWord ++ tailWord_2691637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691637).length < 2 ^ (prefixWord ++ tailWord_2691637).sum := by decide
  have hdescent : baseEnd_2691637 < baseStart_2691637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691639 : List Nat := [1, 1, 3, 1, 2, 3, 3, 4, 4]
def baseStart_2691639 : Nat := 118140960795 + 2691639 * 2 ^ 59
def prefixEnd_2691639 : Nat := 4983230072969 + 3 ^ 40 * 2691639 * 2
def baseEnd_2691639 : Nat := 307134345641622151940863

theorem tailTrace_2691639 : CollatzResearch.WordTrace tailWord_2691639 prefixEnd_2691639 307134345641622151940863 := by
  unfold tailWord_2691639
  simp only [CollatzResearch.WordTrace]
  refine ⟨98172139495659073188093971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65448092997106048792062647 98172139495659073188093971)
  ·
    refine ⟨147258209243488609782140957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98172139495659073188093971 147258209243488609782140957)
    ·
      refine ⟨55221828466308228668302859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147258209243488609782140957 55221828466308228668302859)
      ·
        refine ⟨82832742699462343002454289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55221828466308228668302859 82832742699462343002454289)
        ·
          refine ⟨62124557024596757251840717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82832742699462343002454289 62124557024596757251840717)
          ·
            refine ⟨23296708884223783969440269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62124557024596757251840717 23296708884223783969440269)
            ·
              refine ⟨8736265831583918988540101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23296708884223783969440269 8736265831583918988540101)
              ·
                refine ⟨1638049843421984810351269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8736265831583918988540101 1638049843421984810351269)
                ·
                  refine ⟨307134345641622151940863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638049843421984810351269 307134345641622151940863)
                  ·
                    rfl

theorem cell22_2691639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 4].length) (baseStart_2691639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691639 prefixEnd_2691639 := by exact prefixLift 2691639
  have htrace : WordTrace (prefixWord ++ tailWord_2691639) baseStart_2691639 baseEnd_2691639 := by
    simpa [prefixWord, tailWord_2691639, baseEnd_2691639] using wordTrace_append hprefix tailTrace_2691639
  have hstable : (prefixWord ++ tailWord_2691639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691639).length < 2 ^ (prefixWord ++ tailWord_2691639).sum := by decide
  have hdescent : baseEnd_2691639 < baseStart_2691639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691669 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2691669 : Nat := 118140960795 + 2691669 * 2 ^ 59
def prefixEnd_2691669 : Nat := 4983230072969 + 3 ^ 40 * 2691669 * 2
def baseEnd_2691669 : Nat := 921413306537956377572497

theorem tailTrace_2691669 : CollatzResearch.WordTrace tailWord_2691669 prefixEnd_2691669 921413306537956377572497 := by
  unfold tailWord_2691669
  simp only [CollatzResearch.WordTrace]
  refine ⟨98173233685550388311686061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65448822457033592207790707 98173233685550388311686061)
  ·
    refine ⟨36814962632081395616882273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98173233685550388311686061 36814962632081395616882273)
    ·
      refine ⟨27611221974061046712661705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36814962632081395616882273 27611221974061046712661705)
      ·
        refine ⟨20708416480545785034496279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27611221974061046712661705 20708416480545785034496279)
        ·
          refine ⟨31062624720818677551744419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20708416480545785034496279 31062624720818677551744419)
          ·
            refine ⟨46593937081228016327616629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31062624720818677551744419 46593937081228016327616629)
            ·
              refine ⟨4368181601365126530714059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46593937081228016327616629 4368181601365126530714059)
              ·
                refine ⟨6552272402047689796071089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368181601365126530714059 6552272402047689796071089)
                ·
                  refine ⟨4914204301535767347053317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6552272402047689796071089 4914204301535767347053317)
                  ·
                    refine ⟨921413306537956377572497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914204301535767347053317 921413306537956377572497)
                    ·
                      rfl

theorem cell22_2691669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2691669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691669 prefixEnd_2691669 := by exact prefixLift 2691669
  have htrace : WordTrace (prefixWord ++ tailWord_2691669) baseStart_2691669 baseEnd_2691669 := by
    simpa [prefixWord, tailWord_2691669, baseEnd_2691669] using wordTrace_append hprefix tailTrace_2691669
  have hstable : (prefixWord ++ tailWord_2691669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691669).length < 2 ^ (prefixWord ++ tailWord_2691669).sum := by decide
  have hdescent : baseEnd_2691669 < baseStart_2691669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691716 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2691716 : Nat := 118140960795 + 2691716 * 2 ^ 59
def prefixEnd_2691716 : Nat := 4983230072969 + 3 ^ 40 * 2691716 * 2
def baseEnd_2691716 : Nat := 921429395598463921647353

theorem tailTrace_2691716 : CollatzResearch.WordTrace tailWord_2691716 prefixEnd_2691716 921429395598463921647353 := by
  unfold tailWord_2691716
  simp only [CollatzResearch.WordTrace]
  refine ⟨49087473958190057669323501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65449965277586743559098001 49087473958190057669323501)
  ·
    refine ⟨18407802734321271625996313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49087473958190057669323501 18407802734321271625996313)
    ·
      refine ⟨13805852050740953719497235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18407802734321271625996313 13805852050740953719497235)
      ·
        refine ⟨20708778076111430579245853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13805852050740953719497235 20708778076111430579245853)
        ·
          refine ⟨7765791778541786467217195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20708778076111430579245853 7765791778541786467217195)
          ·
            refine ⟨11648687667812679700825793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7765791778541786467217195 11648687667812679700825793)
            ·
              refine ⟨8736515750859509775619345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11648687667812679700825793 8736515750859509775619345)
              ·
                refine ⟨6552386813144632331714509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8736515750859509775619345 6552386813144632331714509)
                ·
                  refine ⟨2457145054929237124392941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6552386813144632331714509 2457145054929237124392941)
                  ·
                    refine ⟨921429395598463921647353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2457145054929237124392941 921429395598463921647353)
                    ·
                      rfl

theorem cell22_2691716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2691716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691716 prefixEnd_2691716 := by exact prefixLift 2691716
  have htrace : WordTrace (prefixWord ++ tailWord_2691716) baseStart_2691716 baseEnd_2691716 := by
    simpa [prefixWord, tailWord_2691716, baseEnd_2691716] using wordTrace_append hprefix tailTrace_2691716
  have hstable : (prefixWord ++ tailWord_2691716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691716).length < 2 ^ (prefixWord ++ tailWord_2691716).sum := by decide
  have hdescent : baseEnd_2691716 < baseStart_2691716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691774 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2691774 : Nat := 118140960795 + 2691774 * 2 ^ 59
def prefixEnd_2691774 : Nat := 4983230072969 + 3 ^ 40 * 2691774 * 2
def baseEnd_2691774 : Nat := 307149750061257034565725

theorem tailTrace_2691774 : CollatzResearch.WordTrace tailWord_2691774 prefixEnd_2691774 307149750061257034565725 := by
  unfold tailWord_2691774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272132918771248905532297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65451375566779994162838917 12272132918771248905532297)
  ·
    refine ⟨9204099689078436679149223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12272132918771248905532297 9204099689078436679149223)
    ·
      refine ⟨13806149533617655018723835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204099689078436679149223 13806149533617655018723835)
      ·
        refine ⟨20709224300426482528085753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13806149533617655018723835 20709224300426482528085753)
        ·
          refine ⟨15531918225319861896064315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20709224300426482528085753 15531918225319861896064315)
          ·
            refine ⟨23297877337979792844096473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15531918225319861896064315 23297877337979792844096473)
            ·
              refine ⟨17473408003484844633072355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23297877337979792844096473 17473408003484844633072355)
              ·
                refine ⟨26210112005227266949608533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17473408003484844633072355 26210112005227266949608533)
                ·
                  refine ⟨307149750061257034565725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26210112005227266949608533 307149750061257034565725)
                  ·
                    rfl

theorem cell22_2691774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2691774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691774 prefixEnd_2691774 := by exact prefixLift 2691774
  have htrace : WordTrace (prefixWord ++ tailWord_2691774) baseStart_2691774 baseEnd_2691774 := by
    simpa [prefixWord, tailWord_2691774, baseEnd_2691774] using wordTrace_append hprefix tailTrace_2691774
  have hstable : (prefixWord ++ tailWord_2691774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691774).length < 2 ^ (prefixWord ++ tailWord_2691774).sum := by decide
  have hdescent : baseEnd_2691774 < baseStart_2691774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691776 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_2691776 : Nat := 118140960795 + 2691776 * 2 ^ 59
def prefixEnd_2691776 : Nat := 4983230072969 + 3 ^ 40 * 2691776 * 2
def baseEnd_2691776 : Nat := 921449934824643765147169

theorem tailTrace_2691776 : CollatzResearch.WordTrace tailWord_2691776 prefixEnd_2691776 921449934824643765147169 := by
  unfold tailWord_2691776
  simp only [CollatzResearch.WordTrace]
  refine ⟨49088568148081372792915591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65451424197441830390554121 49088568148081372792915591)
  ·
    refine ⟨73632852222122059189373387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49088568148081372792915591 73632852222122059189373387)
    ·
      refine ⟨110449278333183088784060081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73632852222122059189373387 110449278333183088784060081)
      ·
        refine ⟨82836958749887316588045061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110449278333183088784060081 82836958749887316588045061)
        ·
          refine ⟨15531929765603871860258449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82836958749887316588045061 15531929765603871860258449)
          ·
            refine ⟨11648947324202903895193837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15531929765603871860258449 11648947324202903895193837)
            ·
              refine ⟨4368355246576088960697689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11648947324202903895193837 4368355246576088960697689)
              ·
                refine ⟨3276266434932066720523267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368355246576088960697689 3276266434932066720523267)
                ·
                  refine ⟨4914399652398100080784901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3276266434932066720523267 4914399652398100080784901)
                  ·
                    refine ⟨921449934824643765147169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914399652398100080784901 921449934824643765147169)
                    ·
                      rfl

theorem cell22_2691776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_2691776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691776 prefixEnd_2691776 := by exact prefixLift 2691776
  have htrace : WordTrace (prefixWord ++ tailWord_2691776) baseStart_2691776 baseEnd_2691776 := by
    simpa [prefixWord, tailWord_2691776, baseEnd_2691776] using wordTrace_append hprefix tailTrace_2691776
  have hstable : (prefixWord ++ tailWord_2691776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691776).length < 2 ^ (prefixWord ++ tailWord_2691776).sum := by decide
  have hdescent : baseEnd_2691776 < baseStart_2691776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691836 : List Nat := [2, 2, 2, 1, 3, 3, 3, 6]
def baseStart_2691836 : Nat := 118140960795 + 2691836 * 2 ^ 59
def prefixEnd_2691836 : Nat := 4983230072969 + 3 ^ 40 * 2691836 * 2
def baseEnd_2691836 : Nat := 102385608227869289849665

theorem tailTrace_2691836 : CollatzResearch.WordTrace tailWord_2691836 prefixEnd_2691836 102385608227869289849665 := by
  unfold tailWord_2691836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089662337972687916507681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65452883117296917222010241 49089662337972687916507681)
  ·
    refine ⟨36817246753479515937380761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49089662337972687916507681 36817246753479515937380761)
    ·
      refine ⟨27612935065109636953035571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36817246753479515937380761 27612935065109636953035571)
      ·
        refine ⟨41419402597664455429553357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27612935065109636953035571 41419402597664455429553357)
        ·
          refine ⟨15532275974124170786082509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41419402597664455429553357 15532275974124170786082509)
          ·
            refine ⟨5824603490296564044780941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15532275974124170786082509 5824603490296564044780941)
            ·
              refine ⟨2184226308861211516792853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5824603490296564044780941 2184226308861211516792853)
              ·
                refine ⟨102385608227869289849665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184226308861211516792853 102385608227869289849665)
                ·
                  rfl

theorem cell22_2691836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_2691836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691836 prefixEnd_2691836 := by exact prefixLift 2691836
  have htrace : WordTrace (prefixWord ++ tailWord_2691836) baseStart_2691836 baseEnd_2691836 := by
    simpa [prefixWord, tailWord_2691836, baseEnd_2691836] using wordTrace_append hprefix tailTrace_2691836
  have hstable : (prefixWord ++ tailWord_2691836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691836).length < 2 ^ (prefixWord ++ tailWord_2691836).sum := by decide
  have hdescent : baseEnd_2691836 < baseStart_2691836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691838 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2691838 : Nat := 118140960795 + 2691838 * 2 ^ 59
def prefixEnd_2691838 : Nat := 4983230072969 + 3 ^ 40 * 2691838 * 2
def baseEnd_2691838 : Nat := 921471158691696270096979

theorem tailTrace_2691838 : CollatzResearch.WordTrace tailWord_2691838 prefixEnd_2691838 921471158691696270096979 := by
  unfold tailWord_2691838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12272424702742266271823521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65452931747958753449725445 12272424702742266271823521)
  ·
    refine ⟨9204318527056699703867641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12272424702742266271823521 9204318527056699703867641)
    ·
      refine ⟨6903238895292524777900731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9204318527056699703867641 6903238895292524777900731)
      ·
        refine ⟨10354858342938787166851097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903238895292524777900731 10354858342938787166851097)
        ·
          refine ⟨7766143757204090375138323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10354858342938787166851097 7766143757204090375138323)
          ·
            refine ⟨11649215635806135562707485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766143757204090375138323 11649215635806135562707485)
            ·
              refine ⟨4368455863427300836015307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11649215635806135562707485 4368455863427300836015307)
              ·
                refine ⟨6552683795140951254022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368455863427300836015307 6552683795140951254022961)
                ·
                  refine ⟨4914512846355713440517221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6552683795140951254022961 4914512846355713440517221)
                  ·
                    refine ⟨921471158691696270096979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914512846355713440517221 921471158691696270096979)
                    ·
                      rfl

theorem cell22_2691838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2691838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691838 prefixEnd_2691838 := by exact prefixLift 2691838
  have htrace : WordTrace (prefixWord ++ tailWord_2691838) baseStart_2691838 baseEnd_2691838 := by
    simpa [prefixWord, tailWord_2691838, baseEnd_2691838] using wordTrace_append hprefix tailTrace_2691838
  have hstable : (prefixWord ++ tailWord_2691838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691838).length < 2 ^ (prefixWord ++ tailWord_2691838).sum := by decide
  have hdescent : baseEnd_2691838 < baseStart_2691838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691868 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2691868 : Nat := 118140960795 + 2691868 * 2 ^ 59
def prefixEnd_2691868 : Nat := 4983230072969 + 3 ^ 40 * 2691868 * 2
def baseEnd_2691868 : Nat := 921481428304786191846887

theorem tailTrace_2691868 : CollatzResearch.WordTrace tailWord_2691868 prefixEnd_2691868 921481428304786191846887 := by
  unfold tailWord_2691868
  simp only [CollatzResearch.WordTrace]
  refine ⟨49090245905914722649090129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65453661207886296865453505 49090245905914722649090129)
  ·
    refine ⟨36817684429436041986817597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49090245905914722649090129 36817684429436041986817597)
    ·
      refine ⟨13806631661038515745056599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36817684429436041986817597 13806631661038515745056599)
      ·
        refine ⟨20709947491557773617584899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13806631661038515745056599 20709947491557773617584899)
        ·
          refine ⟨31064921237336660426377349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20709947491557773617584899 31064921237336660426377349)
          ·
            refine ⟨5824672732000623829945753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31064921237336660426377349 5824672732000623829945753)
            ·
              refine ⟨4368504549000467872459315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824672732000623829945753 4368504549000467872459315)
              ·
                refine ⟨6552756823500701808688973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368504549000467872459315 6552756823500701808688973)
                ·
                  refine ⟨2457283808812763178258365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6552756823500701808688973 2457283808812763178258365)
                  ·
                    refine ⟨921481428304786191846887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2457283808812763178258365 921481428304786191846887)
                    ·
                      rfl

theorem cell22_2691868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2691868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691868 prefixEnd_2691868 := by exact prefixLift 2691868
  have htrace : WordTrace (prefixWord ++ tailWord_2691868) baseStart_2691868 baseEnd_2691868 := by
    simpa [prefixWord, tailWord_2691868, baseEnd_2691868] using wordTrace_append hprefix tailTrace_2691868
  have hstable : (prefixWord ++ tailWord_2691868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691868).length < 2 ^ (prefixWord ++ tailWord_2691868).sum := by decide
  have hdescent : baseEnd_2691868 < baseStart_2691868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691958 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2691958 : Nat := 118140960795 + 2691958 * 2 ^ 59
def prefixEnd_2691958 : Nat := 4983230072969 + 3 ^ 40 * 2691958 * 2
def baseEnd_2691958 : Nat := 921512237144055957096611

theorem tailTrace_2691958 : CollatzResearch.WordTrace tailWord_2691958 prefixEnd_2691958 921512237144055957096611 := by
  unfold tailWord_2691958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136485898843961916809783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65455849587668927112637685 6136485898843961916809783)
  ·
    refine ⟨9204728848265942875214675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136485898843961916809783 9204728848265942875214675)
    ·
      refine ⟨13807093272398914312822013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9204728848265942875214675 13807093272398914312822013)
      ·
        refine ⟨5177659977149592867308255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13807093272398914312822013 5177659977149592867308255)
        ·
          refine ⟨7766489965724389300962383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177659977149592867308255 7766489965724389300962383)
          ·
            refine ⟨11649734948586583951443575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766489965724389300962383 11649734948586583951443575)
            ·
              refine ⟨17474602422879875927165363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11649734948586583951443575 17474602422879875927165363)
              ·
                refine ⟨26211903634319813890748045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17474602422879875927165363 26211903634319813890748045)
                ·
                  refine ⟨9829463862869930209030517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26211903634319813890748045 9829463862869930209030517)
                  ·
                    refine ⟨921512237144055957096611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9829463862869930209030517 921512237144055957096611)
                    ·
                      rfl

theorem cell22_2691958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2691958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691958 prefixEnd_2691958 := by exact prefixLift 2691958
  have htrace : WordTrace (prefixWord ++ tailWord_2691958) baseStart_2691958 baseEnd_2691958 := by
    simpa [prefixWord, tailWord_2691958, baseEnd_2691958] using wordTrace_append hprefix tailTrace_2691958
  have hstable : (prefixWord ++ tailWord_2691958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691958).length < 2 ^ (prefixWord ++ tailWord_2691958).sum := by decide
  have hdescent : baseEnd_2691958 < baseStart_2691958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2691975 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 2, 3]
def baseStart_2691975 : Nat := 118140960795 + 2691975 * 2 ^ 59
def prefixEnd_2691975 : Nat := 4983230072969 + 3 ^ 40 * 2691975 * 2
def baseEnd_2691975 : Nat := 921518056591473579421559

theorem tailTrace_2691975 : CollatzResearch.WordTrace tailWord_2691975 prefixEnd_2691975 921518056591473579421559 := by
  unfold tailWord_2691975
  simp only [CollatzResearch.WordTrace]
  refine ⟨98184394422441802572325379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65456262948294535048216919 98184394422441802572325379)
  ·
    refine ⟨147276591633662703858488069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98184394422441802572325379 147276591633662703858488069)
    ·
      refine ⟨27614360931311756973466513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147276591633662703858488069 27614360931311756973466513)
      ·
        refine ⟨20710770698483817730099885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27614360931311756973466513 20710770698483817730099885)
        ·
          refine ⟨7766539011931431648787457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20710770698483817730099885 7766539011931431648787457)
          ·
            refine ⟨5824904258948573736590593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7766539011931431648787457 5824904258948573736590593)
            ·
              refine ⟨4368678194211430302442945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824904258948573736590593 4368678194211430302442945)
              ·
                refine ⟨3276508645658572726832209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4368678194211430302442945 3276508645658572726832209)
                ·
                  refine ⟨2457381484243929545124157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3276508645658572726832209 2457381484243929545124157)
                  ·
                    refine ⟨921518056591473579421559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2457381484243929545124157 921518056591473579421559)
                    ·
                      rfl

theorem cell22_2691975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_2691975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2691975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2691975 prefixEnd_2691975 := by exact prefixLift 2691975
  have htrace : WordTrace (prefixWord ++ tailWord_2691975) baseStart_2691975 baseEnd_2691975 := by
    simpa [prefixWord, tailWord_2691975, baseEnd_2691975] using wordTrace_append hprefix tailTrace_2691975
  have hstable : (prefixWord ++ tailWord_2691975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2691975).length < 2 ^ (prefixWord ++ tailWord_2691975).sum := by decide
  have hdescent : baseEnd_2691975 < baseStart_2691975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2691975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692007 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2692007 : Nat := 118140960795 + 2692007 * 2 ^ 59
def prefixEnd_2692007 : Nat := 4983230072969 + 3 ^ 40 * 2692007 * 2
def baseEnd_2692007 : Nat := 921529010845436162621461

theorem tailTrace_2692007 : CollatzResearch.WordTrace tailWord_2692007 prefixEnd_2692007 921529010845436162621461 := by
  unfold tailWord_2692007
  simp only [CollatzResearch.WordTrace]
  refine ⟨98185561558325872037490275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65457041038883914691660183 98185561558325872037490275)
  ·
    refine ⟨147278342337488808056235413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98185561558325872037490275 147278342337488808056235413)
    ·
      refine ⟨6903672297069787877636035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147278342337488808056235413 6903672297069787877636035)
      ·
        refine ⟨10355508445604681816454053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903672297069787877636035 10355508445604681816454053)
        ·
          refine ⟨1941657833550877840585135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10355508445604681816454053 1941657833550877840585135)
          ·
            refine ⟨2912486750326316760877703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941657833550877840585135 2912486750326316760877703)
            ·
              refine ⟨4368730125489475141316555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912486750326316760877703 4368730125489475141316555)
              ·
                refine ⟨6553095188234212711974833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368730125489475141316555 6553095188234212711974833)
                ·
                  refine ⟨4914821391175659533981125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6553095188234212711974833 4914821391175659533981125)
                  ·
                    refine ⟨921529010845436162621461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4914821391175659533981125 921529010845436162621461)
                    ·
                      rfl

theorem cell22_2692007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2692007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692007 prefixEnd_2692007 := by exact prefixLift 2692007
  have htrace : WordTrace (prefixWord ++ tailWord_2692007) baseStart_2692007 baseEnd_2692007 := by
    simpa [prefixWord, tailWord_2692007, baseEnd_2692007] using wordTrace_append hprefix tailTrace_2692007
  have hstable : (prefixWord ++ tailWord_2692007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692007).length < 2 ^ (prefixWord ++ tailWord_2692007).sum := by decide
  have hdescent : baseEnd_2692007 < baseStart_2692007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692022 : List Nat := [5, 1, 4, 1, 1, 1, 9]
def baseStart_2692022 : Nat := 118140960795 + 2692022 * 2 ^ 59
def prefixEnd_2692022 : Nat := 4983230072969 + 3 ^ 40 * 2692022 * 2
def baseEnd_2692022 : Nat := 34130894283406708277645

theorem tailTrace_2692022 : CollatzResearch.WordTrace tailWord_2692022 prefixEnd_2692022 34130894283406708277645 := by
  unfold tailWord_2692022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136631790829470599955395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65457405768847686399524213 6136631790829470599955395)
  ·
    refine ⟨9204947686244205899933093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6136631790829470599955395 9204947686244205899933093)
    ·
      refine ⟨1725927691170788606237455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9204947686244205899933093 1725927691170788606237455)
      ·
        refine ⟨2588891536756182909356183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725927691170788606237455 2588891536756182909356183)
        ·
          refine ⟨3883337305134274364034275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588891536756182909356183 3883337305134274364034275)
          ·
            refine ⟨5825005957701411546051413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883337305134274364034275 5825005957701411546051413)
            ·
              refine ⟨34130894283406708277645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5825005957701411546051413 34130894283406708277645)
              ·
                rfl

theorem cell22_2692022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 9].length) (baseStart_2692022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692022 prefixEnd_2692022 := by exact prefixLift 2692022
  have htrace : WordTrace (prefixWord ++ tailWord_2692022) baseStart_2692022 baseEnd_2692022 := by
    simpa [prefixWord, tailWord_2692022, baseEnd_2692022] using wordTrace_append hprefix tailTrace_2692022
  have hstable : (prefixWord ++ tailWord_2692022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692022).length < 2 ^ (prefixWord ++ tailWord_2692022).sum := by decide
  have hdescent : baseEnd_2692022 < baseStart_2692022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692114 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2692114 : Nat := 118140960795 + 2692114 * 2 ^ 59
def prefixEnd_2692114 : Nat := 4983230072969 + 3 ^ 40 * 2692114 * 2
def baseEnd_2692114 : Nat := 921565639132123550196133

theorem tailTrace_2692114 : CollatzResearch.WordTrace tailWord_2692114 prefixEnd_2692114 921565639132123550196133 := by
  unfold tailWord_2692114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24547366042234557327908849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65459642779292152874423597 24547366042234557327908849)
  ·
    refine ⟨18410524531675917995931637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24547366042234557327908849 18410524531675917995931637)
    ·
      refine ⟨1725986674844617312118591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18410524531675917995931637 1725986674844617312118591)
      ·
        refine ⟨2588980012266925968177887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725986674844617312118591 2588980012266925968177887)
        ·
          refine ⟨3883470018400388952266831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588980012266925968177887 3883470018400388952266831)
          ·
            refine ⟨5825205027600583428400247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883470018400388952266831 5825205027600583428400247)
            ·
              refine ⟨8737807541400875142600371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5825205027600583428400247 8737807541400875142600371)
              ·
                refine ⟨13106711312101312713900557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8737807541400875142600371 13106711312101312713900557)
                ·
                  refine ⟨4915016742037992267712709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13106711312101312713900557 4915016742037992267712709)
                  ·
                    refine ⟨921565639132123550196133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915016742037992267712709 921565639132123550196133)
                    ·
                      rfl

theorem cell22_2692114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2692114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692114 prefixEnd_2692114 := by exact prefixLift 2692114
  have htrace : WordTrace (prefixWord ++ tailWord_2692114) baseStart_2692114 baseEnd_2692114 := by
    simpa [prefixWord, tailWord_2692114, baseEnd_2692114] using wordTrace_append hprefix tailTrace_2692114
  have hstable : (prefixWord ++ tailWord_2692114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692114).length < 2 ^ (prefixWord ++ tailWord_2692114).sum := by decide
  have hdescent : baseEnd_2692114 < baseStart_2692114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692121 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_2692121 : Nat := 118140960795 + 2692121 * 2 ^ 59
def prefixEnd_2692121 : Nat := 4983230072969 + 3 ^ 40 * 2692121 * 2
def baseEnd_2692121 : Nat := 921568035375177865271111

theorem tailTrace_2692121 : CollatzResearch.WordTrace tailWord_2692121 prefixEnd_2692121 921568035375177865271111 := by
  unfold tailWord_2692121
  simp only [CollatzResearch.WordTrace]
  refine ⟨98189719479912869507140217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65459812986608579671426811 98189719479912869507140217)
  ·
    refine ⟨73642289609934652130355163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98189719479912869507140217 73642289609934652130355163)
    ·
      refine ⟨110463434414901978195532745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73642289609934652130355163 110463434414901978195532745)
      ·
        refine ⟨82847575811176483646649559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110463434414901978195532745 82847575811176483646649559)
        ·
          refine ⟨124271363716764725469974339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82847575811176483646649559 124271363716764725469974339)
          ·
            refine ⟨186407045575147088204961509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124271363716764725469974339 186407045575147088204961509)
            ·
              refine ⟨34951321045340079038430283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186407045575147088204961509 34951321045340079038430283)
              ·
                refine ⟨52426981568010118557645425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34951321045340079038430283 52426981568010118557645425)
                ·
                  refine ⟨39320236176007588918234069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52426981568010118557645425 39320236176007588918234069)
                  ·
                    refine ⟨921568035375177865271111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39320236176007588918234069 921568035375177865271111)
                    ·
                      rfl

theorem cell22_2692121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_2692121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692121 prefixEnd_2692121 := by exact prefixLift 2692121
  have htrace : WordTrace (prefixWord ++ tailWord_2692121) baseStart_2692121 baseEnd_2692121 := by
    simpa [prefixWord, tailWord_2692121, baseEnd_2692121] using wordTrace_append hprefix tailTrace_2692121
  have hstable : (prefixWord ++ tailWord_2692121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692121).length < 2 ^ (prefixWord ++ tailWord_2692121).sum := by decide
  have hdescent : baseEnd_2692121 < baseStart_2692121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692153 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_2692153 : Nat := 118140960795 + 2692153 * 2 ^ 59
def prefixEnd_2692153 : Nat := 4983230072969 + 3 ^ 40 * 2692153 * 2
def baseEnd_2692153 : Nat := 921578989629140448471013

theorem tailTrace_2692153 : CollatzResearch.WordTrace tailWord_2692153 prefixEnd_2692153 921578989629140448471013 := by
  unfold tailWord_2692153
  simp only [CollatzResearch.WordTrace]
  refine ⟨98190886615796938972305113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65460591077197959314870075 98190886615796938972305113)
  ·
    refine ⟨73643164961847704229228835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98190886615796938972305113 73643164961847704229228835)
    ·
      refine ⟨110464747442771556343843253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73643164961847704229228835 110464747442771556343843253)
      ·
        refine ⟨10356070072759833407235305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110464747442771556343843253 10356070072759833407235305)
        ·
          refine ⟨7767052554569875055426479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10356070072759833407235305 7767052554569875055426479)
          ·
            refine ⟨11650578831854812583139719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767052554569875055426479 11650578831854812583139719)
            ·
              refine ⟨17475868247782218874709579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11650578831854812583139719 17475868247782218874709579)
              ·
                refine ⟨26213802371673328312064369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17475868247782218874709579 26213802371673328312064369)
                ·
                  refine ⟨19660351778754996234048277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26213802371673328312064369 19660351778754996234048277)
                  ·
                    refine ⟨921578989629140448471013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19660351778754996234048277 921578989629140448471013)
                    ·
                      rfl

theorem cell22_2692153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_2692153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692153 prefixEnd_2692153 := by exact prefixLift 2692153
  have htrace : WordTrace (prefixWord ++ tailWord_2692153) baseStart_2692153 baseEnd_2692153 := by
    simpa [prefixWord, tailWord_2692153, baseEnd_2692153] using wordTrace_append hprefix tailTrace_2692153
  have hstable : (prefixWord ++ tailWord_2692153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692153).length < 2 ^ (prefixWord ++ tailWord_2692153).sum := by decide
  have hdescent : baseEnd_2692153 < baseStart_2692153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692168 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_2692168 : Nat := 118140960795 + 2692168 * 2 ^ 59
def prefixEnd_2692168 : Nat := 4983230072969 + 3 ^ 40 * 2692168 * 2
def baseEnd_2692168 : Nat := 307194708145228469781989

theorem tailTrace_2692168 : CollatzResearch.WordTrace tailWord_2692168 prefixEnd_2692168 307194708145228469781989 := by
  unfold tailWord_2692168
  simp only [CollatzResearch.WordTrace]
  refine ⟨49095716855371298267050579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65460955807161731022734105 49095716855371298267050579)
  ·
    refine ⟨73643575283056947400575869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49095716855371298267050579 73643575283056947400575869)
    ·
      refine ⟨27616340731146355275215951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73643575283056947400575869 27616340731146355275215951)
      ·
        refine ⟨41424511096719532912823927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27616340731146355275215951 41424511096719532912823927)
        ·
          refine ⟨62136766645079299369235891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41424511096719532912823927 62136766645079299369235891)
          ·
            refine ⟨93205149967618949053853837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62136766645079299369235891 93205149967618949053853837)
            ·
              refine ⟨34951931237857105895195189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93205149967618949053853837 34951931237857105895195189)
              ·
                refine ⟨3276743553549103677674549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34951931237857105895195189 3276743553549103677674549)
                ·
                  refine ⟨307194708145228469781989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3276743553549103677674549 307194708145228469781989)
                  ·
                    rfl

theorem cell22_2692168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_2692168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692168 prefixEnd_2692168 := by exact prefixLift 2692168
  have htrace : WordTrace (prefixWord ++ tailWord_2692168) baseStart_2692168 baseEnd_2692168 := by
    simpa [prefixWord, tailWord_2692168, baseEnd_2692168] using wordTrace_append hprefix tailTrace_2692168
  have hstable : (prefixWord ++ tailWord_2692168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692168).length < 2 ^ (prefixWord ++ tailWord_2692168).sum := by decide
  have hdescent : baseEnd_2692168 < baseStart_2692168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692202 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_2692202 : Nat := 118140960795 + 2692202 * 2 ^ 59
def prefixEnd_2692202 : Nat := 4983230072969 + 3 ^ 40 * 2692202 * 2
def baseEnd_2692202 : Nat := 307198587776840217998621

theorem tailTrace_2692202 : CollatzResearch.WordTrace tailWord_2692202 prefixEnd_2692202 307198587776840217998621 := by
  unfold tailWord_2692202
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548168448154855085209715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65461782528412946893892573 24548168448154855085209715)
  ·
    refine ⟨36822252672232282627814573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24548168448154855085209715 36822252672232282627814573)
    ·
      refine ⟨13808344752087105985430465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36822252672232282627814573 13808344752087105985430465)
      ·
        refine ⟨10356258564065329489072849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13808344752087105985430465 10356258564065329489072849)
        ·
          refine ⟨7767193923048997116804637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10356258564065329489072849 7767193923048997116804637)
          ·
            refine ⟨2912697721143373918801739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7767193923048997116804637 2912697721143373918801739)
            ·
              refine ⟨4369046581715060878202609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912697721143373918801739 4369046581715060878202609)
              ·
                refine ⟨3276784936286295658651957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369046581715060878202609 3276784936286295658651957)
                ·
                  refine ⟨307198587776840217998621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3276784936286295658651957 307198587776840217998621)
                  ·
                    rfl

theorem cell22_2692202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_2692202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692202 prefixEnd_2692202 := by exact prefixLift 2692202
  have htrace : WordTrace (prefixWord ++ tailWord_2692202) baseStart_2692202 baseEnd_2692202 := by
    simpa [prefixWord, tailWord_2692202, baseEnd_2692202] using wordTrace_append hprefix tailTrace_2692202
  have hstable : (prefixWord ++ tailWord_2692202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692202).length < 2 ^ (prefixWord ++ tailWord_2692202).sum := by decide
  have hdescent : baseEnd_2692202 < baseStart_2692202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692243 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 6]
def baseStart_2692243 : Nat := 118140960795 + 2692243 * 2 ^ 59
def prefixEnd_2692243 : Nat := 4983230072969 + 3 ^ 40 * 2692243 * 2
def baseEnd_2692243 : Nat := 921609798468410213720737

theorem tailTrace_2692243 : CollatzResearch.WordTrace tailWord_2692243 prefixEnd_2692243 921609798468410213720737 := by
  unfold tailWord_2692243
  simp only [CollatzResearch.WordTrace]
  refine ⟨98194169185470884343081383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65462779456980589562054255 98194169185470884343081383)
  ·
    refine ⟨147291253778206326514622075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98194169185470884343081383 147291253778206326514622075)
    ·
      refine ⟨220936880667309489771933113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147291253778206326514622075 220936880667309489771933113)
      ·
        refine ⟨165702660500482117328949835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220936880667309489771933113 165702660500482117328949835)
        ·
          refine ⟨248553990750723175993424753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165702660500482117328949835 248553990750723175993424753)
          ·
            refine ⟨186415493063042381995068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248553990750723175993424753 186415493063042381995068565)
            ·
              refine ⟨8738226237330111656018839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 186415493063042381995068565 8738226237330111656018839)
              ·
                refine ⟨13107339355995167484028259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8738226237330111656018839 13107339355995167484028259)
                ·
                  refine ⟨19661009033992751226042389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13107339355995167484028259 19661009033992751226042389)
                  ·
                    refine ⟨921609798468410213720737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19661009033992751226042389 921609798468410213720737)
                    ·
                      rfl

theorem cell22_2692243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_2692243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692243 prefixEnd_2692243 := by exact prefixLift 2692243
  have htrace : WordTrace (prefixWord ++ tailWord_2692243) baseStart_2692243 baseEnd_2692243 := by
    simpa [prefixWord, tailWord_2692243, baseEnd_2692243] using wordTrace_append hprefix tailTrace_2692243
  have hstable : (prefixWord ++ tailWord_2692243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692243).length < 2 ^ (prefixWord ++ tailWord_2692243).sum := by decide
  have hdescent : baseEnd_2692243 < baseStart_2692243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692247 : List Nat := [1, 1, 3, 3, 3, 1, 3, 3, 4]
def baseStart_2692247 : Nat := 118140960795 + 2692247 * 2 ^ 59
def prefixEnd_2692247 : Nat := 4983230072969 + 3 ^ 40 * 2692247 * 2
def baseEnd_2692247 : Nat := 307203722583385178873575

theorem tailTrace_2692247 : CollatzResearch.WordTrace tailWord_2692247 prefixEnd_2692247 307203722583385178873575 := by
  unfold tailWord_2692247
  simp only [CollatzResearch.WordTrace]
  refine ⟨98194315077456393026226995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65462876718304262017484663 98194315077456393026226995)
  ·
    refine ⟨147291472616184589539340493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98194315077456393026226995 147291472616184589539340493)
    ·
      refine ⟨55234302231069221077252685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147291472616184589539340493 55234302231069221077252685)
      ·
        refine ⟨20712863336650957903969757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55234302231069221077252685 20712863336650957903969757)
        ·
          refine ⟨7767323751244109213988659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20712863336650957903969757 7767323751244109213988659)
          ·
            refine ⟨11650985626866163820982989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767323751244109213988659 11650985626866163820982989)
            ·
              refine ⟨4369119610074811432868621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11650985626866163820982989 4369119610074811432868621)
              ·
                refine ⟨1638419853778054287325733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369119610074811432868621 1638419853778054287325733)
                ·
                  refine ⟨307203722583385178873575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638419853778054287325733 307203722583385178873575)
                  ·
                    rfl

theorem cell22_2692247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 4].length) (baseStart_2692247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692247 prefixEnd_2692247 := by exact prefixLift 2692247
  have htrace : WordTrace (prefixWord ++ tailWord_2692247) baseStart_2692247 baseEnd_2692247 := by
    simpa [prefixWord, tailWord_2692247, baseEnd_2692247] using wordTrace_append hprefix tailTrace_2692247
  have hstable : (prefixWord ++ tailWord_2692247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692247).length < 2 ^ (prefixWord ++ tailWord_2692247).sum := by decide
  have hdescent : baseEnd_2692247 < baseStart_2692247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692260 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_2692260 : Nat := 118140960795 + 2692260 * 2 ^ 59
def prefixEnd_2692260 : Nat := 4983230072969 + 3 ^ 40 * 2692260 * 2
def baseEnd_2692260 : Nat := 921615617915827836045685

theorem tailTrace_2692260 : CollatzResearch.WordTrace tailWord_2692260 prefixEnd_2692260 921615617915827836045685 := by
  unfold tailWord_2692260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49097394613204648123225117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65463192817606197497633489 49097394613204648123225117)
  ·
    refine ⟨18411522979951743046209419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49097394613204648123225117 18411522979951743046209419)
    ·
      refine ⟨27617284469927614569314129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18411522979951743046209419 27617284469927614569314129)
      ·
        refine ⟨20712963352445710926985597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27617284469927614569314129 20712963352445710926985597)
        ·
          refine ⟨7767361257167141597619599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20712963352445710926985597 7767361257167141597619599)
          ·
            refine ⟨11651041885750712396429399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7767361257167141597619599 11651041885750712396429399)
            ·
              refine ⟨17476562828626068594644099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651041885750712396429399 17476562828626068594644099)
              ·
                refine ⟨26214844242939102891966149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17476562828626068594644099 26214844242939102891966149)
                ·
                  refine ⟨4915283295551081792243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26214844242939102891966149 4915283295551081792243653)
                  ·
                    refine ⟨921615617915827836045685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915283295551081792243653 921615617915827836045685)
                    ·
                      rfl

theorem cell22_2692260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_2692260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692260 prefixEnd_2692260 := by exact prefixLift 2692260
  have htrace : WordTrace (prefixWord ++ tailWord_2692260) baseStart_2692260 baseEnd_2692260 := by
    simpa [prefixWord, tailWord_2692260, baseEnd_2692260] using wordTrace_append hprefix tailTrace_2692260
  have hstable : (prefixWord ++ tailWord_2692260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692260).length < 2 ^ (prefixWord ++ tailWord_2692260).sum := by decide
  have hdescent : baseEnd_2692260 < baseStart_2692260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692303 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 7]
def baseStart_2692303 : Nat := 118140960795 + 2692303 * 2 ^ 59
def prefixEnd_2692303 : Nat := 4983230072969 + 3 ^ 40 * 2692303 * 2
def baseEnd_2692303 : Nat := 307210112564863352406851

theorem tailTrace_2692303 : CollatzResearch.WordTrace tailWord_2692303 prefixEnd_2692303 307210112564863352406851 := by
  unfold tailWord_2692303
  simp only [CollatzResearch.WordTrace]
  refine ⟨98196357565253514590265563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65464238376835676393510375 98196357565253514590265563)
  ·
    refine ⟨147294536347880271885398345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98196357565253514590265563 147294536347880271885398345)
    ·
      refine ⟨110470902260910203914048759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147294536347880271885398345 110470902260910203914048759)
      ·
        refine ⟨165706353391365305871073139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110470902260910203914048759 165706353391365305871073139)
        ·
          refine ⟨248559530087047958806609709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165706353391365305871073139 248559530087047958806609709)
          ·
            refine ⟨93209823782642984552478641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248559530087047958806609709 93209823782642984552478641)
            ·
              refine ⟨69907367836982238414358981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93209823782642984552478641 69907367836982238414358981)
              ·
                refine ⟨13107631469434169702692309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69907367836982238414358981 13107631469434169702692309)
                ·
                  refine ⟨307210112564863352406851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13107631469434169702692309 307210112564863352406851)
                  ·
                    rfl

theorem cell22_2692303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 7].length) (baseStart_2692303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692303 prefixEnd_2692303 := by exact prefixLift 2692303
  have htrace : WordTrace (prefixWord ++ tailWord_2692303) baseStart_2692303 baseEnd_2692303 := by
    simpa [prefixWord, tailWord_2692303, baseEnd_2692303] using wordTrace_append hprefix tailTrace_2692303
  have hstable : (prefixWord ++ tailWord_2692303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692303).length < 2 ^ (prefixWord ++ tailWord_2692303).sum := by decide
  have hdescent : baseEnd_2692303 < baseStart_2692303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692320 : List Nat := [2, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_2692320 : Nat := 118140960795 + 2692320 * 2 ^ 59
def prefixEnd_2692320 : Nat := 4983230072969 + 3 ^ 40 * 2692320 * 2
def baseEnd_2692320 : Nat := 307212052380669226515167

theorem tailTrace_2692320 : CollatzResearch.WordTrace tailWord_2692320 prefixEnd_2692320 307212052380669226515167 := by
  unfold tailWord_2692320
  simp only [CollatzResearch.WordTrace]
  refine ⟨49098488803095963246817207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65464651737461284329089609 49098488803095963246817207)
  ·
    refine ⟨73647733204643944870225811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49098488803095963246817207 73647733204643944870225811)
    ·
      refine ⟨110471599806965917305338717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73647733204643944870225811 110471599806965917305338717)
      ·
        refine ⟨41426849927612218989502019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110471599806965917305338717 41426849927612218989502019)
        ·
          refine ⟨62140274891418328484253029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41426849927612218989502019 62140274891418328484253029)
          ·
            refine ⟨11651301542140936590797443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62140274891418328484253029 11651301542140936590797443)
            ·
              refine ⟨17476952313211404886196165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11651301542140936590797443 17476952313211404886196165)
              ·
                refine ⟨3276928558727138416161781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17476952313211404886196165 3276928558727138416161781)
                ·
                  refine ⟨307212052380669226515167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3276928558727138416161781 307212052380669226515167)
                  ·
                    rfl

theorem cell22_2692320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_2692320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692320 prefixEnd_2692320 := by exact prefixLift 2692320
  have htrace : WordTrace (prefixWord ++ tailWord_2692320) baseStart_2692320 baseEnd_2692320 := by
    simpa [prefixWord, tailWord_2692320, baseEnd_2692320] using wordTrace_append hprefix tailTrace_2692320
  have hstable : (prefixWord ++ tailWord_2692320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692320).length < 2 ^ (prefixWord ++ tailWord_2692320).sum := by decide
  have hdescent : baseEnd_2692320 < baseStart_2692320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692380 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2692380 : Nat := 118140960795 + 2692380 * 2 ^ 59
def prefixEnd_2692380 : Nat := 4983230072969 + 3 ^ 40 * 2692380 * 2
def baseEnd_2692380 : Nat := 921656696368187523045317

theorem tailTrace_2692380 : CollatzResearch.WordTrace tailWord_2692380 prefixEnd_2692380 921656696368187523045317 := by
  unfold tailWord_2692380
  simp only [CollatzResearch.WordTrace]
  refine ⟨49099582992987278370409297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65466110657316371160545729 49099582992987278370409297)
  ·
    refine ⟨36824687244740458777806973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49099582992987278370409297 36824687244740458777806973)
    ·
      refine ⟨13809257716777672041677615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36824687244740458777806973 13809257716777672041677615)
      ·
        refine ⟨20713886575166508062516423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13809257716777672041677615 20713886575166508062516423)
        ·
          refine ⟨31070829862749762093774635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20713886575166508062516423 31070829862749762093774635)
          ·
            refine ⟨46606244794124643140661953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31070829862749762093774635 46606244794124643140661953)
            ·
              refine ⟨34954683595593482355496465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46606244794124643140661953 34954683595593482355496465)
              ·
                refine ⟨26216012696695111766622349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34954683595593482355496465 26216012696695111766622349)
                ·
                  refine ⟨9831004761260666912483381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26216012696695111766622349 9831004761260666912483381)
                  ·
                    refine ⟨921656696368187523045317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9831004761260666912483381 921656696368187523045317)
                    ·
                      rfl

theorem cell22_2692380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2692380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692380 prefixEnd_2692380 := by exact prefixLift 2692380
  have htrace : WordTrace (prefixWord ++ tailWord_2692380) baseStart_2692380 baseEnd_2692380 := by
    simpa [prefixWord, tailWord_2692380, baseEnd_2692380] using wordTrace_append hprefix tailTrace_2692380
  have hstable : (prefixWord ++ tailWord_2692380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692380).length < 2 ^ (prefixWord ++ tailWord_2692380).sum := by decide
  have hdescent : baseEnd_2692380 < baseStart_2692380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692410 : List Nat := [3, 1, 1, 1, 4, 1, 3, 8]
def baseStart_2692410 : Nat := 118140960795 + 2692410 * 2 ^ 59
def prefixEnd_2692410 : Nat := 4983230072969 + 3 ^ 40 * 2692410 * 2
def baseEnd_2692410 : Nat := 102407440664586382755025

theorem tailTrace_2692410 : CollatzResearch.WordTrace tailWord_2692410 prefixEnd_2692410 102407440664586382755025 := by
  unfold tailWord_2692410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24550065043966467966102671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65466840117243914576273789 24550065043966467966102671)
  ·
    refine ⟨36825097565949701949154007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24550065043966467966102671 36825097565949701949154007)
    ·
      refine ⟨55237646348924552923731011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36825097565949701949154007 55237646348924552923731011)
      ·
        refine ⟨82856469523386829385596517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55237646348924552923731011 82856469523386829385596517)
        ·
          refine ⟨15535588035635030509799347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82856469523386829385596517 15535588035635030509799347)
          ·
            refine ⟨23303382053452545764699021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15535588035635030509799347 23303382053452545764699021)
            ·
              refine ⟨8738768270044704661762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23303382053452545764699021 8738768270044704661762133)
              ·
                refine ⟨102407440664586382755025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8738768270044704661762133 102407440664586382755025)
                ·
                  rfl

theorem cell22_2692410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_2692410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692410 prefixEnd_2692410 := by exact prefixLift 2692410
  have htrace : WordTrace (prefixWord ++ tailWord_2692410) baseStart_2692410 baseEnd_2692410 := by
    simpa [prefixWord, tailWord_2692410, baseEnd_2692410] using wordTrace_append hprefix tailTrace_2692410
  have hstable : (prefixWord ++ tailWord_2692410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692410).length < 2 ^ (prefixWord ++ tailWord_2692410).sum := by decide
  have hdescent : baseEnd_2692410 < baseStart_2692410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692440 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2692440 : Nat := 118140960795 + 2692440 * 2 ^ 59
def prefixEnd_2692440 : Nat := 4983230072969 + 3 ^ 40 * 2692440 * 2
def baseEnd_2692440 : Nat := 921677235594367366545133

theorem tailTrace_2692440 : CollatzResearch.WordTrace tailWord_2692440 prefixEnd_2692440 921677235594367366545133 := by
  unfold tailWord_2692440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49100677182878593494001387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65467569577171457992001849 49100677182878593494001387)
  ·
    refine ⟨73651015774317890241002081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49100677182878593494001387 73651015774317890241002081)
    ·
      refine ⟨55238261830738417680751561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73651015774317890241002081 55238261830738417680751561)
      ·
        refine ⟨41428696373053813260563671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55238261830738417680751561 41428696373053813260563671)
        ·
          refine ⟨62143044559580719890845507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41428696373053813260563671 62143044559580719890845507)
          ·
            refine ⟨93214566839371079836268261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62143044559580719890845507 93214566839371079836268261)
            ·
              refine ⟨17477731282382077469300299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93214566839371079836268261 17477731282382077469300299)
              ·
                refine ⟨26216596923573116203950449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17477731282382077469300299 26216596923573116203950449)
                ·
                  refine ⟨19662447692679837152962837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26216596923573116203950449 19662447692679837152962837)
                  ·
                    refine ⟨921677235594367366545133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19662447692679837152962837 921677235594367366545133)
                    ·
                      rfl

theorem cell22_2692440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2692440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692440 prefixEnd_2692440 := by exact prefixLift 2692440
  have htrace : WordTrace (prefixWord ++ tailWord_2692440) baseStart_2692440 baseEnd_2692440 := by
    simpa [prefixWord, tailWord_2692440, baseEnd_2692440] using wordTrace_append hprefix tailTrace_2692440
  have hstable : (prefixWord ++ tailWord_2692440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692440).length < 2 ^ (prefixWord ++ tailWord_2692440).sum := by decide
  have hdescent : baseEnd_2692440 < baseStart_2692440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692489 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 5]
def baseStart_2692489 : Nat := 118140960795 + 2692489 * 2 ^ 59
def prefixEnd_2692489 : Nat := 4983230072969 + 3 ^ 40 * 2692489 * 2
def baseEnd_2692489 : Nat := 307231336431915857356661

theorem tailTrace_2692489 : CollatzResearch.WordTrace tailWord_2692489 prefixEnd_2692489 307231336431915857356661 := by
  unfold tailWord_2692489
  simp only [CollatzResearch.WordTrace]
  refine ⟨98203141542579668356536521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65468761028386445571024347 98203141542579668356536521)
  ·
    refine ⟨73652356156934751267402391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98203141542579668356536521 73652356156934751267402391)
    ·
      refine ⟨110478534235402126901103587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73652356156934751267402391 110478534235402126901103587)
      ·
        refine ⟨165717801353103190351655381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110478534235402126901103587 165717801353103190351655381)
        ·
          refine ⟨3884010969213356023866923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 165717801353103190351655381 3884010969213356023866923)
          ·
            refine ⟨5826016453820034035800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884010969213356023866923 5826016453820034035800385)
            ·
              refine ⟨4369512340365025526850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5826016453820034035800385 4369512340365025526850289)
              ·
                refine ⟨3277134255273769145137717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4369512340365025526850289 3277134255273769145137717)
                ·
                  refine ⟨307231336431915857356661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277134255273769145137717 307231336431915857356661)
                  ·
                    rfl

theorem cell22_2692489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_2692489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692489 prefixEnd_2692489 := by exact prefixLift 2692489
  have htrace : WordTrace (prefixWord ++ tailWord_2692489) baseStart_2692489 baseEnd_2692489 := by
    simpa [prefixWord, tailWord_2692489, baseEnd_2692489] using wordTrace_append hprefix tailTrace_2692489
  have hstable : (prefixWord ++ tailWord_2692489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692489).length < 2 ^ (prefixWord ++ tailWord_2692489).sum := by decide
  have hdescent : baseEnd_2692489 < baseStart_2692489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692504 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_2692504 : Nat := 118140960795 + 2692504 * 2 ^ 59
def prefixEnd_2692504 : Nat := 4983230072969 + 3 ^ 40 * 2692504 * 2
def baseEnd_2692504 : Nat := 921699144102292532944937

theorem tailTrace_2692504 : CollatzResearch.WordTrace tailWord_2692504 prefixEnd_2692504 921699144102292532944937 := by
  unfold tailWord_2692504
  simp only [CollatzResearch.WordTrace]
  refine ⟨49101844318762662959166283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65469125758350217278888377 49101844318762662959166283)
  ·
    refine ⟨73652766478143994438749425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49101844318762662959166283 73652766478143994438749425)
    ·
      refine ⟨55239574858607995829062069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73652766478143994438749425 55239574858607995829062069)
      ·
        refine ⟨5178710142994499608974569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55239574858607995829062069 5178710142994499608974569)
        ·
          refine ⟨3884032607245874706730927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5178710142994499608974569 3884032607245874706730927)
          ·
            refine ⟨5826048910868812060096391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884032607245874706730927 5826048910868812060096391)
            ·
              refine ⟨8739073366303218090144587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826048910868812060096391 8739073366303218090144587)
              ·
                refine ⟨13108610049454827135216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739073366303218090144587 13108610049454827135216881)
                ·
                  refine ⟨9831457537091120351412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13108610049454827135216881 9831457537091120351412661)
                  ·
                    refine ⟨921699144102292532944937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9831457537091120351412661 921699144102292532944937)
                    ·
                      rfl

theorem cell22_2692504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_2692504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692504 prefixEnd_2692504 := by exact prefixLift 2692504
  have htrace : WordTrace (prefixWord ++ tailWord_2692504) baseStart_2692504 baseEnd_2692504 := by
    simpa [prefixWord, tailWord_2692504, baseEnd_2692504] using wordTrace_append hprefix tailTrace_2692504
  have hstable : (prefixWord ++ tailWord_2692504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692504).length < 2 ^ (prefixWord ++ tailWord_2692504).sum := by decide
  have hdescent : baseEnd_2692504 < baseStart_2692504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692519 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2692519 : Nat := 118140960795 + 2692519 * 2 ^ 59
def prefixEnd_2692519 : Nat := 4983230072969 + 3 ^ 40 * 2692519 * 2
def baseEnd_2692519 : Nat := 921704278908837493819891

theorem tailTrace_2692519 : CollatzResearch.WordTrace tailWord_2692519 prefixEnd_2692519 921704278908837493819891 := by
  unfold tailWord_2692519
  simp only [CollatzResearch.WordTrace]
  refine ⟨98204235732470983480128611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65469490488313988986752407 98204235732470983480128611)
  ·
    refine ⟨147306353598706475220192917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98204235732470983480128611 147306353598706475220192917)
    ·
      refine ⟨6904985324939366025946543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147306353598706475220192917 6904985324939366025946543)
      ·
        refine ⟨10357477987409049038919815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6904985324939366025946543 10357477987409049038919815)
        ·
          refine ⟨15536216981113573558379723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357477987409049038919815 15536216981113573558379723)
          ·
            refine ⟨23304325471670360337569585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15536216981113573558379723 23304325471670360337569585)
            ·
              refine ⟨17478244103752770253177189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23304325471670360337569585 17478244103752770253177189)
              ·
                refine ⟨3277170769453644422470723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17478244103752770253177189 3277170769453644422470723)
                ·
                  refine ⟨4915756154180466633706085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277170769453644422470723 4915756154180466633706085)
                  ·
                    refine ⟨921704278908837493819891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915756154180466633706085 921704278908837493819891)
                    ·
                      rfl

theorem cell22_2692519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2692519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692519 prefixEnd_2692519 := by exact prefixLift 2692519
  have htrace : WordTrace (prefixWord ++ tailWord_2692519) baseStart_2692519 baseEnd_2692519 := by
    simpa [prefixWord, tailWord_2692519, baseEnd_2692519] using wordTrace_append hprefix tailTrace_2692519
  have hstable : (prefixWord ++ tailWord_2692519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692519).length < 2 ^ (prefixWord ++ tailWord_2692519).sum := by decide
  have hdescent : baseEnd_2692519 < baseStart_2692519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692547 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 2, 4]
def baseStart_2692547 : Nat := 118140960795 + 2692547 * 2 ^ 59
def prefixEnd_2692547 : Nat := 4983230072969 + 3 ^ 40 * 2692547 * 2
def baseEnd_2692547 : Nat := 921713863881054754119805

theorem tailTrace_2692547 : CollatzResearch.WordTrace tailWord_2692547 prefixEnd_2692547 921713863881054754119805 := by
  unfold tailWord_2692547
  simp only [CollatzResearch.WordTrace]
  refine ⟨98205256976369544262147895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65470171317579696174765263 98205256976369544262147895)
  ·
    refine ⟨147307885464554316393221843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98205256976369544262147895 147307885464554316393221843)
    ·
      refine ⟨220961828196831474589832765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147307885464554316393221843 220961828196831474589832765)
      ·
        refine ⟨82860685573811802971187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220961828196831474589832765 82860685573811802971187287)
        ·
          refine ⟨124291028360717704456780931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82860685573811802971187287 124291028360717704456780931)
          ·
            refine ⟨186436542541076556685171397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124291028360717704456780931 186436542541076556685171397)
            ·
              refine ⟨34956851726451854378469637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186436542541076556685171397 34956851726451854378469637)
              ·
                refine ⟨6554409698709722695963057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34956851726451854378469637 6554409698709722695963057)
                ·
                  refine ⟨4915807274032292021972293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6554409698709722695963057 4915807274032292021972293)
                  ·
                    refine ⟨921713863881054754119805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4915807274032292021972293 921713863881054754119805)
                    ·
                      rfl

theorem cell22_2692547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_2692547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692547 prefixEnd_2692547 := by exact prefixLift 2692547
  have htrace : WordTrace (prefixWord ++ tailWord_2692547) baseStart_2692547 baseEnd_2692547 := by
    simpa [prefixWord, tailWord_2692547, baseEnd_2692547] using wordTrace_append hprefix tailTrace_2692547
  have hstable : (prefixWord ++ tailWord_2692547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692547).length < 2 ^ (prefixWord ++ tailWord_2692547).sum := by decide
  have hdescent : baseEnd_2692547 < baseStart_2692547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692566 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2692566 : Nat := 118140960795 + 2692566 * 2 ^ 59
def prefixEnd_2692566 : Nat := 4983230072969 + 3 ^ 40 * 2692566 * 2
def baseEnd_2692566 : Nat := 921720367969345037894747

theorem tailTrace_2692566 : CollatzResearch.WordTrace tailWord_2692566 prefixEnd_2692566 921720367969345037894747 := by
  unfold tailWord_2692566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137871872706294406693097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65470633308867140338059701 6137871872706294406693097)
  ·
    refine ⟨4603403904529720805019823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6137871872706294406693097 4603403904529720805019823)
    ·
      refine ⟨6905105856794581207529735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603403904529720805019823 6905105856794581207529735)
      ·
        refine ⟨10357658785191871811294603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905105856794581207529735 10357658785191871811294603)
        ·
          refine ⟨15536488177787807716941905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10357658785191871811294603 15536488177787807716941905)
          ·
            refine ⟨11652366133340855787706429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15536488177787807716941905 11652366133340855787706429)
            ·
              refine ⟨4369637300002820920389911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11652366133340855787706429 4369637300002820920389911)
              ·
                refine ⟨6554455950004231380584867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369637300002820920389911 6554455950004231380584867)
                ·
                  refine ⟨9831683925006347070877301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6554455950004231380584867 9831683925006347070877301)
                  ·
                    refine ⟨921720367969345037894747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9831683925006347070877301 921720367969345037894747)
                    ·
                      rfl

theorem cell22_2692566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2692566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692566 prefixEnd_2692566 := by exact prefixLift 2692566
  have htrace : WordTrace (prefixWord ++ tailWord_2692566) baseStart_2692566 baseEnd_2692566 := by
    simpa [prefixWord, tailWord_2692566, baseEnd_2692566] using wordTrace_append hprefix tailTrace_2692566
  have hstable : (prefixWord ++ tailWord_2692566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692566).length < 2 ^ (prefixWord ++ tailWord_2692566).sum := by decide
  have hdescent : baseEnd_2692566 < baseStart_2692566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692579 : List Nat := [1, 1, 1, 6, 2, 1, 4, 6]
def baseStart_2692579 : Nat := 118140960795 + 2692579 * 2 ^ 59
def prefixEnd_2692579 : Nat := 4983230072969 + 3 ^ 40 * 2692579 * 2
def baseEnd_2692579 : Nat := 102413868681668593035523

theorem tailTrace_2692579 : CollatzResearch.WordTrace tailWord_2692579 prefixEnd_2692579 102413868681668593035523 := by
  unfold tailWord_2692579
  simp only [CollatzResearch.WordTrace]
  refine ⟨98206424112253613727312791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65470949408169075818208527 98206424112253613727312791)
  ·
    refine ⟨147309636168380420590969187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98206424112253613727312791 147309636168380420590969187)
    ·
      refine ⟨220964454252570630886453781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147309636168380420590969187 220964454252570630886453781)
      ·
        refine ⟨10357708793089248322802521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 220964454252570630886453781 10357708793089248322802521)
        ·
          refine ⟨7768281594816936242101891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10357708793089248322802521 7768281594816936242101891)
          ·
            refine ⟨11652422392225404363152837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7768281594816936242101891 11652422392225404363152837)
            ·
              refine ⟨2184829198542263318091157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11652422392225404363152837 2184829198542263318091157)
              ·
                refine ⟨102413868681668593035523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184829198542263318091157 102413868681668593035523)
                ·
                  rfl

theorem cell22_2692579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 6].length) (baseStart_2692579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692579 prefixEnd_2692579 := by exact prefixLift 2692579
  have htrace : WordTrace (prefixWord ++ tailWord_2692579) baseStart_2692579 baseEnd_2692579 := by
    simpa [prefixWord, tailWord_2692579, baseEnd_2692579] using wordTrace_append hprefix tailTrace_2692579
  have hstable : (prefixWord ++ tailWord_2692579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692579).length < 2 ^ (prefixWord ++ tailWord_2692579).sum := by decide
  have hdescent : baseEnd_2692579 < baseStart_2692579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692684 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_2692684 : Nat := 118140960795 + 2692684 * 2 ^ 59
def prefixEnd_2692684 : Nat := 4983230072969 + 3 ^ 40 * 2692684 * 2
def baseEnd_2692684 : Nat := 921760761780832063444385

theorem tailTrace_2692684 : CollatzResearch.WordTrace tailWord_2692684 prefixEnd_2692684 921760761780832063444385 := by
  unfold tailWord_2692684
  simp only [CollatzResearch.WordTrace]
  refine ⟨49105126888436608329942553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65473502517915477773256737 49105126888436608329942553)
  ·
    refine ⟨36828845166327456247456915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49105126888436608329942553 36828845166327456247456915)
    ·
      refine ⟨55243267749491184371185373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36828845166327456247456915 55243267749491184371185373)
      ·
        refine ⟨20716225406059194139194515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55243267749491184371185373 20716225406059194139194515)
        ·
          refine ⟨31074338109088791208791773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20716225406059194139194515 31074338109088791208791773)
          ·
            refine ⟨11652876790908296703296915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31074338109088791208791773 11652876790908296703296915)
            ·
              refine ⟨17479315186362445054945373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11652876790908296703296915 17479315186362445054945373)
              ·
                refine ⟨6554743194885916895604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17479315186362445054945373 6554743194885916895604515)
                ·
                  refine ⟨9832114792328875343406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6554743194885916895604515 9832114792328875343406773)
                  ·
                    refine ⟨921760761780832063444385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9832114792328875343406773 921760761780832063444385)
                    ·
                      rfl

theorem cell22_2692684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_2692684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692684 prefixEnd_2692684 := by exact prefixLift 2692684
  have htrace : WordTrace (prefixWord ++ tailWord_2692684) baseStart_2692684 baseEnd_2692684 := by
    simpa [prefixWord, tailWord_2692684, baseEnd_2692684] using wordTrace_append hprefix tailTrace_2692684
  have hstable : (prefixWord ++ tailWord_2692684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692684).length < 2 ^ (prefixWord ++ tailWord_2692684).sum := by decide
  have hdescent : baseEnd_2692684 < baseStart_2692684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692697 : List Nat := [1, 2, 1, 2, 2, 1, 1, 12]
def baseStart_2692697 : Nat := 118140960795 + 2692697 * 2 ^ 59
def prefixEnd_2692697 : Nat := 4983230072969 + 3 ^ 40 * 2692697 * 2
def baseEnd_2692697 : Nat := 102418356882944929207705

theorem tailTrace_2692697 : CollatzResearch.WordTrace tailWord_2692697 prefixEnd_2692697 102418356882944929207705 := by
  unfold tailWord_2692697
  simp only [CollatzResearch.WordTrace]
  refine ⟨98210727925826119880108345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65473818617217413253405563 98210727925826119880108345)
  ·
    refine ⟨73658045944369589910081259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98210727925826119880108345 73658045944369589910081259)
    ·
      refine ⟨110487068916554384865121889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73658045944369589910081259 110487068916554384865121889)
      ·
        refine ⟨82865301687415788648841417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110487068916554384865121889 82865301687415788648841417)
        ·
          refine ⟨62148976265561841486631063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82865301687415788648841417 62148976265561841486631063)
          ·
            refine ⟨93223464398342762229946595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62148976265561841486631063 93223464398342762229946595)
            ·
              refine ⟨139835196597514143344919893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93223464398342762229946595 139835196597514143344919893)
              ·
                refine ⟨102418356882944929207705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 139835196597514143344919893 102418356882944929207705)
                ·
                  rfl

theorem cell22_2692697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 12].length) (baseStart_2692697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692697 prefixEnd_2692697 := by exact prefixLift 2692697
  have htrace : WordTrace (prefixWord ++ tailWord_2692697) baseStart_2692697 baseEnd_2692697 := by
    simpa [prefixWord, tailWord_2692697, baseEnd_2692697] using wordTrace_append hprefix tailTrace_2692697
  have hstable : (prefixWord ++ tailWord_2692697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692697).length < 2 ^ (prefixWord ++ tailWord_2692697).sum := by decide
  have hdescent : baseEnd_2692697 < baseStart_2692697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692714 : List Nat := [3, 1, 3, 2, 1, 3, 9]
def baseStart_2692714 : Nat := 118140960795 + 2692714 * 2 ^ 59
def prefixEnd_2692714 : Nat := 4983230072969 + 3 ^ 40 * 2692714 * 2
def baseEnd_2692714 : Nat := 34139667829404517970159

theorem tailTrace_2692714 : CollatzResearch.WordTrace tailWord_2692714 prefixEnd_2692714 34139667829404517970159 := by
  unfold tailWord_2692714
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552836991691132945869299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65474231977843021188984797 24552836991691132945869299)
  ·
    refine ⟨36829255487536699418803949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552836991691132945869299 36829255487536699418803949)
    ·
      refine ⟨13810970807826262282051481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36829255487536699418803949 13810970807826262282051481)
      ·
        refine ⟨10358228105869696711538611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13810970807826262282051481 10358228105869696711538611)
        ·
          refine ⟨15537342158804545067307917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10358228105869696711538611 15537342158804545067307917)
          ·
            refine ⟨5826503309551704400240469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15537342158804545067307917 5826503309551704400240469)
            ·
              refine ⟨34139667829404517970159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5826503309551704400240469 34139667829404517970159)
              ·
                rfl

theorem cell22_2692714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 9].length) (baseStart_2692714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692714 prefixEnd_2692714 := by exact prefixLift 2692714
  have htrace : WordTrace (prefixWord ++ tailWord_2692714) baseStart_2692714 baseEnd_2692714 := by
    simpa [prefixWord, tailWord_2692714, baseEnd_2692714] using wordTrace_append hprefix tailTrace_2692714
  have hstable : (prefixWord ++ tailWord_2692714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692714).length < 2 ^ (prefixWord ++ tailWord_2692714).sum := by decide
  have hdescent : baseEnd_2692714 < baseStart_2692714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692718 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2692718 : Nat := 118140960795 + 2692718 * 2 ^ 59
def prefixEnd_2692718 : Nat := 4983230072969 + 3 ^ 40 * 2692718 * 2
def baseEnd_2692718 : Nat := 921772400675667308094281

theorem tailTrace_2692718 : CollatzResearch.WordTrace tailWord_2692718 prefixEnd_2692718 921772400675667308094281 := by
  unfold tailWord_2692718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12276436732343755058327851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65474329239166693644415205 12276436732343755058327851)
  ·
    refine ⟨18414655098515632587491777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12276436732343755058327851 18414655098515632587491777)
    ·
      refine ⟨13810991323886724440618833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18414655098515632587491777 13810991323886724440618833)
      ·
        refine ⟨10358243492915043330464125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13810991323886724440618833 10358243492915043330464125)
        ·
          refine ⟨3884341309843141248924047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10358243492915043330464125 3884341309843141248924047)
          ·
            refine ⟨5826511964764711873386071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3884341309843141248924047 5826511964764711873386071)
            ·
              refine ⟨8739767947147067810079107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5826511964764711873386071 8739767947147067810079107)
              ·
                refine ⟨13109651920720601715118661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8739767947147067810079107 13109651920720601715118661)
                ·
                  refine ⟨2458059735135112821584749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13109651920720601715118661 2458059735135112821584749)
                  ·
                    refine ⟨921772400675667308094281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458059735135112821584749 921772400675667308094281)
                    ·
                      rfl

theorem cell22_2692718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2692718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692718 prefixEnd_2692718 := by exact prefixLift 2692718
  have htrace : WordTrace (prefixWord ++ tailWord_2692718) baseStart_2692718 baseEnd_2692718 := by
    simpa [prefixWord, tailWord_2692718, baseEnd_2692718] using wordTrace_append hprefix tailTrace_2692718
  have hstable : (prefixWord ++ tailWord_2692718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692718).length < 2 ^ (prefixWord ++ tailWord_2692718).sum := by decide
  have hdescent : baseEnd_2692718 < baseStart_2692718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692759 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 7]
def baseStart_2692759 : Nat := 118140960795 + 2692759 * 2 ^ 59
def prefixEnd_2692759 : Nat := 4983230072969 + 3 ^ 40 * 2692759 * 2
def baseEnd_2692759 : Nat := 307262145271185622606385

theorem tailTrace_2692759 : CollatzResearch.WordTrace tailWord_2692759 prefixEnd_2692759 307262145271185622606385 := by
  unfold tailWord_2692759
  simp only [CollatzResearch.WordTrace]
  refine ⟨98212989251601504468865331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65475326167734336312576887 98212989251601504468865331)
  ·
    refine ⟨147319483877402256703297997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98212989251601504468865331 147319483877402256703297997)
    ·
      refine ⟨55244806454025846263736749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147319483877402256703297997 55244806454025846263736749)
      ·
        refine ⟨20716802420259692348901281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55244806454025846263736749 20716802420259692348901281)
        ·
          refine ⟨15537601815194769261675961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20716802420259692348901281 15537601815194769261675961)
          ·
            refine ⟨11653201361396076946256971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15537601815194769261675961 11653201361396076946256971)
            ·
              refine ⟨17479802042094115419385457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11653201361396076946256971 17479802042094115419385457)
              ·
                refine ⟨13109851531570586564539093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17479802042094115419385457 13109851531570586564539093)
                ·
                  refine ⟨307262145271185622606385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13109851531570586564539093 307262145271185622606385)
                  ·
                    rfl

theorem cell22_2692759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 7].length) (baseStart_2692759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692759 prefixEnd_2692759 := by exact prefixLift 2692759
  have htrace : WordTrace (prefixWord ++ tailWord_2692759) baseStart_2692759 baseEnd_2692759 := by
    simpa [prefixWord, tailWord_2692759, baseEnd_2692759] using wordTrace_append hprefix tailTrace_2692759
  have hstable : (prefixWord ++ tailWord_2692759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692759).length < 2 ^ (prefixWord ++ tailWord_2692759).sum := by decide
  have hdescent : baseEnd_2692759 < baseStart_2692759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692823 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 1, 4]
def baseStart_2692823 : Nat := 118140960795 + 2692823 * 2 ^ 59
def prefixEnd_2692823 : Nat := 4983230072969 + 3 ^ 40 * 2692823 * 2
def baseEnd_2692823 : Nat := 921808344321482034218959

theorem tailTrace_2692823 : CollatzResearch.WordTrace tailWord_2692823 prefixEnd_2692823 921808344321482034218959 := by
  unfold tailWord_2692823
  simp only [CollatzResearch.WordTrace]
  refine ⟨98215323523369643399195123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65476882348913095599463415 98215323523369643399195123)
  ·
    refine ⟨147322985285054465098792685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98215323523369643399195123 147322985285054465098792685)
    ·
      refine ⟨55246119481895424412047257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147322985285054465098792685 55246119481895424412047257)
      ·
        refine ⟨41434589611421568309035443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55246119481895424412047257 41434589611421568309035443)
        ·
          refine ⟨62151884417132352463553165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41434589611421568309035443 62151884417132352463553165)
          ·
            refine ⟨23306956656424632173832437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62151884417132352463553165 23306956656424632173832437)
            ·
              refine ⟨2185027186539809266296791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23306956656424632173832437 2185027186539809266296791)
              ·
                refine ⟨3277540779809713899445187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185027186539809266296791 3277540779809713899445187)
                ·
                  refine ⟨4916311169714570849167781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3277540779809713899445187 4916311169714570849167781)
                  ·
                    refine ⟨921808344321482034218959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916311169714570849167781 921808344321482034218959)
                    ·
                      rfl

theorem cell22_2692823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_2692823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692823 prefixEnd_2692823 := by exact prefixLift 2692823
  have htrace : WordTrace (prefixWord ++ tailWord_2692823) baseStart_2692823 baseEnd_2692823 := by
    simpa [prefixWord, tailWord_2692823, baseEnd_2692823] using wordTrace_append hprefix tailTrace_2692823
  have hstable : (prefixWord ++ tailWord_2692823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692823).length < 2 ^ (prefixWord ++ tailWord_2692823).sum := by decide
  have hdescent : baseEnd_2692823 < baseStart_2692823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_2692864 : Nat := 118140960795 + 2692864 * 2 ^ 59
def prefixEnd_2692864 : Nat := 4983230072969 + 3 ^ 40 * 2692864 * 2
def baseEnd_2692864 : Nat := 921822379459371593943833

theorem tailTrace_2692864 : CollatzResearch.WordTrace tailWord_2692864 prefixEnd_2692864 921822379459371593943833 := by
  unfold tailWord_2692864
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108409458110553700718823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65477879277480738267625097 49108409458110553700718823)
  ·
    refine ⟨73662614187165830551078235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49108409458110553700718823 73662614187165830551078235)
    ·
      refine ⟨110493921280748745826617353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73662614187165830551078235 110493921280748745826617353)
      ·
        refine ⟨82870440960561559369963015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110493921280748745826617353 82870440960561559369963015)
        ·
          refine ⟨124305661440842339054944523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82870440960561559369963015 124305661440842339054944523)
          ·
            refine ⟨186458492161263508582416785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124305661440842339054944523 186458492161263508582416785)
            ·
              refine ⟨139843869120947631436812589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186458492161263508582416785 139843869120947631436812589)
              ·
                refine ⟨52441450920355361788804721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139843869120947631436812589 52441450920355361788804721)
                ·
                  refine ⟨39331088190266521341603541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52441450920355361788804721 39331088190266521341603541)
                  ·
                    refine ⟨921822379459371593943833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39331088190266521341603541 921822379459371593943833)
                    ·
                      rfl

theorem cell22_2692864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_2692864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692864 prefixEnd_2692864 := by exact prefixLift 2692864
  have htrace : WordTrace (prefixWord ++ tailWord_2692864) baseStart_2692864 baseEnd_2692864 := by
    simpa [prefixWord, tailWord_2692864, baseEnd_2692864] using wordTrace_append hprefix tailTrace_2692864
  have hstable : (prefixWord ++ tailWord_2692864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692864).length < 2 ^ (prefixWord ++ tailWord_2692864).sum := by decide
  have hdescent : baseEnd_2692864 < baseStart_2692864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692868 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2692868 : Nat := 118140960795 + 2692868 * 2 ^ 59
def prefixEnd_2692868 : Nat := 4983230072969 + 3 ^ 40 * 2692868 * 2
def baseEnd_2692868 : Nat := 921823748741116916843821

theorem tailTrace_2692868 : CollatzResearch.WordTrace tailWord_2692868 prefixEnd_2692868 921823748741116916843821 := by
  unfold tailWord_2692868
  simp only [CollatzResearch.WordTrace]
  refine ⟨49108482404103308042291629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65477976538804410723055505 49108482404103308042291629)
  ·
    refine ⟨18415680901538740515859361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49108482404103308042291629 18415680901538740515859361)
    ·
      refine ⟨13811760676154055386894521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18415680901538740515859361 13811760676154055386894521)
      ·
        refine ⟨10358820507115541540170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13811760676154055386894521 10358820507115541540170891)
        ·
          refine ⟨15538230760673312310256337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10358820507115541540170891 15538230760673312310256337)
          ·
            refine ⟨11653673070504984232692253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15538230760673312310256337 11653673070504984232692253)
            ·
              refine ⟨4370127401439369087259595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11653673070504984232692253 4370127401439369087259595)
              ·
                refine ⟨6555191102159053630889393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370127401439369087259595 6555191102159053630889393)
                ·
                  refine ⟨4916393326619290223167045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555191102159053630889393 4916393326619290223167045)
                  ·
                    refine ⟨921823748741116916843821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916393326619290223167045 921823748741116916843821)
                    ·
                      rfl

theorem cell22_2692868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2692868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692868 prefixEnd_2692868 := by exact prefixLift 2692868
  have htrace : WordTrace (prefixWord ++ tailWord_2692868) baseStart_2692868 baseEnd_2692868 := by
    simpa [prefixWord, tailWord_2692868, baseEnd_2692868] using wordTrace_append hprefix tailTrace_2692868
  have hstable : (prefixWord ++ tailWord_2692868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692868).length < 2 ^ (prefixWord ++ tailWord_2692868).sum := by decide
  have hdescent : baseEnd_2692868 < baseStart_2692868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692879 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 8]
def baseStart_2692879 : Nat := 118140960795 + 2692879 * 2 ^ 59
def prefixEnd_2692879 : Nat := 4983230072969 + 3 ^ 40 * 2692879 * 2
def baseEnd_2692879 : Nat := 921827514265916554818787

theorem tailTrace_2692879 : CollatzResearch.WordTrace tailWord_2692879 prefixEnd_2692879 921827514265916554818787 := by
  unfold tailWord_2692879
  simp only [CollatzResearch.WordTrace]
  refine ⟨98217366011166764963233691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65478244007444509975489127 98217366011166764963233691)
  ·
    refine ⟨147326049016750147444850537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98217366011166764963233691 147326049016750147444850537)
    ·
      refine ⟨110494536762562610583637903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147326049016750147444850537 110494536762562610583637903)
      ·
        refine ⟨165741805143843915875456855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110494536762562610583637903 165741805143843915875456855)
        ·
          refine ⟨248612707715765873813185283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165741805143843915875456855 248612707715765873813185283)
          ·
            refine ⟨372919061573648810719777925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248612707715765873813185283 372919061573648810719777925)
            ·
              refine ⟨69922324045059152009958361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 372919061573648810719777925 69922324045059152009958361)
              ·
                refine ⟨52441743033794364007468771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69922324045059152009958361 52441743033794364007468771)
                ·
                  refine ⟨78662614550691546011203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52441743033794364007468771 78662614550691546011203157)
                  ·
                    refine ⟨921827514265916554818787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78662614550691546011203157 921827514265916554818787)
                    ·
                      rfl

theorem cell22_2692879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_2692879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692879 prefixEnd_2692879 := by exact prefixLift 2692879
  have htrace : WordTrace (prefixWord ++ tailWord_2692879) baseStart_2692879 baseEnd_2692879 := by
    simpa [prefixWord, tailWord_2692879, baseEnd_2692879] using wordTrace_append hprefix tailTrace_2692879
  have hstable : (prefixWord ++ tailWord_2692879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692879).length < 2 ^ (prefixWord ++ tailWord_2692879).sum := by decide
  have hdescent : baseEnd_2692879 < baseStart_2692879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692881 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2692881 : Nat := 118140960795 + 2692881 * 2 ^ 59
def prefixEnd_2692881 : Nat := 4983230072969 + 3 ^ 40 * 2692881 * 2
def baseEnd_2692881 : Nat := 921828198906789216268781

theorem tailTrace_2692881 : CollatzResearch.WordTrace tailWord_2692881 prefixEnd_2692881 921828198906789216268781 := by
  unfold tailWord_2692881
  simp only [CollatzResearch.WordTrace]
  refine ⟨98217438957159519304806497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65478292638106346203204331 98217438957159519304806497)
  ·
    refine ⟨73663079217869639478604873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98217438957159519304806497 73663079217869639478604873)
    ·
      refine ⟨55247309413402229608953655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73663079217869639478604873 55247309413402229608953655)
      ·
        refine ⟨82870964120103344413430483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55247309413402229608953655 82870964120103344413430483)
        ·
          refine ⟨124306446180155016620145725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82870964120103344413430483 124306446180155016620145725)
          ·
            refine ⟨46614917317558131232554647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124306446180155016620145725 46614917317558131232554647)
            ·
              refine ⟨69922375976337196848831971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46614917317558131232554647 69922375976337196848831971)
              ·
                refine ⟨104883563964505795273247957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69922375976337196848831971 104883563964505795273247957)
                ·
                  refine ⟨2458208530418104576716749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104883563964505795273247957 2458208530418104576716749)
                  ·
                    refine ⟨921828198906789216268781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458208530418104576716749 921828198906789216268781)
                    ·
                      rfl

theorem cell22_2692881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2692881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692881 prefixEnd_2692881 := by exact prefixLift 2692881
  have htrace : WordTrace (prefixWord ++ tailWord_2692881) baseStart_2692881 baseEnd_2692881 := by
    simpa [prefixWord, tailWord_2692881, baseEnd_2692881] using wordTrace_append hprefix tailTrace_2692881
  have hstable : (prefixWord ++ tailWord_2692881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692881).length < 2 ^ (prefixWord ++ tailWord_2692881).sum := by decide
  have hdescent : baseEnd_2692881 < baseStart_2692881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692962 : List Nat := [3, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2692962 : Nat := 118140960795 + 2692962 * 2 ^ 59
def prefixEnd_2692962 : Nat := 4983230072969 + 3 ^ 40 * 2692962 * 2
def baseEnd_2692962 : Nat := 307285308954044001664511

theorem tailTrace_2692962 : CollatzResearch.WordTrace tailWord_2692962 prefixEnd_2692962 307285308954044001664511 := by
  unfold tailWord_2692962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555098317466517534626285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65480262179910713425670093 24555098317466517534626285)
  ·
    refine ⟨9208161869049944075484857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24555098317466517534626285 9208161869049944075484857)
    ·
      refine ⟨6906121401787458056613643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9208161869049944075484857 6906121401787458056613643)
      ·
        refine ⟨10359182102681187084920465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906121401787458056613643 10359182102681187084920465)
        ·
          refine ⟨7769386577010890313690349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10359182102681187084920465 7769386577010890313690349)
          ·
            refine ⟨2913519966379083867633881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7769386577010890313690349 2913519966379083867633881)
            ·
              refine ⟨2185139974784312900725411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913519966379083867633881 2185139974784312900725411)
              ·
                refine ⟨3277709962176469351088117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185139974784312900725411 3277709962176469351088117)
                ·
                  refine ⟨307285308954044001664511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277709962176469351088117 307285308954044001664511)
                  ·
                    rfl

theorem cell22_2692962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2692962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692962 prefixEnd_2692962 := by exact prefixLift 2692962
  have htrace : WordTrace (prefixWord ++ tailWord_2692962) baseStart_2692962 baseEnd_2692962 := by
    simpa [prefixWord, tailWord_2692962, baseEnd_2692962] using wordTrace_append hprefix tailTrace_2692962
  have hstable : (prefixWord ++ tailWord_2692962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692962).length < 2 ^ (prefixWord ++ tailWord_2692962).sum := by decide
  have hdescent : baseEnd_2692962 < baseStart_2692962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692971 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_2692971 : Nat := 118140960795 + 2692971 * 2 ^ 59
def prefixEnd_2692971 : Nat := 4983230072969 + 3 ^ 40 * 2692971 * 2
def baseEnd_2692971 : Nat := 921859007746058981518505

theorem tailTrace_2692971 : CollatzResearch.WordTrace tailWord_2692971 prefixEnd_2692971 921859007746058981518505 := by
  unfold tailWord_2692971
  simp only [CollatzResearch.WordTrace]
  refine ⟨98220721526833464675582767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65480481017888976450388511 98220721526833464675582767)
  ·
    refine ⟨147331082290250197013374151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98220721526833464675582767 147331082290250197013374151)
    ·
      refine ⟨220996623435375295520061227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147331082290250197013374151 220996623435375295520061227)
      ·
        refine ⟨331494935153062943280091841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220996623435375295520061227 331494935153062943280091841)
        ·
          refine ⟨248621201364797207460068881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331494935153062943280091841 248621201364797207460068881)
          ·
            refine ⟨186465901023597905595051661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248621201364797207460068881 186465901023597905595051661)
            ·
              refine ⟨69924712883849214598144373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186465901023597905595051661 69924712883849214598144373)
              ·
                refine ⟨6555441832860863868576035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69924712883849214598144373 6555441832860863868576035)
                ·
                  refine ⟨9833162749291295802864053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6555441832860863868576035 9833162749291295802864053)
                  ·
                    refine ⟨921859007746058981518505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9833162749291295802864053 921859007746058981518505)
                    ·
                      rfl

theorem cell22_2692971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_2692971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692971 prefixEnd_2692971 := by exact prefixLift 2692971
  have htrace : WordTrace (prefixWord ++ tailWord_2692971) baseStart_2692971 baseEnd_2692971 := by
    simpa [prefixWord, tailWord_2692971, baseEnd_2692971] using wordTrace_append hprefix tailTrace_2692971
  have hstable : (prefixWord ++ tailWord_2692971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692971).length < 2 ^ (prefixWord ++ tailWord_2692971).sum := by decide
  have hdescent : baseEnd_2692971 < baseStart_2692971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2692986 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_2692986 : Nat := 118140960795 + 2692986 * 2 ^ 59
def prefixEnd_2692986 : Nat := 4983230072969 + 3 ^ 40 * 2692986 * 2
def baseEnd_2692986 : Nat := 921864142552603942393459

theorem tailTrace_2692986 : CollatzResearch.WordTrace tailWord_2692986 prefixEnd_2692986 921864142552603942393459 := by
  unfold tailWord_2692986
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555317155444780559344703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65480845747852748158252541 24555317155444780559344703)
  ·
    refine ⟨36832975733167170839017055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24555317155444780559344703 36832975733167170839017055)
    ·
      refine ⟨55249463599750756258525583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36832975733167170839017055 55249463599750756258525583)
      ·
        refine ⟨82874195399626134387788375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55249463599750756258525583 82874195399626134387788375)
        ·
          refine ⟨124311293099439201581682563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82874195399626134387788375 124311293099439201581682563)
          ·
            refine ⟨186466939649158802372523845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124311293099439201581682563 186466939649158802372523845)
            ·
              refine ⟨34962551184217275444848221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186466939649158802372523845 34962551184217275444848221)
              ·
                refine ⟨13110956694081478291818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34962551184217275444848221 13110956694081478291818083)
                ·
                  refine ⟨19666435041122217437727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13110956694081478291818083 19666435041122217437727125)
                  ·
                    refine ⟨921864142552603942393459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19666435041122217437727125 921864142552603942393459)
                    ·
                      rfl

theorem cell22_2692986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_2692986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2692986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2692986 prefixEnd_2692986 := by exact prefixLift 2692986
  have htrace : WordTrace (prefixWord ++ tailWord_2692986) baseStart_2692986 baseEnd_2692986 := by
    simpa [prefixWord, tailWord_2692986, baseEnd_2692986] using wordTrace_append hprefix tailTrace_2692986
  have hstable : (prefixWord ++ tailWord_2692986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2692986).length < 2 ^ (prefixWord ++ tailWord_2692986).sum := by decide
  have hdescent : baseEnd_2692986 < baseStart_2692986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2692986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693018 : List Nat := [3, 1, 1, 4, 2, 1, 3, 7]
def baseStart_2693018 : Nat := 118140960795 + 2693018 * 2 ^ 59
def prefixEnd_2693018 : Nat := 4983230072969 + 3 ^ 40 * 2693018 * 2
def baseEnd_2693018 : Nat := 102430566311840725065929

theorem tailTrace_2693018 : CollatzResearch.WordTrace tailWord_2693018 prefixEnd_2693018 102430566311840725065929 := by
  unfold tailWord_2693018
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555608939415797925635927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65481623838442127801695805 24555608939415797925635927)
  ·
    refine ⟨36833413409123696888453891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24555608939415797925635927 36833413409123696888453891)
    ·
      refine ⟨55250120113685545332680837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36833413409123696888453891 55250120113685545332680837)
      ·
        refine ⟨10359397521316039749877657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55250120113685545332680837 10359397521316039749877657)
        ·
          refine ⟨7769548140987029812408243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10359397521316039749877657 7769548140987029812408243)
          ·
            refine ⟨11654322211480544718612365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7769548140987029812408243 11654322211480544718612365)
            ·
              refine ⟨4370370829305204269479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11654322211480544718612365 4370370829305204269479637)
              ·
                refine ⟨102430566311840725065929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4370370829305204269479637 102430566311840725065929)
                ·
                  rfl

theorem cell22_2693018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_2693018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693018 prefixEnd_2693018 := by exact prefixLift 2693018
  have htrace : WordTrace (prefixWord ++ tailWord_2693018) baseStart_2693018 baseEnd_2693018 := by
    simpa [prefixWord, tailWord_2693018, baseEnd_2693018] using wordTrace_append hprefix tailTrace_2693018
  have hstable : (prefixWord ++ tailWord_2693018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693018).length < 2 ^ (prefixWord ++ tailWord_2693018).sum := by decide
  have hdescent : baseEnd_2693018 < baseStart_2693018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693080 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_2693080 : Nat := 118140960795 + 2693080 * 2 ^ 59
def prefixEnd_2693080 : Nat := 4983230072969 + 3 ^ 40 * 2693080 * 2
def baseEnd_2693080 : Nat := 307298773557873010181057

theorem tailTrace_2693080 : CollatzResearch.WordTrace tailWord_2693080 prefixEnd_2693080 307298773557873010181057 := by
  unfold tailWord_2693080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49112348541719288145650347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65483131388959050860867129 49112348541719288145650347)
  ·
    refine ⟨73668522812578932218475521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49112348541719288145650347 73668522812578932218475521)
    ·
      refine ⟨55251392109434199163856641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73668522812578932218475521 55251392109434199163856641)
      ·
        refine ⟨41438544082075649372892481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55251392109434199163856641 41438544082075649372892481)
        ·
          refine ⟨31078908061556737029669361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41438544082075649372892481 31078908061556737029669361)
          ·
            refine ⟨23309181046167552772252021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31078908061556737029669361 23309181046167552772252021)
            ·
              refine ⟨2185235723078208072398627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23309181046167552772252021 2185235723078208072398627)
              ·
                refine ⟨3277853584617312108597941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185235723078208072398627 3277853584617312108597941)
                ·
                  refine ⟨307298773557873010181057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277853584617312108597941 307298773557873010181057)
                  ·
                    rfl

theorem cell22_2693080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_2693080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693080 prefixEnd_2693080 := by exact prefixLift 2693080
  have htrace : WordTrace (prefixWord ++ tailWord_2693080) baseStart_2693080 baseEnd_2693080 := by
    simpa [prefixWord, tailWord_2693080, baseEnd_2693080] using wordTrace_append hprefix tailTrace_2693080
  have hstable : (prefixWord ++ tailWord_2693080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693080).length < 2 ^ (prefixWord ++ tailWord_2693080).sum := by decide
  have hdescent : baseEnd_2693080 < baseStart_2693080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693125 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 6]
def baseStart_2693125 : Nat := 118140960795 + 2693125 * 2 ^ 59
def prefixEnd_2693125 : Nat := 4983230072969 + 3 ^ 40 * 2693125 * 2
def baseEnd_2693125 : Nat := 307303908364417971056011

theorem tailTrace_2693125 : CollatzResearch.WordTrace tailWord_2693125 prefixEnd_2693125 307303908364417971056011 := by
  unfold tailWord_2693125
  simp only [CollatzResearch.WordTrace]
  refine ⟨98226338368275548976688829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65484225578850365984459219 98226338368275548976688829)
  ·
    refine ⟨36834876888103330866258311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98226338368275548976688829 36834876888103330866258311)
    ·
      refine ⟨55252315332154996299387467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36834876888103330866258311 55252315332154996299387467)
      ·
        refine ⟨82878472998232494449081201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55252315332154996299387467 82878472998232494449081201)
        ·
          refine ⟨62158854748674370836810901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82878472998232494449081201 62158854748674370836810901)
          ·
            refine ⟨2913696316344111132975511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62158854748674370836810901 2913696316344111132975511)
            ·
              refine ⟨4370544474516166699463267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913696316344111132975511 4370544474516166699463267)
              ·
                refine ⟨6555816711774250049194901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370544474516166699463267 6555816711774250049194901)
                ·
                  refine ⟨307303908364417971056011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6555816711774250049194901 307303908364417971056011)
                  ·
                    rfl

theorem cell22_2693125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_2693125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693125 prefixEnd_2693125 := by exact prefixLift 2693125
  have htrace : WordTrace (prefixWord ++ tailWord_2693125) baseStart_2693125 baseEnd_2693125 := by
    simpa [prefixWord, tailWord_2693125, baseEnd_2693125] using wordTrace_append hprefix tailTrace_2693125
  have hstable : (prefixWord ++ tailWord_2693125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693125).length < 2 ^ (prefixWord ++ tailWord_2693125).sum := by decide
  have hdescent : baseEnd_2693125 < baseStart_2693125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693155 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 2, 4]
def baseStart_2693155 : Nat := 118140960795 + 2693155 * 2 ^ 59
def prefixEnd_2693155 : Nat := 4983230072969 + 3 ^ 40 * 2693155 * 2
def baseEnd_2693155 : Nat := 921921994706343834917941

theorem tailTrace_2693155 : CollatzResearch.WordTrace tailWord_2693155 prefixEnd_2693155 921921994706343834917941 := by
  unfold tailWord_2693155
  simp only [CollatzResearch.WordTrace]
  refine ⟨98227432558166864100280919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65484955038777909400187279 98227432558166864100280919)
  ·
    refine ⟨147341148837250296150421379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98227432558166864100280919 147341148837250296150421379)
    ·
      refine ⟨221011723255875444225632069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147341148837250296150421379 221011723255875444225632069)
      ·
        refine ⟨41439698110476645792306013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221011723255875444225632069 41439698110476645792306013)
        ·
          refine ⟨15539886791428742172114755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41439698110476645792306013 15539886791428742172114755)
          ·
            refine ⟨23309830187143113258172133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15539886791428742172114755 23309830187143113258172133)
            ·
              refine ⟨4370593160089333735907275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23309830187143113258172133 4370593160089333735907275)
              ·
                refine ⟨6555889740134000603860913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370593160089333735907275 6555889740134000603860913)
                ·
                  refine ⟨4916917305100500452895685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6555889740134000603860913 4916917305100500452895685)
                  ·
                    refine ⟨921921994706343834917941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4916917305100500452895685 921921994706343834917941)
                    ·
                      rfl

theorem cell22_2693155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_2693155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693155 prefixEnd_2693155 := by exact prefixLift 2693155
  have htrace : WordTrace (prefixWord ++ tailWord_2693155) baseStart_2693155 baseEnd_2693155 := by
    simpa [prefixWord, tailWord_2693155, baseEnd_2693155] using wordTrace_append hprefix tailTrace_2693155
  have hstable : (prefixWord ++ tailWord_2693155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693155).length < 2 ^ (prefixWord ++ tailWord_2693155).sum := by decide
  have hdescent : baseEnd_2693155 < baseStart_2693155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693174 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2693174 : Nat := 118140960795 + 2693174 * 2 ^ 59
def prefixEnd_2693174 : Nat := 4983230072969 + 3 ^ 40 * 2693174 * 2
def baseEnd_2693174 : Nat := 921928498794634118692883

theorem tailTrace_2693174 : CollatzResearch.WordTrace tailWord_2693174 prefixEnd_2693174 921928498794634118692883 := by
  unfold tailWord_2693174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139257846568626896576411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65485417030065353563481717 6139257846568626896576411)
  ·
    refine ⟨9208886769852940344864617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6139257846568626896576411 9208886769852940344864617)
    ·
      refine ⟨6906665077389705258648463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9208886769852940344864617 6906665077389705258648463)
      ·
        refine ⟨10359997616084557887972695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6906665077389705258648463 10359997616084557887972695)
        ·
          refine ⟨15539996424126836831959043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10359997616084557887972695 15539996424126836831959043)
          ·
            refine ⟨23309994636190255247938565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15539996424126836831959043 23309994636190255247938565)
            ·
              refine ⟨4370623994285672858988481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23309994636190255247938565 4370623994285672858988481)
              ·
                refine ⟨3277967995714254644241361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370623994285672858988481 3277967995714254644241361)
                ·
                  refine ⟨2458475996785690983181021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3277967995714254644241361 2458475996785690983181021)
                  ·
                    refine ⟨921928498794634118692883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458475996785690983181021 921928498794634118692883)
                    ·
                      rfl

theorem cell22_2693174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2693174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693174 prefixEnd_2693174 := by exact prefixLift 2693174
  have htrace : WordTrace (prefixWord ++ tailWord_2693174) baseStart_2693174 baseEnd_2693174 := by
    simpa [prefixWord, tailWord_2693174, baseEnd_2693174] using wordTrace_append hprefix tailTrace_2693174
  have hstable : (prefixWord ++ tailWord_2693174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693174).length < 2 ^ (prefixWord ++ tailWord_2693174).sum := by decide
  have hdescent : baseEnd_2693174 < baseStart_2693174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693176 : List Nat := [2, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_2693176 : Nat := 118140960795 + 2693176 * 2 ^ 59
def prefixEnd_2693176 : Nat := 4983230072969 + 3 ^ 40 * 2693176 * 2
def baseEnd_2693176 : Nat := 307309727811835593380959

theorem tailTrace_2693176 : CollatzResearch.WordTrace tailWord_2693176 prefixEnd_2693176 307309727811835593380959 := by
  unfold tailWord_2693176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49114099245545392343397691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65485465660727189791196921 49114099245545392343397691)
  ·
    refine ⟨73671148868318088515096537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49114099245545392343397691 73671148868318088515096537)
    ·
      refine ⟨55253361651238566386322403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73671148868318088515096537 55253361651238566386322403)
      ·
        refine ⟨82880042476857849579483605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55253361651238566386322403 82880042476857849579483605)
        ·
          refine ⟨1942500995551355849519147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82880042476857849579483605 1942500995551355849519147)
          ·
            refine ⟨2913751493327033774278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942500995551355849519147 2913751493327033774278721)
            ·
              refine ⟨2185313619995275330709041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913751493327033774278721 2185313619995275330709041)
              ·
                refine ⟨1638985214996456498031781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185313619995275330709041 1638985214996456498031781)
                ·
                  refine ⟨307309727811835593380959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638985214996456498031781 307309727811835593380959)
                  ·
                    rfl

theorem cell22_2693176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_2693176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693176 prefixEnd_2693176 := by exact prefixLift 2693176
  have htrace : WordTrace (prefixWord ++ tailWord_2693176) baseStart_2693176 baseEnd_2693176 := by
    simpa [prefixWord, tailWord_2693176, baseEnd_2693176] using wordTrace_append hprefix tailTrace_2693176
  have hstable : (prefixWord ++ tailWord_2693176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693176).length < 2 ^ (prefixWord ++ tailWord_2693176).sum := by decide
  have hdescent : baseEnd_2693176 < baseStart_2693176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693183 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 6]
def baseStart_2693183 : Nat := 118140960795 + 2693183 * 2 ^ 59
def prefixEnd_2693183 : Nat := 4983230072969 + 3 ^ 40 * 2693183 * 2
def baseEnd_2693183 : Nat := 921931579678561095217855

theorem tailTrace_2693183 : CollatzResearch.WordTrace tailWord_2693183 prefixEnd_2693183 921931579678561095217855 := by
  unfold tailWord_2693183
  simp only [CollatzResearch.WordTrace]
  refine ⟨98228453802065424882300203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65485635868043616588200135 98228453802065424882300203)
  ·
    refine ⟨147342680703098137323450305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98228453802065424882300203 147342680703098137323450305)
    ·
      refine ⟨110507010527323602992587729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147342680703098137323450305 110507010527323602992587729)
      ·
        refine ⟨82880257895492702244440797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110507010527323602992587729 82880257895492702244440797)
        ·
          refine ⟨31080096710809763341665299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82880257895492702244440797 31080096710809763341665299)
          ·
            refine ⟨46620145066214645012497949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31080096710809763341665299 46620145066214645012497949)
            ·
              refine ⟨17482554399830491879686731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46620145066214645012497949 17482554399830491879686731)
              ·
                refine ⟨26223831599745737819530097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17482554399830491879686731 26223831599745737819530097)
                ·
                  refine ⟨19667873699809303364647573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26223831599745737819530097 19667873699809303364647573)
                  ·
                    refine ⟨921931579678561095217855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19667873699809303364647573 921931579678561095217855)
                    ·
                      rfl

theorem cell22_2693183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_2693183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693183 prefixEnd_2693183 := by exact prefixLift 2693183
  have htrace : WordTrace (prefixWord ++ tailWord_2693183) baseStart_2693183 baseEnd_2693183 := by
    simpa [prefixWord, tailWord_2693183, baseEnd_2693183] using wordTrace_append hprefix tailTrace_2693183
  have hstable : (prefixWord ++ tailWord_2693183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693183).length < 2 ^ (prefixWord ++ tailWord_2693183).sum := by decide
  have hdescent : baseEnd_2693183 < baseStart_2693183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693206 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2693206 : Nat := 118140960795 + 2693206 * 2 ^ 59
def prefixEnd_2693206 : Nat := 4983230072969 + 3 ^ 40 * 2693206 * 2
def baseEnd_2693206 : Nat := 921939453048596701892785

theorem tailTrace_2693206 : CollatzResearch.WordTrace tailWord_2693206 prefixEnd_2693206 921939453048596701892785 := by
  unfold tailWord_2693206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139330792561381238149217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65486195120654733206924981 6139330792561381238149217)
  ·
    refine ⟨4604498094421035928611913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6139330792561381238149217 4604498094421035928611913)
    ·
      refine ⟨3453373570815776946458935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4604498094421035928611913 3453373570815776946458935)
      ·
        refine ⟨5180060356223665419688403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453373570815776946458935 5180060356223665419688403)
        ·
          refine ⟨7770090534335498129532605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180060356223665419688403 7770090534335498129532605)
          ·
            refine ⟨2913783950375811798574727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7770090534335498129532605 2913783950375811798574727)
            ·
              refine ⟨4370675925563717697862091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913783950375811798574727 4370675925563717697862091)
              ·
                refine ⟨6556013888345576546793137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370675925563717697862091 6556013888345576546793137)
                ·
                  refine ⟨4917010416259182410094853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6556013888345576546793137 4917010416259182410094853)
                  ·
                    refine ⟨921939453048596701892785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4917010416259182410094853 921939453048596701892785)
                    ·
                      rfl

theorem cell22_2693206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2693206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693206 prefixEnd_2693206 := by exact prefixLift 2693206
  have htrace : WordTrace (prefixWord ++ tailWord_2693206) baseStart_2693206 baseEnd_2693206 := by
    simpa [prefixWord, tailWord_2693206, baseEnd_2693206] using wordTrace_append hprefix tailTrace_2693206
  have hstable : (prefixWord ++ tailWord_2693206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693206).length < 2 ^ (prefixWord ++ tailWord_2693206).sum := by decide
  have hdescent : baseEnd_2693206 < baseStart_2693206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693230 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2693230 : Nat := 118140960795 + 2693230 * 2 ^ 59
def prefixEnd_2693230 : Nat := 4983230072969 + 3 ^ 40 * 2693230 * 2
def baseEnd_2693230 : Nat := 921947668739068639292711

theorem tailTrace_2693230 : CollatzResearch.WordTrace tailWord_2693230 prefixEnd_2693230 921947668739068639292711 := by
  unfold tailWord_2693230
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278771004111893988657643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65486778688596767939507429 12278771004111893988657643)
  ·
    refine ⟨18418156506167840982986465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12278771004111893988657643 18418156506167840982986465)
    ·
      refine ⟨13813617379625880737239849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18418156506167840982986465 13813617379625880737239849)
      ·
        refine ⟨10360213034719410552929887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813617379625880737239849 10360213034719410552929887)
        ·
          refine ⟨15540319552079115829394831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360213034719410552929887 15540319552079115829394831)
          ·
            refine ⟨23310479328118673744092247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15540319552079115829394831 23310479328118673744092247)
            ·
              refine ⟨34965718992178010616138371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23310479328118673744092247 34965718992178010616138371)
              ·
                refine ⟨52448578488267015924207557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34965718992178010616138371 52448578488267015924207557)
                ·
                  refine ⟨9834108466550065485788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52448578488267015924207557 9834108466550065485788917)
                  ·
                    refine ⟨921947668739068639292711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9834108466550065485788917 921947668739068639292711)
                    ·
                      rfl

theorem cell22_2693230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2693230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693230 prefixEnd_2693230 := by exact prefixLift 2693230
  have htrace : WordTrace (prefixWord ++ tailWord_2693230) baseStart_2693230 baseEnd_2693230 := by
    simpa [prefixWord, tailWord_2693230, baseEnd_2693230] using wordTrace_append hprefix tailTrace_2693230
  have hstable : (prefixWord ++ tailWord_2693230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693230).length < 2 ^ (prefixWord ++ tailWord_2693230).sum := by decide
  have hdescent : baseEnd_2693230 < baseStart_2693230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693232 : List Nat := [2, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_2693232 : Nat := 118140960795 + 2693232 * 2 ^ 59
def prefixEnd_2693232 : Nat := 4983230072969 + 3 ^ 40 * 2693232 * 2
def baseEnd_2693232 : Nat := 307316117793313766914235

theorem tailTrace_2693232 : CollatzResearch.WordTrace tailWord_2693232 prefixEnd_2693232 307316117793313766914235 := by
  unfold tailWord_2693232
  simp only [CollatzResearch.WordTrace]
  refine ⟨49115120489443953125416975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65486827319258604167222633 49115120489443953125416975)
  ·
    refine ⟨73672680734165929688125463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49115120489443953125416975 73672680734165929688125463)
    ·
      refine ⟨110509021101248894532188195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73672680734165929688125463 110509021101248894532188195)
      ·
        refine ⟨165763531651873341798282293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110509021101248894532188195 165763531651873341798282293)
        ·
          refine ⟨15540331092363125793588965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165763531651873341798282293 15540331092363125793588965)
          ·
            refine ⟨2913812079818086086297931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15540331092363125793588965 2913812079818086086297931)
            ·
              refine ⟨4370718119727129129446897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913812079818086086297931 4370718119727129129446897)
              ·
                refine ⟨3278038589795346847085173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370718119727129129446897 3278038589795346847085173)
                ·
                  refine ⟨307316117793313766914235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278038589795346847085173 307316117793313766914235)
                  ·
                    rfl

theorem cell22_2693232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_2693232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693232 prefixEnd_2693232 := by exact prefixLift 2693232
  have htrace : WordTrace (prefixWord ++ tailWord_2693232) baseStart_2693232 baseEnd_2693232 := by
    simpa [prefixWord, tailWord_2693232, baseEnd_2693232] using wordTrace_append hprefix tailTrace_2693232
  have hstable : (prefixWord ++ tailWord_2693232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693232).length < 2 ^ (prefixWord ++ tailWord_2693232).sum := by decide
  have hdescent : baseEnd_2693232 < baseStart_2693232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693249 : List Nat := [1, 2, 4, 2, 3, 1, 3, 1, 5]
def baseStart_2693249 : Nat := 118140960795 + 2693249 * 2 ^ 59
def prefixEnd_2693249 : Nat := 4983230072969 + 3 ^ 40 * 2693249 * 2
def baseEnd_2693249 : Nat := 307318057609119641022551

theorem tailTrace_2693249 : CollatzResearch.WordTrace tailWord_2693249 prefixEnd_2693249 307318057609119641022551 := by
  unfold tailWord_2693249
  simp only [CollatzResearch.WordTrace]
  refine ⟨98230861019826318154202801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65487240679884212102801867 98230861019826318154202801)
  ·
    refine ⟨73673145764869738615652101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98230861019826318154202801 73673145764869738615652101)
    ·
      refine ⟨13813714830913075990434769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73673145764869738615652101 13813714830913075990434769)
      ·
        refine ⟨10360286123184806992826077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813714830913075990434769 10360286123184806992826077)
        ·
          refine ⟨3885107296194302622309779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10360286123184806992826077 3885107296194302622309779)
          ·
            refine ⟨5827660944291453933464669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885107296194302622309779 5827660944291453933464669)
            ·
              refine ⟨2185372854109295225049251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5827660944291453933464669 2185372854109295225049251)
              ·
                refine ⟨3278059281163942837573877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185372854109295225049251 3278059281163942837573877)
                ·
                  refine ⟨307318057609119641022551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278059281163942837573877 307318057609119641022551)
                  ·
                    rfl

theorem cell22_2693249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_2693249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693249 prefixEnd_2693249 := by exact prefixLift 2693249
  have htrace : WordTrace (prefixWord ++ tailWord_2693249) baseStart_2693249 baseEnd_2693249 := by
    simpa [prefixWord, tailWord_2693249, baseEnd_2693249] using wordTrace_append hprefix tailTrace_2693249
  have hstable : (prefixWord ++ tailWord_2693249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693249).length < 2 ^ (prefixWord ++ tailWord_2693249).sum := by decide
  have hdescent : baseEnd_2693249 < baseStart_2693249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693275 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 6, 3]
def baseStart_2693275 : Nat := 118140960795 + 2693275 * 2 ^ 59
def prefixEnd_2693275 : Nat := 4983230072969 + 3 ^ 40 * 2693275 * 2
def baseEnd_2693275 : Nat := 921963073158703521917573

theorem tailTrace_2693275 : CollatzResearch.WordTrace tailWord_2693275 prefixEnd_2693275 921963073158703521917573 := by
  unfold tailWord_2693275
  simp only [CollatzResearch.WordTrace]
  refine ⟨98231809317732124594649279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65487872878488083063099519 98231809317732124594649279)
  ·
    refine ⟨147347713976598186891973919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98231809317732124594649279 147347713976598186891973919)
    ·
      refine ⟨221021570964897280337960879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147347713976598186891973919 221021570964897280337960879)
      ·
        refine ⟨331532356447345920506941319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221021570964897280337960879 331532356447345920506941319)
        ·
          refine ⟨497298534671018880760411979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331532356447345920506941319 497298534671018880760411979)
          ·
            refine ⟨745947802006528321140617969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497298534671018880760411979 745947802006528321140617969)
            ·
              refine ⟨559460851504896240855463477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745947802006528321140617969 559460851504896240855463477)
              ·
                refine ⟨52449454828584022580199701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 559460851504896240855463477 52449454828584022580199701)
                ·
                  refine ⟨2458568195089876058446861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52449454828584022580199701 2458568195089876058446861)
                  ·
                    refine ⟨921963073158703521917573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2458568195089876058446861 921963073158703521917573)
                    ·
                      rfl

theorem cell22_2693275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 3].length) (baseStart_2693275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693275 prefixEnd_2693275 := by exact prefixLift 2693275
  have htrace : WordTrace (prefixWord ++ tailWord_2693275) baseStart_2693275 baseEnd_2693275 := by
    simpa [prefixWord, tailWord_2693275, baseEnd_2693275] using wordTrace_append hprefix tailTrace_2693275
  have hstable : (prefixWord ++ tailWord_2693275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693275).length < 2 ^ (prefixWord ++ tailWord_2693275).sum := by decide
  have hdescent : baseEnd_2693275 < baseStart_2693275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693300 : List Nat := [2, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2693300 : Nat := 118140960795 + 2693300 * 2 ^ 59
def prefixEnd_2693300 : Nat := 4983230072969 + 3 ^ 40 * 2693300 * 2
def baseEnd_2693300 : Nat := 307323877056537263347499

theorem tailTrace_2693300 : CollatzResearch.WordTrace tailWord_2693300 prefixEnd_2693300 307323877056537263347499 := by
  unfold tailWord_2693300
  simp only [CollatzResearch.WordTrace]
  refine ⟨49116360571320776932154677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65488480761761035909539569 49116360571320776932154677)
  ·
    refine ⟨4604658803561322837389501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49116360571320776932154677 4604658803561322837389501)
    ·
      refine ⟨1726747051335496064021063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4604658803561322837389501 1726747051335496064021063)
      ·
        refine ⟨2590120577003244096031595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726747051335496064021063 2590120577003244096031595)
        ·
          refine ⟨3885180865504866144047393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590120577003244096031595 3885180865504866144047393)
          ·
            refine ⟨2913885649128649608035545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3885180865504866144047393 2913885649128649608035545)
            ·
              refine ⟨2185414236846487206026659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913885649128649608035545 2185414236846487206026659)
              ·
                refine ⟨3278121355269730809039989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185414236846487206026659 3278121355269730809039989)
                ·
                  refine ⟨307323877056537263347499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278121355269730809039989 307323877056537263347499)
                  ·
                    rfl

theorem cell22_2693300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2693300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693300 prefixEnd_2693300 := by exact prefixLift 2693300
  have htrace : WordTrace (prefixWord ++ tailWord_2693300) baseStart_2693300 baseEnd_2693300 := by
    simpa [prefixWord, tailWord_2693300, baseEnd_2693300] using wordTrace_append hprefix tailTrace_2693300
  have hstable : (prefixWord ++ tailWord_2693300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693300).length < 2 ^ (prefixWord ++ tailWord_2693300).sum := by decide
  have hdescent : baseEnd_2693300 < baseStart_2693300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693305 : List Nat := [1, 2, 1, 4, 1, 2, 4, 7]
def baseStart_2693305 : Nat := 118140960795 + 2693305 * 2 ^ 59
def prefixEnd_2693305 : Nat := 4983230072969 + 3 ^ 40 * 2693305 * 2
def baseEnd_2693305 : Nat := 102441482530199271518609

theorem tailTrace_2693305 : CollatzResearch.WordTrace tailWord_2693305 prefixEnd_2693305 102441482530199271518609 := by
  unfold tailWord_2693305
  simp only [CollatzResearch.WordTrace]
  refine ⟨98232903507623439718241369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65488602338415626478827579 98232903507623439718241369)
  ·
    refine ⟨73674677630717579788681027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98232903507623439718241369 73674677630717579788681027)
    ·
      refine ⟨110512016446076369683021541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73674677630717579788681027 110512016446076369683021541)
      ·
        refine ⟨20721003083639319315566539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110512016446076369683021541 20721003083639319315566539)
        ·
          refine ⟨31081504625458978973349809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20721003083639319315566539 31081504625458978973349809)
          ·
            refine ⟨23311128469094234230012357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31081504625458978973349809 23311128469094234230012357)
            ·
              refine ⟨4370836587955168918127317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23311128469094234230012357 4370836587955168918127317)
              ·
                refine ⟨102441482530199271518609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4370836587955168918127317 102441482530199271518609)
                ·
                  rfl

theorem cell22_2693305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 7].length) (baseStart_2693305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693305 prefixEnd_2693305 := by exact prefixLift 2693305
  have htrace : WordTrace (prefixWord ++ tailWord_2693305) baseStart_2693305 baseEnd_2693305 := by
    simpa [prefixWord, tailWord_2693305, baseEnd_2693305] using wordTrace_append hprefix tailTrace_2693305
  have hstable : (prefixWord ++ tailWord_2693305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693305).length < 2 ^ (prefixWord ++ tailWord_2693305).sum := by decide
  have hdescent : baseEnd_2693305 < baseStart_2693305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693313 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2693313 : Nat := 118140960795 + 2693313 * 2 ^ 59
def prefixEnd_2693313 : Nat := 4983230072969 + 3 ^ 40 * 2693313 * 2
def baseEnd_2693313 : Nat := 921976081335284089467457

theorem tailTrace_2693313 : CollatzResearch.WordTrace tailWord_2693313 prefixEnd_2693313 921976081335284089467457 := by
  unfold tailWord_2693313
  simp only [CollatzResearch.WordTrace]
  refine ⟨98233195291594457084532593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65488796861062971389688395 98233195291594457084532593)
  ·
    refine ⟨73674896468695842813399445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98233195291594457084532593 73674896468695842813399445)
    ·
      refine ⟨3453510771970117631878099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73674896468695842813399445 3453510771970117631878099)
      ·
        refine ⟨5180266157955176447817149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453510771970117631878099 5180266157955176447817149)
        ·
          refine ⟨1942599809233191167931431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5180266157955176447817149 1942599809233191167931431)
          ·
            refine ⟨2913899713849786751897147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942599809233191167931431 2913899713849786751897147)
            ·
              refine ⟨4370849570774680127845721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2913899713849786751897147 4370849570774680127845721)
              ·
                refine ⟨3278137178081010095884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4370849570774680127845721 3278137178081010095884291)
                ·
                  refine ⟨4917205767121515143826437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3278137178081010095884291 4917205767121515143826437)
                  ·
                    refine ⟨921976081335284089467457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4917205767121515143826437 921976081335284089467457)
                    ·
                      rfl

theorem cell22_2693313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2693313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693313 prefixEnd_2693313 := by exact prefixLift 2693313
  have htrace : WordTrace (prefixWord ++ tailWord_2693313) baseStart_2693313 baseEnd_2693313 := by
    simpa [prefixWord, tailWord_2693313, baseEnd_2693313] using wordTrace_append hprefix tailTrace_2693313
  have hstable : (prefixWord ++ tailWord_2693313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693313).length < 2 ^ (prefixWord ++ tailWord_2693313).sum := by decide
  have hdescent : baseEnd_2693313 < baseStart_2693313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2693412 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_2693412 : Nat := 118140960795 + 2693412 * 2 ^ 59
def prefixEnd_2693412 : Nat := 4983230072969 + 3 ^ 40 * 2693412 * 2
def baseEnd_2693412 : Nat := 307336657019493610414051

theorem tailTrace_2693412 : CollatzResearch.WordTrace tailWord_2693412 prefixEnd_2693412 307336657019493610414051 := by
  unfold tailWord_2693412
  simp only [CollatzResearch.WordTrace]
  refine ⟨49118403059117898496193245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65491204078823864661590993 49118403059117898496193245)
  ·
    refine ⟨18419401147169211936072467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49118403059117898496193245 18419401147169211936072467)
    ·
      refine ⟨27629101720753817904108701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18419401147169211936072467 27629101720753817904108701)
      ·
        refine ⟨10360913145282681714040763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27629101720753817904108701 10360913145282681714040763)
        ·
          refine ⟨15541369717924022571061145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10360913145282681714040763 15541369717924022571061145)
          ·
            refine ⟨11656027288443016928295859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15541369717924022571061145 11656027288443016928295859)
            ·
              refine ⟨17484040932664525392443789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11656027288443016928295859 17484040932664525392443789)
              ·
                refine ⟨6556515349749197022166421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17484040932664525392443789 6556515349749197022166421)
                ·
                  refine ⟨307336657019493610414051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6556515349749197022166421 307336657019493610414051)
                  ·
                    rfl

theorem cell22_2693412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_2693412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2693412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2693412 prefixEnd_2693412 := by exact prefixLift 2693412
  have htrace : WordTrace (prefixWord ++ tailWord_2693412) baseStart_2693412 baseEnd_2693412 := by
    simpa [prefixWord, tailWord_2693412, baseEnd_2693412] using wordTrace_append hprefix tailTrace_2693412
  have hstable : (prefixWord ++ tailWord_2693412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2693412).length < 2 ^ (prefixWord ++ tailWord_2693412).sum := by decide
  have hdescent : baseEnd_2693412 < baseStart_2693412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2693412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
